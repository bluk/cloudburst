// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! KRPC messages are the protocol messages exchanged.

use bt_bencode::Value;
use core::{convert::TryFrom, fmt};
use serde_bytes::{ByteBuf, Bytes};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::collections::BTreeMap;

#[cfg(feature = "std")]
use crate::dht::node::AddrId;
#[cfg(feature = "std")]
use std::{
    collections::BTreeMap,
    net::{Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6},
};

use crate::dht::node::Id;

/// Error for KRPC protocol.
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl Error {
    pub(crate) const fn is_deserialize_error() -> Self {
        Self {
            kind: ErrorKind::CannotDeserializeKrpcMessage,
        }
    }
}

impl From<bt_bencode::Error> for Error {
    fn from(e: bt_bencode::Error) -> Self {
        match e {
            bt_bencode::Error::Serialize(_) => Self {
                kind: ErrorKind::CannotSerializeKrpcMessage,
            },
            _ => Self {
                kind: ErrorKind::CannotDeserializeKrpcMessage,
            },
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ErrorKind::CannotDeserializeKrpcMessage => {
                f.write_str("cannot deserialize KRPC message")
            }
            ErrorKind::CannotSerializeKrpcMessage => f.write_str("cannot serialize KRPC message"),
        }
    }
}

#[derive(Debug)]
enum ErrorKind {
    CannotDeserializeKrpcMessage,
    CannotSerializeKrpcMessage,
}

/// Type of KRPC message.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Ty<'a> {
    /// Query message.
    Query,
    /// Response message.
    Response,
    /// Error message.
    Error,
    /// Unknown message type.
    Unknown(&'a str),
}

impl<'a> Ty<'a> {
    /// Returns the value used in a message to identify the message type.
    #[must_use]
    pub fn val(&self) -> &'a str {
        match self {
            Ty::Query => "q",
            Ty::Response => "r",
            Ty::Error => "e",
            Ty::Unknown(v) => v,
        }
    }
}

/// A KRPC message.
pub trait Msg {
    /// The transaction id for the message.
    fn tx_id(&self) -> Option<&[u8]>;

    /// The type of message.
    fn ty(&self) -> Option<Ty<'_>>;

    /// The client version as a byte buffer.
    fn client_version(&self) -> Option<&[u8]>;

    /// The client version as a string.
    fn client_version_str(&self) -> Option<&str> {
        self.client_version()
            .and_then(|v| core::str::from_utf8(v).ok())
    }
}

impl Msg for Value {
    fn tx_id(&self) -> Option<&[u8]> {
        self.get("t")
            .and_then(bt_bencode::Value::as_byte_str)
            .map(|t| t.as_slice())
    }

    fn ty(&self) -> Option<Ty<'_>> {
        self.get("y")
            .and_then(bt_bencode::Value::as_str)
            .map(|y| match y {
                "q" => Ty::Query,
                "r" => Ty::Response,
                "e" => Ty::Error,
                y => Ty::Unknown(y),
            })
    }

    fn client_version(&self) -> Option<&[u8]> {
        self.get("v")
            .and_then(bt_bencode::Value::as_byte_str)
            .map(|v| v.as_slice())
    }
}

/// A KPRC query message.
pub trait QueryMsg: Msg {
    /// The method name of the query.
    fn method_name(&self) -> Option<&[u8]>;

    /// The method name of the query as a string.
    fn method_name_str(&self) -> Option<&str> {
        self.method_name()
            .and_then(|v| core::str::from_utf8(v).ok())
    }

    /// The arguments for the query.
    fn args(&self) -> Option<&BTreeMap<ByteBuf, Value>>;

    /// The querying node ID.
    fn querying_node_id(&self) -> Option<Id> {
        self.args()
            .and_then(|a| a.get(Bytes::new(b"id")))
            .and_then(bt_bencode::Value::as_byte_str)
            .and_then(|id| Id::try_from(id.as_slice()).ok())
    }
}

impl QueryMsg for Value {
    fn method_name(&self) -> Option<&[u8]> {
        self.get("q")
            .and_then(bt_bencode::Value::as_byte_str)
            .map(|v| v.as_slice())
    }

    fn args(&self) -> Option<&BTreeMap<ByteBuf, Value>> {
        self.get("a").and_then(bt_bencode::Value::as_dict)
    }
}

/// KRPC query arguments.
pub trait QueryArgs {
    /// The query method name.
    fn method_name() -> &'static [u8];

    /// The querying node ID.
    fn id(&self) -> Id;

    /// Represents the arguments as a Bencoded Value.
    fn to_value(&self) -> Value;
}

/// A KPRC response message.
pub trait RespMsg: Msg {
    /// The response values.
    fn values(&self) -> Option<&BTreeMap<ByteBuf, Value>>;

    /// The queried node id.
    fn queried_node_id(&self) -> Option<Id>;
}

impl RespMsg for Value {
    fn values(&self) -> Option<&BTreeMap<ByteBuf, Value>> {
        self.get("r").and_then(bt_bencode::Value::as_dict)
    }

    fn queried_node_id(&self) -> Option<Id> {
        self.get("r")
            .and_then(|a| a.get("id"))
            .and_then(bt_bencode::Value::as_byte_str)
            .and_then(|id| Id::try_from(id.as_slice()).ok())
    }
}

/// KRPC response values.
pub trait RespVal {
    /// The queried node ID.
    fn id(&self) -> Id;

    /// Represents the values as a Bencoded value.
    fn to_value(&self) -> Value;
}

/// A KRPC error message.
pub trait ErrorMsg: Msg {
    /// The error value.
    fn error(&self) -> Option<&[Value]>;
}

impl ErrorMsg for Value {
    fn error(&self) -> Option<&[Value]> {
        self.get("e")
            .and_then(bt_bencode::Value::as_array)
            .map(core::convert::AsRef::as_ref)
    }
}

/// Standard error codes in KRPC error messages.
#[derive(Clone, Copy, Debug, PartialEq)]
#[non_exhaustive]
pub enum ErrorCode {
    /// Generic error.
    GenericError,
    /// Server error.
    ServerError,
    /// Protocol error.
    ProtocolError,
    /// Method unknown error.
    MethodUnknown,
    /// A non-standard error.
    Other(i32),
}

impl ErrorCode {
    /// The code used in a message to identify the message.
    #[must_use]
    pub fn code(self) -> i32 {
        match self {
            ErrorCode::GenericError => 201,
            ErrorCode::ServerError => 202,
            ErrorCode::ProtocolError => 203,
            ErrorCode::MethodUnknown => 204,
            ErrorCode::Other(n) => n,
        }
    }
}

/// The error value.
pub trait ErrorVal {
    /// The error code.
    fn code(&self) -> ErrorCode;

    /// The error description.
    fn description(&self) -> &str;

    /// Represents the arguments as a Bencoded Value.
    fn to_value(&self) -> Value;
}

/// An IPv4 socket address representable by a compact format.
///
/// The trait is intended to help convert an IPv4 socket address to the compact form used in KRPC messages.
///
/// This trait is sealed and cannot be implemented for types outside this crate.
pub trait CompactAddrV4Info: sealed::Private {
    /// Returns the address encoded as a compact address.
    fn to_compact_addr(&self) -> [u8; 6];

    /// Converts from the compact address to the self type.
    fn from_compact_addr(bytes: [u8; 6]) -> Self;
}

#[cfg(feature = "std")]
impl CompactAddrV4Info for SocketAddrV4 {
    fn to_compact_addr(&self) -> [u8; 6] {
        let mut a: [u8; 6] = [0; 6];
        a[0..4].copy_from_slice(&self.ip().octets());
        a[4..6].copy_from_slice(&self.port().to_be_bytes());
        a
    }

    fn from_compact_addr(bytes: [u8; 6]) -> Self {
        let mut ip: [u8; 4] = [0; 4];
        ip[0..4].copy_from_slice(&bytes[0..4]);
        let ip = Ipv4Addr::from(ip);

        let mut port: [u8; 2] = [0; 2];
        port[0..2].copy_from_slice(&bytes[4..6]);
        let port = u16::from_be_bytes(port);

        SocketAddrV4::new(ip, port)
    }
}

/// An IPv6 socket address representable by a compact format.
///
/// The trait is intended to help convert an IPv6 socket address to the compact form used in KRPC messages.
///
/// This trait is sealed and cannot be implemented for types outside this crate.
pub trait CompactAddrV6Info: sealed::Private {
    /// Returns the address encoded as a compact address.
    fn to_compact_addr(&self) -> [u8; 18];

    /// Converts from the compact address to the self type.
    fn from_compact_addr(bytes: [u8; 18]) -> Self;
}

#[cfg(feature = "std")]
impl CompactAddrV6Info for SocketAddrV6 {
    fn to_compact_addr(&self) -> [u8; 18] {
        let mut a: [u8; 18] = [0; 18];
        a[0..16].copy_from_slice(&self.ip().octets());
        a[16..18].copy_from_slice(&self.port().to_be_bytes());
        a
    }

    fn from_compact_addr(bytes: [u8; 18]) -> Self {
        let mut ip: [u8; 16] = [0; 16];
        ip[0..16].copy_from_slice(&bytes[0..16]);
        let ip = Ipv6Addr::from(ip);

        let mut port: [u8; 2] = [0; 2];
        port[0..2].copy_from_slice(&bytes[16..18]);
        let port = u16::from_be_bytes(port);

        SocketAddrV6::new(ip, port, 0, 0)
    }
}

#[cfg(feature = "std")]
fn decode_addr_ipv4_list<B>(nodes: B) -> Result<Vec<AddrId<SocketAddrV4>>, Error>
where
    B: AsRef<[u8]>,
{
    let nodes = nodes.as_ref();

    if nodes.len() % 26 != 0 {
        return Err(Error::is_deserialize_error());
    }

    let addr_len = nodes.len() / 26;
    Ok((0..addr_len)
        .map(|i| {
            let offset = i * 26;

            let mut id: [u8; 20] = [0; 20];
            id.copy_from_slice(&nodes[offset..offset + 20]);
            let id = Id::from(id);

            let mut compact_addr: [u8; 6] = [0; 6];
            compact_addr.copy_from_slice(&nodes[offset + 20..offset + 26]);
            AddrId::new(SocketAddrV4::from_compact_addr(compact_addr), id)
        })
        .collect::<Vec<_>>())
}

#[cfg(feature = "std")]
fn decode_addr_ipv6_list<B>(nodes6: B) -> Result<Vec<AddrId<SocketAddrV6>>, Error>
where
    B: AsRef<[u8]>,
{
    let nodes6 = nodes6.as_ref();

    if nodes6.len() % 38 != 0 {
        return Err(Error::is_deserialize_error());
    }

    let addr_len = nodes6.len() / 38;
    Ok((0..addr_len)
        .map(|i| {
            let offset = i * 38;

            let mut id: [u8; 20] = [0; 20];
            id.copy_from_slice(&nodes6[offset..offset + 20]);
            let id = Id::from(id);

            let mut compact_addr: [u8; 18] = [0; 18];
            compact_addr.copy_from_slice(&nodes6[offset + 20..offset + 38]);
            let addr = SocketAddrV6::from_compact_addr(compact_addr);

            AddrId::new(addr, id)
        })
        .collect::<Vec<_>>())
}

mod sealed {
    #[cfg(feature = "std")]
    use std::net::{SocketAddrV4, SocketAddrV6};

    pub trait Private {}

    #[cfg(feature = "std")]
    impl Private for SocketAddrV6 {}
    #[cfg(feature = "std")]
    impl Private for SocketAddrV4 {}
}

pub mod error;
pub mod find_node;
pub mod ping;
pub mod ser;
