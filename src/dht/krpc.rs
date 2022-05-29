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
use alloc::{collections::BTreeMap, vec::Vec};

#[cfg(feature = "std")]
use std::{
    collections::BTreeMap,
    net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
    vec::Vec,
};

use crate::dht::node::{AddrId, Id};

/// Error for KRPC protocol.
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl Error {
    #[must_use]
    #[inline]
    pub(crate) const fn is_deserialize_error() -> Self {
        Self {
            kind: ErrorKind::CannotDeserializeKrpcMessage,
        }
    }

    #[allow(dead_code)]
    #[must_use]
    #[inline]
    pub(crate) const fn is_invalid_compact_addr() -> Self {
        Self {
            kind: ErrorKind::InvalidCompactAddr,
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
            ErrorKind::InvalidCompactAddr => f.write_str("invalid compact address"),
        }
    }
}

#[derive(Debug)]
enum ErrorKind {
    CannotDeserializeKrpcMessage,
    CannotSerializeKrpcMessage,
    #[allow(dead_code)]
    InvalidCompactAddr,
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
    #[inline]
    pub const fn val(&self) -> &'a str {
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
    #[inline]
    pub const fn code(self) -> i32 {
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CompactAddrV4(pub [u8; 6]);

impl CompactAddrV4 {
    /// Instantiates with the given bytes.
    #[must_use]
    #[inline]
    pub const fn with_bytes(value: [u8; 6]) -> Self {
        Self(value)
    }

    /// Instantiates with the given socket address.
    #[cfg(feature = "std")]
    #[must_use]
    #[inline]
    pub fn with_socket_addr(value: SocketAddrV4) -> Self {
        let mut a: [u8; 6] = [0; 6];
        a[0..4].copy_from_slice(value.ip().octets().as_ref());
        a[4..6].copy_from_slice(value.port().to_be_bytes().as_ref());
        Self(a)
    }
}

impl core::fmt::Display for CompactAddrV4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let port = <[u8; 2]>::try_from(&self.0[4..6]).unwrap();
        let port = u16::from_be_bytes(port);
        write!(
            f,
            "{}.{}.{}.{}:{}",
            self.0[0], self.0[1], self.0[2], self.0[3], port
        )
    }
}

impl AsRef<[u8]> for CompactAddrV4 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 6]> for CompactAddrV4 {
    fn from(value: [u8; 6]) -> Self {
        Self(value)
    }
}

impl From<CompactAddrV4> for [u8; 6] {
    fn from(value: CompactAddrV4) -> Self {
        value.0
    }
}

#[cfg(feature = "std")]
impl From<SocketAddrV4> for CompactAddrV4 {
    fn from(value: SocketAddrV4) -> Self {
        let mut a: [u8; 6] = [0; 6];
        a[0..4].copy_from_slice(&value.ip().octets());
        a[4..6].copy_from_slice(&value.port().to_be_bytes());
        Self(a)
    }
}

#[cfg(feature = "std")]
impl From<CompactAddrV4> for SocketAddrV4 {
    fn from(value: CompactAddrV4) -> Self {
        let mut ip: [u8; 4] = [0; 4];
        ip[0..4].copy_from_slice(&value.0[0..4]);
        let ip = Ipv4Addr::from(ip);

        let mut port: [u8; 2] = [0; 2];
        port[0..2].copy_from_slice(&value.0[4..6]);
        let port = u16::from_be_bytes(port);

        SocketAddrV4::new(ip, port)
    }
}

#[cfg(feature = "std")]
impl From<CompactAddrV4> for SocketAddr {
    fn from(value: CompactAddrV4) -> Self {
        SocketAddr::V4(SocketAddrV4::from(value))
    }
}

/// An IPv6 socket address representable by a compact format.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CompactAddrV6(pub [u8; 18]);

impl CompactAddrV6 {
    /// Instantiates with the given bytes.
    #[must_use]
    #[inline]
    pub const fn with_bytes(value: [u8; 18]) -> Self {
        Self(value)
    }

    /// Instantiates with the given socket address.
    #[cfg(feature = "std")]
    #[must_use]
    #[inline]
    pub fn with_socket_addr(value: SocketAddrV6) -> Self {
        let mut a: [u8; 18] = [0; 18];
        a[0..16].copy_from_slice(value.ip().octets().as_ref());
        a[16..18].copy_from_slice(value.port().to_be_bytes().as_ref());
        Self(a)
    }
}

impl core::fmt::Display for CompactAddrV6 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut index = 0;
        loop {
            write!(f, "{:02x?}{:02x?}", self.0[index], self.0[index + 1])?;

            if index == 14 {
                break;
            }

            index += 2;
            write!(f, ":")?;
        }

        let port = <[u8; 2]>::try_from(&self.0[16..18]).unwrap();
        let port = u16::from_be_bytes(port);

        write!(f, "]:{}", port)
    }
}

impl AsRef<[u8]> for CompactAddrV6 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 18]> for CompactAddrV6 {
    fn from(value: [u8; 18]) -> Self {
        Self(value)
    }
}

impl From<CompactAddrV6> for [u8; 18] {
    fn from(value: CompactAddrV6) -> Self {
        value.0
    }
}

#[cfg(feature = "std")]
impl From<SocketAddrV6> for CompactAddrV6 {
    fn from(value: SocketAddrV6) -> Self {
        let mut a: [u8; 18] = [0; 18];
        a[0..16].copy_from_slice(&value.ip().octets());
        a[16..18].copy_from_slice(&value.port().to_be_bytes());
        Self(a)
    }
}

#[cfg(feature = "std")]
impl From<CompactAddrV6> for SocketAddrV6 {
    fn from(value: CompactAddrV6) -> Self {
        let mut ip: [u8; 16] = [0; 16];
        ip[0..16].copy_from_slice(&value.0[0..16]);
        let ip = Ipv6Addr::from(ip);

        let mut port: [u8; 2] = [0; 2];
        port[0..2].copy_from_slice(&value.0[16..18]);
        let port = u16::from_be_bytes(port);

        SocketAddrV6::new(ip, port, 0, 0)
    }
}

#[cfg(feature = "std")]
impl From<CompactAddrV6> for SocketAddr {
    fn from(value: CompactAddrV6) -> Self {
        SocketAddr::V6(SocketAddrV6::from(value))
    }
}

/// Compact byte form of a socket address.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompactAddr {
    /// An IPv4 address with a port.
    V4(CompactAddrV4),
    /// An IPv6 address with a port.
    V6(CompactAddrV6),
}

impl core::fmt::Display for CompactAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompactAddr::V4(addr) => write!(f, "{addr}"),
            CompactAddr::V6(addr) => write!(f, "{addr}"),
        }
    }
}

impl AsRef<[u8]> for CompactAddr {
    fn as_ref(&self) -> &[u8] {
        match self {
            CompactAddr::V4(value) => value.as_ref(),
            CompactAddr::V6(value) => value.as_ref(),
        }
    }
}

impl From<CompactAddrV4> for CompactAddr {
    fn from(value: CompactAddrV4) -> Self {
        CompactAddr::V4(value)
    }
}

impl From<CompactAddrV6> for CompactAddr {
    fn from(value: CompactAddrV6) -> Self {
        CompactAddr::V6(value)
    }
}

#[cfg(feature = "std")]
impl From<SocketAddrV4> for CompactAddr {
    fn from(value: SocketAddrV4) -> Self {
        CompactAddr::V4(CompactAddrV4::from(value))
    }
}

#[cfg(feature = "std")]
impl From<SocketAddrV6> for CompactAddr {
    fn from(value: SocketAddrV6) -> Self {
        CompactAddr::V6(CompactAddrV6::from(value))
    }
}

#[cfg(feature = "std")]
impl From<SocketAddr> for CompactAddr {
    fn from(value: SocketAddr) -> Self {
        match value {
            SocketAddr::V4(value) => CompactAddr::V4(CompactAddrV4::from(value)),
            SocketAddr::V6(value) => CompactAddr::V6(CompactAddrV6::from(value)),
        }
    }
}

#[cfg(feature = "std")]
impl From<CompactAddr> for SocketAddr {
    fn from(value: CompactAddr) -> Self {
        match value {
            CompactAddr::V4(value) => SocketAddr::from(value),
            CompactAddr::V6(value) => SocketAddr::from(value),
        }
    }
}

fn decode_addr_ipv4_list<B>(nodes: B) -> Result<Vec<AddrId<CompactAddrV4>>, Error>
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
            AddrId::new(CompactAddrV4::from(compact_addr), id)
        })
        .collect::<Vec<_>>())
}

fn decode_addr_ipv6_list<B>(nodes6: B) -> Result<Vec<AddrId<CompactAddrV6>>, Error>
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
            let addr = CompactAddrV6::from(compact_addr);

            AddrId::new(addr, id)
        })
        .collect::<Vec<_>>())
}

pub mod announce_peer;
pub mod error;
pub mod find_node;
pub mod get_peers;
pub mod ping;
pub mod ser;
pub mod transaction;

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;

    #[test]
    fn compact_addr_v4_display() {
        let ipv4_addr_str = "172.16.2.0";
        let ipv4_addr = Ipv4Addr::from_str(ipv4_addr_str).unwrap();
        let socket_addr_v4 = SocketAddrV4::new(ipv4_addr, 6881);
        let compact_addr_v4 = CompactAddrV4::from(socket_addr_v4);
        assert_eq!(
            format!("{}", compact_addr_v4),
            format!("{}:6881", ipv4_addr_str)
        );
    }

    #[test]
    fn compact_addr_v6_display() {
        let ipv6_addr_str = "2001:0db8:0001:0000:0000:8a2e:0370:7335";
        let ipv6_addr = Ipv6Addr::from_str(ipv6_addr_str).unwrap();
        let socket_addr_v6 = SocketAddrV6::new(ipv6_addr, 6881, 0, 0);
        let compact_addr_v6 = CompactAddrV6::from(socket_addr_v6);
        assert_eq!(
            format!("{}", compact_addr_v6),
            format!("[{}]:6881", ipv6_addr_str)
        );
    }
}
