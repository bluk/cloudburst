// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! KRPC messages are the protocol messages exchanged.

use core::{convert::TryFrom, fmt};
use serde::{
    de::{self, Visitor},
    Deserialize, Serialize,
};
use serde_bytes::{ByteBuf, Bytes};

#[cfg(feature = "std")]
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};

use super::node::Id;

/// Error for KRPC protocol.
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl Error {
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
        Self {
            kind: ErrorKind::BtBencode(e),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ErrorKind::BtBencode(error) => fmt::Display::fmt(error, f),
            ErrorKind::InvalidCompactAddr => f.write_str("invalid compact address"),
        }
    }
}

#[cfg(feature = "std")]
impl From<Error> for std::io::Error {
    fn from(error: Error) -> Self {
        match error.kind {
            ErrorKind::BtBencode(error) => std::io::Error::new(std::io::ErrorKind::Other, error),
            ErrorKind::InvalidCompactAddr => {
                std::io::Error::new(std::io::ErrorKind::InvalidInput, error)
            }
        }
    }
}

#[derive(Debug)]
enum ErrorKind {
    BtBencode(bt_bencode::Error),
    #[allow(dead_code)]
    InvalidCompactAddr,
}

/// Type of KRPC message.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Ty {
    /// Query message.
    Query,
    /// Response message.
    Response,
    /// Error message.
    Error,
    /// Unknown message type.
    Unknown,
}

impl<'a> From<&'a [u8]> for Ty {
    fn from(y: &'a [u8]) -> Self {
        match y {
            b"q" => Ty::Query,
            b"r" => Ty::Response,
            b"e" => Ty::Error,
            _ => Ty::Unknown,
        }
    }
}

impl<'a> From<&'a Bytes> for Ty {
    fn from(y: &'a Bytes) -> Self {
        match y.as_ref() {
            b"q" => Ty::Query,
            b"r" => Ty::Response,
            b"e" => Ty::Error,
            _ => Ty::Unknown,
        }
    }
}

impl<'a> From<&'a ByteBuf> for Ty {
    fn from(y: &'a ByteBuf) -> Self {
        match y.as_slice() {
            b"q" => Ty::Query,
            b"r" => Ty::Response,
            b"e" => Ty::Error,
            _ => Ty::Unknown,
        }
    }
}

/// A KRPC message.
#[derive(Debug, serde_derive::Deserialize)]
pub struct Msg<'a> {
    /// Transaction ID
    pub t: &'a [u8],
    /// Type of message
    pub y: &'a [u8],
    /// Client version
    pub v: Option<&'a [u8]>,

    /// Query method name
    pub q: Option<&'a [u8]>,
    /// Query arguments
    ///
    /// The value is the raw value for the `a` key. The bytes should be
    /// deserialized into a specific query argument type based on the method
    /// name.
    pub a: Option<&'a [u8]>,

    /// Response values
    ///
    /// The value is the raw value for the `r` key. The bytes should be
    /// deserialized into a specific response value type based on the
    /// transaction id.
    pub r: Option<&'a [u8]>,

    /// Error data
    ///
    /// The value is the raw value for the `e` key.
    pub e: Option<&'a [u8]>,
}

impl<'a> Msg<'a> {
    /// The transaction id for the message.
    #[inline]
    #[must_use]
    pub fn tx_id(&self) -> &[u8] {
        self.t
    }

    /// The type of message.
    #[inline]
    #[must_use]
    pub fn ty(&self) -> Ty {
        Ty::from(self.y)
    }

    /// The client version as a byte slice.
    #[inline]
    #[must_use]
    pub fn client_version(&self) -> Option<&[u8]> {
        self.v
    }

    /// The client version as a `str`.
    #[inline]
    #[must_use]
    pub fn client_version_str(&self) -> Option<&str> {
        self.v.and_then(|v| core::str::from_utf8(v).ok())
    }

    /// The query method name as a byte slice.
    #[inline]
    #[must_use]
    pub fn method_name(&self) -> Option<&[u8]> {
        self.q
    }

    /// The query method name as a `str`.
    #[inline]
    #[must_use]
    pub fn method_name_str(&self) -> Option<&str> {
        self.q.and_then(|q| core::str::from_utf8(q).ok())
    }

    /// The deserialized query arguments.
    ///
    /// # Example
    ///
    /// ```
    /// use cloudburst::dht::{krpc::{Msg, ping::QueryArgs}, node::Id};
    ///
    /// let ping_query = b"d1:ad2:id20:abcdefghij0123456789e1:q4:ping1:t2:aa1:y1:qe";
    /// let query: Msg<'_> = bt_bencode::from_slice(ping_query.as_slice())?;
    /// let query_args: QueryArgs<'_> = query.args().expect("arguments to exist")?;
    /// assert_eq!(query_args.id(), Some(Id::from(*b"abcdefghij0123456789")));
    ///
    /// # Ok::<(), bt_bencode::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn args<T>(&'a self) -> Option<Result<T, bt_bencode::Error>>
    where
        T: Deserialize<'a>,
    {
        self.a.map(bt_bencode::from_slice)
    }

    /// The deserialized response values.
    ///
    /// # Example
    ///
    /// ```
    /// use cloudburst::dht::{krpc::{Msg, ping::RespValues}, node::Id};
    ///
    /// let ping_resp = b"d1:rd2:id20:mnopqrstuvwxyz123456e1:t2:aa1:y1:re";
    /// let resp: Msg<'_> = bt_bencode::from_slice(ping_resp.as_slice())?;
    /// let resp_values: RespValues<'_> = resp.values().expect("response values to exist")?;
    /// assert_eq!(resp_values.id(), Some(Id::from(*b"mnopqrstuvwxyz123456")));
    ///
    /// # Ok::<(), bt_bencode::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn values<T>(&'a self) -> Option<Result<T, bt_bencode::Error>>
    where
        T: Deserialize<'a>,
    {
        self.r.map(bt_bencode::from_slice)
    }

    /// The raw captured response values data.
    #[inline]
    #[must_use]
    pub fn error(&self) -> Option<(ErrorCode, &str)> {
        self.e
            .and_then(|e| bt_bencode::from_slice::<(i64, &str)>(e).ok())
            .map(|(code, error_msg)| (ErrorCode::from(code), error_msg))
    }
}

/// Generic query arguments.
#[derive(Debug, serde_derive::Deserialize)]
pub struct QueryArgs<'a> {
    /// The querying node's ID
    #[serde(borrow)]
    pub id: &'a Bytes,
}

impl<'a> QueryArgs<'a> {
    /// Returns the querying node's ID.
    #[must_use]
    #[inline]
    pub fn id(&self) -> Option<Id> {
        Id::try_from(self.id.as_ref()).ok()
    }
}

/// Generic response value.
#[derive(Debug, serde_derive::Deserialize)]
pub struct RespValues<'a> {
    /// The queried node's ID
    #[serde(borrow)]
    pub id: &'a Bytes,
}

impl<'a> RespValues<'a> {
    /// Returns the querying node's ID.
    #[must_use]
    #[inline]
    pub fn id(&self) -> Option<Id> {
        Id::try_from(self.id.as_ref()).ok()
    }
}

/// Standard error codes in KRPC error messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
    Other(i64),
}

impl ErrorCode {
    /// The code used in a message to identify the message.
    #[must_use]
    #[inline]
    pub const fn code(self) -> i64 {
        match self {
            ErrorCode::GenericError => 201,
            ErrorCode::ServerError => 202,
            ErrorCode::ProtocolError => 203,
            ErrorCode::MethodUnknown => 204,
            ErrorCode::Other(n) => n,
        }
    }
}

impl From<i64> for ErrorCode {
    fn from(code: i64) -> Self {
        match code {
            201 => ErrorCode::GenericError,
            202 => ErrorCode::ServerError,
            203 => ErrorCode::ProtocolError,
            204 => ErrorCode::MethodUnknown,
            _ => ErrorCode::Other(code),
        }
    }
}

impl Serialize for ErrorCode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_i64(self.code())
    }
}

impl<'de> Deserialize<'de> for ErrorCode {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct I64Visitor;

        impl<'de> Visitor<'de> for I64Visitor {
            type Value = ErrorCode;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("enum ErrorCode")
            }

            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(ErrorCode::from(v))
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                i64::try_from(v)
                    .map_err(|_| de::Error::invalid_type(de::Unexpected::Unsigned(v), &self))
                    .and_then(|v| self.visit_i64(v))
            }
        }

        deserializer.deserialize_i64(I64Visitor)
    }
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

impl Serialize for CompactAddrV4 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_bytes(&self.0)
    }
}

impl<'a, 'de> Deserialize<'de> for CompactAddrV4
where
    'de: 'a,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct CompactAddrV4Visitor;

        impl<'de> Visitor<'de> for CompactAddrV4Visitor {
            type Value = CompactAddrV4;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("struct CompactAddrV4")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                match v.len() {
                    6 => Ok(CompactAddrV4::from(
                        <[u8; 6]>::try_from(v).expect("slice length is not correct"),
                    )),
                    l => Err(de::Error::invalid_length(l, &"a length of 6 bytes")),
                }
            }
        }

        deserializer.deserialize_bytes(CompactAddrV4Visitor)
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

impl Serialize for CompactAddrV6 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_bytes(&self.0)
    }
}

impl<'a, 'de> Deserialize<'de> for CompactAddrV6
where
    'de: 'a,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct CompactAddrV6Visitor;

        impl<'de> Visitor<'de> for CompactAddrV6Visitor {
            type Value = CompactAddrV6;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("struct CompactAddrV6")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                match v.len() {
                    18 => Ok(CompactAddrV6::from(
                        <[u8; 18]>::try_from(v).expect("slice length is not correct"),
                    )),
                    l => Err(de::Error::invalid_length(l, &"a length of 18 bytes")),
                }
            }
        }

        deserializer.deserialize_bytes(CompactAddrV6Visitor)
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

impl Serialize for CompactAddr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::V4(value) => Serialize::serialize(value, serializer),
            Self::V6(value) => Serialize::serialize(value, serializer),
        }
    }
}

impl<'a, 'de> Deserialize<'de> for CompactAddr
where
    'de: 'a,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct CompactAddrVisitor;

        impl<'de> Visitor<'de> for CompactAddrVisitor {
            type Value = CompactAddr;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("struct CompactAddr")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                match v.len() {
                    6 => Ok(CompactAddr::V4(CompactAddrV4::from(
                        <[u8; 6]>::try_from(v).expect("slice length is not correct"),
                    ))),
                    18 => Ok(CompactAddr::V6(CompactAddrV6::from(
                        <[u8; 18]>::try_from(v).expect("slice length is not correct"),
                    ))),
                    l => Err(de::Error::invalid_length(
                        l,
                        &"a length of either 6 or 18 bytes",
                    )),
                }
            }
        }

        deserializer.deserialize_bytes(CompactAddrVisitor)
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

pub mod announce_peer;
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
