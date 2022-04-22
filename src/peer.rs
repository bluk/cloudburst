// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A peer in the torrent network.
//!
//! Peers have [Id]s and [Choke] and [Interest] states.

use core::{borrow::Borrow, fmt};
use gen_value::unmanaged::UnmanagedGenVec;
use serde_derive::{Deserialize, Serialize};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::{string::String, vec::Vec};

/// A peer's ID.
#[derive(Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Id(pub(crate) [u8; 20]);

impl Id {
    /// Instantiates an Id with bytes representing the 160-bit value.
    #[must_use]
    pub fn new(bytes: [u8; 20]) -> Self {
        Self(bytes)
    }
}

impl AsRef<[u8]> for Id {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Borrow<[u8]> for Id {
    fn borrow(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 20]> for Id {
    fn from(bytes: [u8; 20]) -> Self {
        Self(bytes)
    }
}

impl From<Id> for Vec<u8> {
    fn from(id: Id) -> Self {
        Vec::from(id.0)
    }
}

impl From<Id> for [u8; 20] {
    fn from(id: Id) -> Self {
        id.0
    }
}

impl fmt::Debug for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct IdDebug<'a>(&'a [u8; 20]);

        impl<'a> fmt::Debug for IdDebug<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                for b in self.0.iter() {
                    write!(f, "{:02x}", b)?;
                }
                Ok(())
            }
        }

        f.debug_tuple("Id").field(&IdDebug(&self.0)).finish()
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in &self.0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

/// A local peer's ID.
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LocalId(Id);

impl AsRef<[u8]> for LocalId {
    fn as_ref(&self) -> &[u8] {
        &(self.0).0
    }
}

impl Borrow<[u8]> for LocalId {
    fn borrow(&self) -> &[u8] {
        &(self.0).0
    }
}

impl From<Id> for LocalId {
    fn from(id: Id) -> LocalId {
        LocalId(id)
    }
}

impl From<LocalId> for Id {
    fn from(local_id: LocalId) -> Id {
        local_id.0
    }
}

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in &(self.0).0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

/// Represents if a peer will fulfill block requests.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Choke {
    /// The peer will not fulfill block requests
    NotChoked,
    /// The peer will fulfill block requests
    Choked,
}

/// Represents if a peer will request blocks.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Interest {
    /// The peer does not want any pieces
    NotInterested,
    /// The peer wants pieces
    Interested,
}

/// An Internet address.
#[cfg(feature = "std")]
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Addr {
    /// Represents a IPv4 or IPv6 address.
    IpAddr(std::net::IpAddr),
    /// Represents a domain name which needs to be resolved into an IP address.
    String(String),
}

#[cfg(feature = "std")]
impl fmt::Display for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IpAddr(addr) => addr.fmt(f),
            Self::String(s) => s.fmt(f),
        }
    }
}

/// Represents an Internet address and port.
#[cfg(feature = "std")]
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SocketAddr {
    /// The address
    pub addr: Addr,
    /// The port
    pub port: u16,
}

#[cfg(feature = "std")]
impl std::net::ToSocketAddrs for SocketAddr {
    type Iter = std::vec::IntoIter<std::net::SocketAddr>;

    fn to_socket_addrs(&self) -> std::io::Result<Self::Iter> {
        match &self.addr {
            Addr::IpAddr(ip_addr) => (*ip_addr, self.port)
                .to_socket_addrs()
                .map(|i| i.into_iter().collect::<Vec<_>>().into_iter()),
            Addr::String(s) => (s.clone(), self.port).to_socket_addrs(),
        }
    }
}

#[cfg(feature = "std")]
impl From<std::net::SocketAddr> for SocketAddr {
    fn from(socket_addr: std::net::SocketAddr) -> Self {
        Self {
            addr: Addr::IpAddr(socket_addr.ip()),
            port: socket_addr.port(),
        }
    }
}

#[cfg(feature = "std")]
impl<I> From<(I, u16)> for SocketAddr
where
    I: Into<std::net::IpAddr>,
{
    fn from(socket_addr: (I, u16)) -> Self {
        let addr = Addr::IpAddr(socket_addr.0.into());
        Self {
            addr,
            port: socket_addr.1,
        }
    }
}

#[cfg(feature = "std")]
impl fmt::Display for SocketAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.addr, self.port)
    }
}

/// A socket address with an optional peer ID.
#[cfg(feature = "std")]
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SocketAddrWithOptId {
    /// The peer's socket addresss
    pub socket_addr: SocketAddr,
    /// The peer's ID, if known
    pub id: Option<Id>,
}

/// Opaque identifier for a peer in a session.
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SessionId<G, I> {
    /// Index
    pub index: I,
    /// Generation
    pub gen: G,
}

impl<G, I> From<(I, G)> for SessionId<G, I> {
    fn from(value: (I, G)) -> Self {
        Self {
            index: value.0,
            gen: value.1,
        }
    }
}

impl<G, I> From<SessionId<G, I>> for (I, G) {
    fn from(value: SessionId<G, I>) -> Self {
        (value.index, value.gen)
    }
}

/// A generational vector with peer session IDs as the indexes.
pub type SessionIdGenVec<T, PeerGen, PeerIndex> =
    UnmanagedGenVec<T, PeerGen, PeerIndex, SessionId<PeerGen, PeerIndex>>;
