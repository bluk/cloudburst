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
use std::{
    string::String,
    time::{Duration, Instant},
    vec::Vec,
};

use crate::{conn, protocol::Frame};

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

/// A peer's metrics.
#[derive(Clone, Copy, Default, Debug)]
pub struct Metrics {
    /// The current interval's metrics
    pub current: conn::Metrics,
    /// The total metrics accumulated
    pub total: conn::Metrics,
}

impl Metrics {
    /// Instantiates a new instance with the last message received and sent instant set to now.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a frame's data to the sent metrics.
    pub fn add_sent_frame(&mut self, frame: &Frame) {
        self.current.sent.add_frame(frame);
        self.total.sent.add_frame(frame);
    }

    /// Adds a frame's data to the received metrics.
    pub fn add_received_frame(&mut self, frame: &Frame) {
        self.current.received.add_frame(frame);
        self.total.received.add_frame(frame);
    }

    /// Resets the current metrics to 0.
    pub fn reset_current(&mut self) {
        self.current = conn::Metrics::default();
    }

    /// Returns true if the peer has ever been unchoked before.
    ///
    /// Useful for finding peers which could be optimistically unchoked.
    #[inline]
    #[must_use]
    pub fn has_been_unchoked(&self) -> bool {
        self.total.sent.unchoke_msgs != 0
    }

    /// Returns true if any message has been received.
    ///
    /// Useful for determining if a connection is sending the bitfield messsage as the first message.
    #[inline]
    #[must_use]
    pub fn has_received_any(&self) -> bool {
        self.total.received.is_any_nonzero()
    }
}

/// Indicates if the message has been sent or not.
#[derive(Debug)]
pub enum SendState<T> {
    /// State which has not been sent yet
    NotSent(T),
    /// State has been sent
    Sent(T),
}

/// A peer's state.
#[derive(Debug)]
#[cfg(feature = "std")]
pub struct State {
    /// The local choke state for the remote peer
    pub local_choke: SendState<Choke>,
    /// The next Instant when the choke state can be sent
    pub next_choke_deadline: Instant,
    /// The local interest state for the remote peer
    pub local_interest: SendState<Interest>,
    /// The next Instant when the interest state can be sent
    pub next_interest_deadline: Instant,
    /// The remote choke state for the local node
    pub remote_choke: Choke,
    /// The remote interest state for the local node
    pub remote_interest: Interest,
    /// Timeout for when a message should have been received by the peer.
    pub read_deadline: Instant,
    /// Timeout for when a keep alive message should be sent.
    ///
    /// The timeout should be reset whenever any message is sent.
    pub write_deadline: Instant,
}

#[cfg(feature = "std")]
impl State {
    /// Instantiates a new peer state.
    #[must_use]
    pub fn new(now: Instant, read_timeout: Duration, write_timeout: Duration) -> Self {
        Self {
            local_choke: SendState::Sent(Choke::Choked),
            next_choke_deadline: now,
            local_interest: SendState::Sent(Interest::NotInterested),
            next_interest_deadline: now,
            remote_choke: Choke::Choked,
            remote_interest: Interest::NotInterested,
            read_deadline: now + read_timeout,
            write_deadline: now + write_timeout,
        }
    }

    /// Returns the local interest last sent to the remote.
    #[must_use]
    #[inline]
    pub fn local_interest_as_remote_sees(&self) -> Interest {
        match self.local_interest {
            SendState::NotSent(state) => match state {
                Interest::Interested => Interest::NotInterested,
                Interest::NotInterested => Interest::Interested,
            },
            SendState::Sent(state) => state,
        }
    }

    /// Returns the intended local interest state for the remote.
    #[must_use]
    #[inline]
    pub fn local_interest_as_local_sees(&self) -> Interest {
        match self.local_interest {
            SendState::NotSent(state) | SendState::Sent(state) => state,
        }
    }

    /// Returns the local choke state last sent to the remote.
    #[must_use]
    #[inline]
    pub fn local_choke_as_remote_sees(&self) -> Choke {
        match self.local_choke {
            SendState::NotSent(state) => match state {
                Choke::Choked => Choke::NotChoked,
                Choke::NotChoked => Choke::Choked,
            },
            SendState::Sent(state) => state,
        }
    }

    /// Returns the intended local choke state for the remote.
    #[must_use]
    #[inline]
    pub fn local_choke_as_local_sees(&self) -> Choke {
        match self.local_choke {
            SendState::NotSent(state) | SendState::Sent(state) => state,
        }
    }

    /// Returns true if the remote peer is in state where it can send requests.
    #[must_use]
    #[inline]
    pub fn remote_unchoked_and_interested(&self) -> bool {
        self.remote_interest == Interest::Interested
            && self.local_choke_as_remote_sees() == Choke::NotChoked
    }

    /// Choke the remote peer.
    ///
    /// Returns true if the peer should write out its state.
    #[must_use]
    pub fn choke(&mut self) -> bool {
        match self.local_choke {
            SendState::NotSent(choke_state) => match choke_state {
                Choke::Choked => true,
                Choke::NotChoked => {
                    self.local_choke = SendState::Sent(Choke::Choked);
                    true
                }
            },
            SendState::Sent(choke_state) => match choke_state {
                Choke::Choked => false,
                Choke::NotChoked => {
                    self.local_choke = SendState::NotSent(Choke::Choked);
                    true
                }
            },
        }
    }

    /// Unchoke the remote peer.
    ///
    /// Returns true if the peer should write out its state.
    #[must_use]
    pub fn unchoke(&mut self) -> bool {
        match self.local_choke {
            SendState::NotSent(choke_state) => match choke_state {
                Choke::Choked => {
                    self.local_choke = SendState::Sent(Choke::NotChoked);
                    true
                }
                Choke::NotChoked => true,
            },
            SendState::Sent(choke_state) => match choke_state {
                Choke::Choked => {
                    self.local_choke = SendState::NotSent(Choke::NotChoked);
                    true
                }
                Choke::NotChoked => false,
            },
        }
    }

    /// Indicate interest in the remote peer.
    ///
    /// Returns true if the peer should write out its state.
    #[must_use]
    pub fn interested(&mut self) -> bool {
        match self.local_interest {
            SendState::NotSent(state) => match state {
                Interest::Interested => true,
                Interest::NotInterested => {
                    self.local_interest = SendState::Sent(Interest::Interested);
                    true
                }
            },
            SendState::Sent(state) => match state {
                Interest::Interested => false,
                Interest::NotInterested => {
                    self.local_interest = SendState::NotSent(Interest::Interested);
                    true
                }
            },
        }
    }

    /// Indicate not interested in the remote peer.
    ///
    /// Returns true if the peer should write out its state.
    #[must_use]
    pub fn not_interested(&mut self) -> bool {
        match self.local_interest {
            SendState::NotSent(state) => match state {
                Interest::Interested => {
                    self.local_interest = SendState::Sent(Interest::NotInterested);
                    true
                }
                Interest::NotInterested => true,
            },
            SendState::Sent(state) => match state {
                Interest::Interested => {
                    self.local_interest = SendState::NotSent(Interest::NotInterested);
                    true
                }
                Interest::NotInterested => false,
            },
        }
    }

    /// Returns true if there is a state change ready to be sent.
    #[must_use]
    pub fn should_write(&self, now: Instant) -> bool {
        if self.write_deadline <= now {
            return true;
        }

        match self.local_choke {
            SendState::NotSent(_) => {
                if self.next_choke_deadline < now {
                    return true;
                }
            }
            SendState::Sent(_) => {}
        }

        match self.local_interest {
            SendState::NotSent(_) => {
                if self.next_interest_deadline < now {
                    return true;
                }
            }
            SendState::Sent(_) => {}
        }

        false
    }
}
