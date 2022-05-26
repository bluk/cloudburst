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

use bytes::Bytes;
use core::{borrow::Borrow, fmt, time::Duration};
use gen_value::{index::Allocator, unmanaged::UnmanagedGenVec, Incrementable};
use serde_derive::{Deserialize, Serialize};

use crate::{
    conn,
    piece::{self, Index, IndexBitfield},
    protocol::{BitfieldMsg, CancelMsg, Frame, HaveMsg, PieceMsg, RequestMsg, ReservedBytes},
    time,
};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::{string::String, vec::Vec};

/// A peer's ID.
#[derive(Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Id(pub [u8; 20]);

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

fmt_byte_array!(Id);

/// A local peer's ID.
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LocalId(pub Id);

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

/// History of metrics.
#[derive(Clone, Copy, Debug)]
pub struct MetricsHistory<const SIZE: usize> {
    /// A limited history of messages.
    history: [conn::Metrics; SIZE],
    /// The last index which history was stored at.
    history_index: usize,
}

impl<const SIZE: usize> Default for MetricsHistory<SIZE> {
    fn default() -> Self {
        assert!(SIZE > 0);
        Self {
            history: [conn::Metrics::default(); SIZE],
            history_index: SIZE - 1,
        }
    }
}

impl<const SIZE: usize> MetricsHistory<SIZE> {
    /// Returns an accumulation of the previous historical metrics.
    ///
    /// `count` is the number of previous historical metrics to use.
    ///
    /// # Panics
    ///
    /// Panics if the number of requested accumulated metrics is greater than
    /// the length of the stored history.
    #[must_use]
    pub fn prev_metrics(&self, count: usize) -> conn::Metrics {
        assert!(count <= SIZE, "Requested more metrics than available");

        let mut index = self.history_index;
        let mut metrics = self.history[index];
        for _ in 0..count {
            if index == 0 {
                index = self.history.len();
            }
            index -= 1;
            metrics += self.history[index];
        }
        metrics
    }

    /// Inserts the current metrics to the history.
    pub fn insert(&mut self, metrics: conn::Metrics) {
        self.history_index = (self.history_index + 1) % self.history.len();
        self.history[self.history_index] = metrics;
    }
}

/// Indicates if the message has been sent or not.
#[derive(Debug)]
enum SendState<T> {
    /// State which has not been sent yet
    NotSent(T),
    /// State has been sent
    Sent(T),
}

/// A peer's state.
#[derive(Debug)]
struct State<Instant> {
    /// The local choke state for the remote peer
    local_choke: SendState<Choke>,
    /// The next Instant when the choke state can be sent
    next_choke_deadline: Instant,
    /// The local interest state for the remote peer
    local_interest: SendState<Interest>,
    /// The next Instant when the interest state can be sent
    next_interest_deadline: Instant,
    /// The remote choke state for the local node
    remote_choke: Choke,
    /// The remote interest state for the local node
    remote_interest: Interest,
    /// Timeout for when a message should have been received by the peer.
    read_deadline: Instant,
    /// Timeout for when a keep alive message should be sent.
    ///
    /// The timeout should be reset whenever any message is sent.
    write_deadline: Instant,
}

impl<Instant> State<Instant>
where
    Instant: time::Instant,
{
    /// Instantiates a new peer state.
    #[must_use]
    fn new(now: Instant, read_timeout: Duration, write_timeout: Duration) -> Self {
        Self {
            local_choke: SendState::Sent(Choke::Choked),
            next_choke_deadline: now.clone(),
            local_interest: SendState::Sent(Interest::NotInterested),
            next_interest_deadline: now.clone(),
            remote_choke: Choke::Choked,
            remote_interest: Interest::NotInterested,
            read_deadline: now.clone() + read_timeout,
            write_deadline: now + write_timeout,
        }
    }

    /// Returns the local interest last sent to the remote.
    #[must_use]
    #[inline]
    fn local_interest_as_remote_sees(&self) -> Interest {
        match self.local_interest {
            SendState::NotSent(state) => match state {
                Interest::Interested => Interest::NotInterested,
                Interest::NotInterested => Interest::Interested,
            },
            SendState::Sent(state) => state,
        }
    }

    /// Returns the local choke state last sent to the remote.
    #[must_use]
    #[inline]
    fn local_choke_as_remote_sees(&self) -> Choke {
        match self.local_choke {
            SendState::NotSent(state) => match state {
                Choke::Choked => Choke::NotChoked,
                Choke::NotChoked => Choke::Choked,
            },
            SendState::Sent(state) => state,
        }
    }

    /// Returns true if the remote peer is in state where it can send requests.
    #[must_use]
    #[inline]
    fn remote_unchoked_and_interested(&self) -> bool {
        self.remote_interest == Interest::Interested
            && self.local_choke_as_remote_sees() == Choke::NotChoked
    }

    /// Choke the remote peer.
    ///
    /// Returns true if the peer should write out its state.
    #[must_use]
    fn choke(&mut self) -> bool {
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
    fn unchoke(&mut self) -> bool {
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
    fn interested(&mut self) -> bool {
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
    fn not_interested(&mut self) -> bool {
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
    fn should_write(&self, now: &Instant) -> bool {
        if self.write_deadline <= *now {
            return true;
        }

        match self.local_choke {
            SendState::NotSent(_) => {
                if self.next_choke_deadline < *now {
                    return true;
                }
            }
            SendState::Sent(_) => {}
        }

        match self.local_interest {
            SendState::NotSent(_) => {
                if self.next_interest_deadline < *now {
                    return true;
                }
            }
            SendState::Sent(_) => {}
        }

        false
    }
}

/// Updates the state for a session when messages are written to a peer.
#[derive(Debug)]
pub struct Writer<'a, Instant> {
    state: &'a mut State<Instant>,
    peer_have_pieces: &'a IndexBitfield,
}

impl<'a, Instant> Writer<'a, Instant>
where
    Instant: time::Instant,
{
    /// Returns the pieces which the peer has.
    #[must_use]
    #[inline]
    pub fn peer_have_pieces(&self) -> &IndexBitfield {
        self.peer_have_pieces
    }

    /// Returns a choke state to be written to the peer.
    ///
    /// The `next_state_change` parameter is used to determine when the next
    /// choke state change can be sent.
    ///
    /// If there is no state change, then `None` is returned.  State changes may
    /// be delayed for a period of time to avoid quickly changing the state back
    /// and forth.
    pub fn choke(&mut self, next_state_change: Duration, now: Instant) -> Option<Choke> {
        if self.state.next_choke_deadline <= now {
            match self.state.local_choke {
                SendState::NotSent(choke_state) => match choke_state {
                    Choke::Choked => {
                        self.state.local_choke = SendState::Sent(choke_state);
                        self.state.next_choke_deadline = now + next_state_change;
                        return Some(Choke::Choked);
                    }
                    Choke::NotChoked => {
                        self.state.local_choke = SendState::Sent(choke_state);
                        self.state.next_choke_deadline = now + next_state_change;
                        return Some(Choke::NotChoked);
                    }
                },
                SendState::Sent(_) => {}
            }
        }

        None
    }

    /// Returns an interest state to be written to the peer.
    ///
    /// The `next_state_change` parameter is used to determine when the next
    /// interest state change can be sent.
    ///
    /// If there is no state change, then `None` is returned.  State changes may
    /// be delayed for a period of time to avoid quickly changing the state back
    /// and forth.
    pub fn interest(&mut self, next_state_change: Duration, now: Instant) -> Option<Interest> {
        if self.state.next_interest_deadline <= now {
            match self.state.local_interest {
                SendState::NotSent(interest_state) => match interest_state {
                    Interest::Interested => {
                        self.state.local_interest = SendState::Sent(interest_state);
                        self.state.next_interest_deadline = now + next_state_change;
                        return Some(Interest::Interested);
                    }
                    Interest::NotInterested => {
                        self.state.local_interest = SendState::Sent(interest_state);
                        self.state.next_interest_deadline = now + next_state_change;
                        return Some(Interest::NotInterested);
                    }
                },
                SendState::Sent(_) => {}
            }
        }

        None
    }

    /// Returns true if blocks requests (or cancellation of previous block requests) can be sent.
    #[must_use]
    #[inline]
    pub fn can_request_blocks(&mut self) -> bool {
        self.state.remote_choke == Choke::NotChoked
            && self.state.local_interest_as_remote_sees() == Interest::Interested
    }

    /// Returns true if block data can be sent.
    #[must_use]
    #[inline]
    pub fn can_provide_blocks(&mut self) -> bool {
        self.state.local_choke_as_remote_sees() == Choke::NotChoked
            && self.state.remote_interest == Interest::Interested
    }

    /// Returns true if a keep alive should be sent.
    ///
    /// This method should be called after all attempts to send other messages
    /// are tried first.
    #[must_use]
    #[inline]
    pub fn should_send_keepalive(&mut self, now: &Instant) -> bool {
        self.state.write_deadline <= *now
    }

    /// Update the write deadline for when a message should be sent to keep the
    /// connection alive.
    ///
    /// This method should be called when any message is sent to the peer.
    #[inline]
    pub fn on_write(&mut self, timeout: Duration, now: Instant) {
        self.state.write_deadline = now + timeout;
    }
}

/// An ID cannot be allocated for the peer.
///
/// If a peer disconnects, an ID may become available (but is not guaranteed).
/// In most cases, the newly connected peer should be disconnected unless an
/// existing peer can be disconnected.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[cfg_attr(feature = "std", error("an identifier could not be allocated"))]
pub struct CouldNotAllocateId;

/// Invalid input was received from a peer.
///
/// The expectation is that the peer will be disconnected from.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[cfg_attr(feature = "std", error("peer sent invalid input"))]
pub struct InvalidInput;

/// Stores and updates the state of peers.
///
/// Usually, there is a singleton instance of a `Session` which manages the
/// state for peers across all torrents.
///
/// Any peer related event usually will require interaction with the session.
/// After handshakes are exchanged with a peer, the peer can be inserted into the
/// session and a peer [`SessionId`] is returned.
///
/// The `SessionId` is valid until the peer is removed from the session.
/// All methods must be called with a valid `SessionId`.
///
/// When a message is received from a peer, a callback on the session should be
/// invoked. For instance, if the remote peer sends a [`HaveMsg`] message, the
/// [`on_read_have()`][Self::on_read_have()] method should be called.
///
/// When a peer's connection can be written to, the
/// [`get_writer()`][Self::get_writer()] method should be invoked. The
/// [`Writer`] has methods like
/// [`interest()`][Writer::interest()] which should be
/// called to see if an [`Interest`] state change should be sent. To determine
/// if there are state messages yet to be written, the
/// [`should_write`][Self::should_write] method can be called.
///
/// A method must be called when a message is received or sent because the read
/// and write timeouts are updated on method callbacks.
///
/// Besides callbacks when a message is received or sent, the
/// [`choke()`][Self::choke()] and [`unchoke()`][Self::unchoke()] method should
/// be called when an algorithm determines which peers it wishes to provide
/// blocks for. Similarly, [`interested()`][Self::interested()] and
/// [`not_interested()`][Self::not_interested()] can be called if the peer has
/// blocks which are not available locally.
///
/// The state which is kept by the session include:
///
/// * [`Id`] and [`ReservedBytes`] from the handshake.
/// * The [`Choke`] and [`Interest`] state for and from the peer
/// * The pieces which the remote peer has
/// * The read and write timeout deadlines
///
/// Notably there is no direct input/output. The session only maintains state.
/// It is intended to be reusable across different I/O implementations (e.g.
/// different async runtimes and sync implementations).
///
/// Furthermore, there is information intentionally left to the caller of the
/// session to manage. Stateful data which is expected to be managed externally:
///
/// * A list of valid peer `SessionId`s
/// * The torrent which is associated with the peer
/// * Any metrics (such as bandwidth usage) associated with a peer
/// * What blocks have been requested from and by a peer
/// * Block data which should be sent to a peer
/// * Block data received from the peer
/// * The locally available piece indexes which should be announced to each peer
///
/// Depending on how I/O is performed, there are different implementations
/// dependent on the environment.
#[derive(Debug)]
pub struct Session<Instant, PeerGen = usize, PeerIndex = usize> {
    /// A generator for peer IDs.
    id_alloc: Allocator<PeerGen, PeerIndex, SessionId<PeerGen, PeerIndex>>,

    reserved_bytes: SessionIdGenVec<ReservedBytes, PeerGen, PeerIndex>,
    id: SessionIdGenVec<Id, PeerGen, PeerIndex>,
    state: SessionIdGenVec<State<Instant>, PeerGen, PeerIndex>,
    have_pieces: SessionIdGenVec<IndexBitfield, PeerGen, PeerIndex>,

    /// The count of peers which are interested and can request blocks
    unchoked_and_interested_count: usize,
}

impl<Instant, PeerGen, PeerIndex> Default for Session<Instant, PeerGen, PeerIndex>
where
    PeerIndex: Default,
{
    fn default() -> Self {
        Self {
            id_alloc: Allocator::default(),
            reserved_bytes: SessionIdGenVec::default(),
            id: SessionIdGenVec::default(),
            state: SessionIdGenVec::default(),
            have_pieces: SessionIdGenVec::default(),
            unchoked_and_interested_count: 0,
        }
    }
}

impl<Instant, PeerGen, PeerIndex> Session<Instant, PeerGen, PeerIndex> {
    /// Returns the number of peers which are interested and can request blocks.
    #[inline]
    #[must_use]
    pub fn unchoked_and_interested_count(&self) -> usize {
        self.unchoked_and_interested_count
    }
}

impl<Instant, PeerGen, PeerIndex> Session<Instant, PeerGen, PeerIndex>
where
    Instant: time::Instant,
    PeerGen: PartialEq,
    PeerIndex: Into<usize>,
{
    /// Returns the reserved bytes received during the connection handshake.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_reserved_bytes(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> ReservedBytes {
        self.reserved_bytes[peer_id]
    }

    /// Returns the [`Id`] received during the connection handshake.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_id(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> Id {
        self.id[peer_id]
    }

    /// Returns the local choke state for the remote.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_choke(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> Choke {
        self.state[peer_id].local_choke_as_remote_sees()
    }

    /// Returns the local interest state for the remote.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_interest(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> Interest {
        self.state[peer_id].local_interest_as_remote_sees()
    }

    /// Returns the choke state from the remote for the local node.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_remote_choke(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> Choke {
        self.state[peer_id].remote_choke
    }

    /// Returns the interest state from the remote for the local node.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_remote_interest(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> Interest {
        self.state[peer_id].remote_interest
    }

    /// Returns the have pieces bitfield.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_have_pieces(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> &IndexBitfield {
        &self.have_pieces[peer_id]
    }

    /// Returns the read deadline.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_read_deadline(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> Instant {
        self.state[peer_id].read_deadline.clone()
    }

    /// Returns the write deadline.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn get_write_deadline(&self, peer_id: SessionId<PeerGen, PeerIndex>) -> Instant {
        self.state[peer_id].write_deadline.clone()
    }

    /// Returns true if the peer should send a message.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    #[must_use]
    pub fn should_write(&self, peer_id: SessionId<PeerGen, PeerIndex>, now: &Instant) -> bool {
        self.state[peer_id].should_write(now)
    }

    /// Chokes a peer.
    ///
    /// Returns true if the peer should write out its state.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[must_use]
    pub fn choke(&mut self, peer_id: SessionId<PeerGen, PeerIndex>) -> bool {
        let state = &mut self.state[peer_id];
        if state.remote_unchoked_and_interested() {
            self.unchoked_and_interested_count =
                self.unchoked_and_interested_count.checked_sub(1).unwrap();
        }

        state.choke()
    }

    /// Unchokes a peer.
    ///
    /// Returns true if the peer should write out its state.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[must_use]
    pub fn unchoke(&mut self, peer_id: SessionId<PeerGen, PeerIndex>) -> bool {
        let state = &mut self.state[peer_id];
        let should_write = state.unchoke();
        if state.remote_unchoked_and_interested() {
            self.unchoked_and_interested_count =
                self.unchoked_and_interested_count.checked_add(1).unwrap();
        }
        should_write
    }

    /// Interested in peer.
    ///
    /// Returns true if the peer should write out its state.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[must_use]
    #[inline]
    pub fn interested(&mut self, peer_id: SessionId<PeerGen, PeerIndex>) -> bool {
        self.state[peer_id].interested()
    }

    /// Not interested in peer.
    ///
    /// Returns true if the peer should write out its state.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[must_use]
    #[inline]
    pub fn not_interested(&mut self, peer_id: SessionId<PeerGen, PeerIndex>) -> bool {
        self.state[peer_id].not_interested()
    }

    /// Callback when a choke message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_choke(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id];
        state.read_deadline = now + next_read;
        state.remote_choke = Choke::Choked;
        Ok(())
    }

    /// Callback when an unchoke message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_unchoke(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id];
        state.read_deadline = now + next_read;
        state.remote_choke = Choke::NotChoked;
        Ok(())
    }

    /// Callback when an interested message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_interested(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id];
        state.read_deadline = now + next_read;
        state.remote_interest = Interest::Interested;
        if state.remote_unchoked_and_interested() {
            self.unchoked_and_interested_count =
                self.unchoked_and_interested_count.checked_add(1).unwrap();
        }
        Ok(())
    }

    /// Callback when a not interested message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_not_interested(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id];
        state.read_deadline = now + next_read;
        if state.remote_unchoked_and_interested() {
            self.unchoked_and_interested_count =
                self.unchoked_and_interested_count.checked_sub(1).unwrap();
        }
        state.remote_interest = Interest::NotInterested;
        Ok(())
    }

    /// Callback when a piece message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_piece(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        _piece_msg: &PieceMsg,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id];
        state.read_deadline = now + next_read;

        Ok(())
    }

    /// Callback when a cancel message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_cancel(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        _cancel_msg: &CancelMsg,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id];
        state.read_deadline = now + next_read;

        Ok(())
    }

    /// Callback when a keep alive message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_keepalive(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id];
        state.read_deadline = now + next_read;

        Ok(())
    }

    /// Callback when an unknown message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_unknown(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        _msg_type: u8,
        _msg_data: &Bytes,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id];
        state.read_deadline = now + next_read;

        Ok(())
    }
}

impl<Instant, PeerGen, PeerIndex> Session<Instant, PeerGen, PeerIndex>
where
    Instant: time::Instant,
    PeerGen: Clone + PartialEq,
    PeerIndex: Clone + Into<usize>,
{
    /// Callback when a have piece message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_have(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        have_msg: &HaveMsg,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id.clone()];
        state.read_deadline = now + next_read;

        let have_pieces = &mut self.have_pieces[peer_id];
        if have_pieces.get(have_msg.0) {
            // tracing::trace!(?peer_id, %index, "duplicate have message");
            return Err(InvalidInput);
        }
        have_pieces.set(have_msg.0, true);
        Ok(())
    }

    /// Callback when a bitfield message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_bitfield(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        bitfield_msg: &BitfieldMsg,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id.clone()];
        state.read_deadline = now + next_read;

        let have_pieces = &mut self.have_pieces[peer_id];
        if piece::verify_bitfield(have_pieces.max_index(), &bitfield_msg.0).is_err() {
            // tracing::trace!(?peer_id, "invalid bitfield message");
            return Err(InvalidInput);
        }
        *have_pieces = IndexBitfield::from_slice(&bitfield_msg.0, have_pieces.max_index());

        Ok(())
    }

    /// Callback when a request message is received from a peer.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message caused an invalid state change.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    #[inline]
    pub fn on_read_request(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
        request_msg: &RequestMsg,
        next_read: Duration,
        now: Instant,
    ) -> Result<(), InvalidInput> {
        let state = &mut self.state[peer_id.clone()];
        state.read_deadline = now + next_read;
        match state.remote_interest {
            Interest::NotInterested => {
                return Err(InvalidInput);
            }
            Interest::Interested => {}
        }

        if self.have_pieces[peer_id].get(request_msg.0.index) {
            // Peer said it already had this piece
            // tracing::trace!(?peer_id, "peer is requesting a piece it already has");
            return Err(InvalidInput);
        }

        Ok(())
    }

    /// Returns the [Writer] for a peer.
    #[must_use]
    #[inline]
    pub fn get_writer(&mut self, peer_id: SessionId<PeerGen, PeerIndex>) -> Writer<'_, Instant> {
        Writer {
            state: &mut self.state[peer_id.clone()],
            peer_have_pieces: &mut self.have_pieces[peer_id],
        }
    }
}

impl<Instant, PeerGen, PeerIndex> Session<Instant, PeerGen, PeerIndex>
where
    Instant: time::Instant,
{
    /// Inserts a peer into the session.
    ///
    /// # Errors
    ///
    /// Returns an error if the [`SessionId`] could not be allocated.
    ///
    /// # Panics
    ///
    /// Panics if memory cannot be allocated.
    pub fn insert(
        &mut self,
        reserved_bytes: ReservedBytes,
        id: Id,
        max_index: Index,
        read_timeout: Duration,
        write_timeout: Duration,
        now: Instant,
    ) -> Result<SessionId<PeerGen, PeerIndex>, CouldNotAllocateId>
    where
        PeerGen: Clone + Default + PartialOrd,
        PeerIndex: Clone + Into<usize> + Incrementable,
    {
        let peer_id = self.id_alloc.alloc().ok_or(CouldNotAllocateId)?;

        self.reserved_bytes
            .set_or_push(peer_id.clone(), reserved_bytes)
            .unwrap();
        self.id.set_or_push(peer_id.clone(), id).unwrap();
        self.state
            .set_or_push(
                peer_id.clone(),
                State::new(now, read_timeout, write_timeout),
            )
            .unwrap();

        if let Ok(have_pieces) = self.have_pieces.get_mut(peer_id.clone()) {
            have_pieces.clear_with_max_index(max_index);
        } else {
            self.have_pieces
                .set_or_push(peer_id.clone(), IndexBitfield::with_max_index(max_index))
                .unwrap();
        }

        Ok(peer_id)
    }

    /// Removes a peer from the session.
    ///
    /// Returns the next generation of the peer ID. The next generation can be
    /// used to increase the generation of any generational index vector using
    /// the peer ID as a generational index.
    ///
    /// # Panics
    ///
    /// Panics if the peer ID is invalid.
    pub fn remove(
        &mut self,
        peer_id: SessionId<PeerGen, PeerIndex>,
    ) -> Option<&SessionId<PeerGen, PeerIndex>>
    where
        PeerGen: Clone + Incrementable,
        PeerIndex: Clone + Into<usize>,
    {
        if self.state[peer_id.clone()].remote_unchoked_and_interested() {
            self.unchoked_and_interested_count =
                self.unchoked_and_interested_count.checked_sub(1).unwrap();
        }

        let next_gen_id = self.id_alloc.dealloc(peer_id);
        if let Some(next_gen_id) = next_gen_id {
            self.reserved_bytes
                .set_next_gen(next_gen_id.clone())
                .unwrap();
            self.id.set_next_gen(next_gen_id.clone()).unwrap();
            self.state.set_next_gen(next_gen_id.clone()).unwrap();
            self.have_pieces.set_next_gen(next_gen_id.clone()).unwrap();
        }

        next_gen_id
    }
}
