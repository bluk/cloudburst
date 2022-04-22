// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A swarm of peers.

use gen_value::unmanaged::UnmanagedGenVec;

use crate::{conn, peer, protocol};

/// Metrics for the torrent.
///
/// Accumulated from the individual peer's message exchanges.
#[derive(Debug, Default, Clone, Copy)]
pub struct Metrics {
    /// The total torrent sent message metrics
    pub sent: protocol::Metrics,
    /// The total torrent received message metrics
    pub received: protocol::Metrics,
}

impl core::ops::Add<conn::Metrics> for Metrics {
    type Output = Metrics;

    fn add(mut self, rhs: conn::Metrics) -> Metrics {
        self.sent += rhs.sent;
        self.received += rhs.received;
        self
    }
}

impl core::ops::AddAssign<conn::Metrics> for Metrics {
    fn add_assign(&mut self, rhs: conn::Metrics) {
        self.sent += rhs.sent;
        self.received += rhs.received;
    }
}

/// Opaque identifier for a torrent in a session.
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

/// A generational vector with torrent session IDs as the indexes.
pub type SessionIdGenVec<T, PeerGen, PeerIndex> =
    UnmanagedGenVec<T, PeerGen, PeerIndex, SessionId<PeerGen, PeerIndex>>;

/// A torrent ID and a peer ID.
pub type SessionTorrentPeerId<PeerGen, TorrentGen, PeerIndex, TorrentIndex> = (
    SessionId<TorrentGen, TorrentIndex>,
    peer::SessionId<PeerGen, PeerIndex>,
);
