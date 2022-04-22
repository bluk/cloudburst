// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A swarm of peers.

use crate::{conn, protocol};

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
