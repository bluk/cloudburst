// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Connections to peers.

use crate::protocol;

/// Metrics for sent and received messages.
#[derive(Debug, Default, Clone, Copy)]
pub struct Metrics {
    /// The sent messages metrics
    pub sent: protocol::Metrics,
    /// The received messages metrics
    pub received: protocol::Metrics,
}

impl core::ops::Add for Metrics {
    type Output = Metrics;

    fn add(mut self, rhs: Metrics) -> Metrics {
        self.sent += rhs.sent;
        self.received += rhs.received;
        self
    }
}

impl core::ops::AddAssign for Metrics {
    fn add_assign(&mut self, rhs: Metrics) {
        self.sent += rhs.sent;
        self.received += rhs.received;
    }
}
