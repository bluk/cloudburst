// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Portable time traits.

use core::{ops::Add, time::Duration};

/// A trait for the equivalent of [`Instant`][std::time::Instant].
pub trait Instant: Clone + Ord + Add<Duration, Output = Self> {
    /// Returns the current `Instant`.
    fn now() -> Self;
}

#[cfg(feature = "std")]
impl Instant for std::time::Instant {
    fn now() -> Self {
        std::time::Instant::now()
    }
}
