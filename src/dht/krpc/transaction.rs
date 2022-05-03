// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Transactions correlate a KRPC query with its response.

use core::convert::TryFrom;

/// An opaque identifer which correlates a KRPC query with a response or error.
///
/// An `Id` is returned when a query is written to the `Dht`. The caller should
/// hold onto the `Id`. When a message is read from the `Dht`, then the caller
/// should determine if the read message's `Id` is equal to the previously held
/// `Id`. If they are the same, then the read message is in response to the
/// original query.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Id([u8; 2]);

impl Id {
    /// Returns a random `Id`.
    ///
    /// # Errors
    ///
    /// Returns an error if the random number generator cannot fill a byte array.
    pub fn rand<R>(rng: &mut R) -> Result<Self, rand::Error>
    where
        R: rand::Rng,
    {
        let mut inner = [0u8; 2];
        rng.try_fill(&mut inner)?;
        Ok(Self(inner))
    }
}

impl From<u16> for Id {
    fn from(value: u16) -> Self {
        Self(value.to_be_bytes())
    }
}

impl TryFrom<&[u8]> for Id {
    type Error = core::array::TryFromSliceError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        <[u8; core::mem::size_of::<u16>()]>::try_from(value).map(Id)
    }
}

impl AsRef<[u8]> for Id {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
