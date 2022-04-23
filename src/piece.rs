// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Data is exchanged in terms of `Piece`s and `Block`s.
//!
//! The torrent's data is split into consecutive `Piece`s. `Piece`s are referenced
//! by [`Index`]. Each piece has the same [`Length`] except possibly the last piece.
//!
//! Peers request and send data in terms of [`Block`]s. A `Block` is a range of
//! data within a single `Piece`. The `Block` specifies which piece via a piece
//! `Index`, the starting byte offset within the piece via a [`BlockBegin`], and
//! the length of the data requested via [`BlockLength`].
//!
//! Assume the metainfo is for a single 31MiB file. The metainfo specifies the
//! piece `Length` is 2MiB. There are 16 pieces with all pieces having a length
//! of 2MiB except the last piece which is only 1MiB.
//!
//! A peer may need piece `3` from another peer. The peer can request the first
//! 16KiB of the piece by sending a request for a `Block` with piece index `3`,
//! beginning at offset `0`, and with a length of 16KiB. Next, the peer can
//! request a `Block` with index `3`, beginning at offset `16KiB`, and a length
//! of 16KiB. Similar to pieces, blocks usually have the same length except for
//! the last block request in a piece. The peer continues requesting `Block`s
//! until it receives all of the data in the piece.
//!
//! The received data can be verified to be correct by data in the metainfo.

use bytes::Bytes;
use core::{cmp::Ordering, fmt};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{vec, vec::Vec};
#[cfg(feature = "std")]
use std::{vec, vec::Vec};

/// A piece's index.
///
/// It is a zero based index.
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Index(u32);

impl From<u32> for Index {
    fn from(value: u32) -> Self {
        Index(value)
    }
}

impl From<Index> for u32 {
    fn from(value: Index) -> Self {
        value.0
    }
}

impl From<Index> for u64 {
    fn from(value: Index) -> Self {
        u64::from(value.0)
    }
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A piece's length.
///
/// The length of all pieces in a torrent, except the last piece which may be smaller.
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Length(u32);

impl From<u32> for Length {
    fn from(value: u32) -> Self {
        Length(value)
    }
}

impl From<Length> for u32 {
    fn from(value: Length) -> Self {
        value.0
    }
}

impl From<Length> for u64 {
    fn from(value: Length) -> Self {
        u64::from(value.0)
    }
}

impl fmt::Display for Length {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl PartialEq<BlockBegin> for Length {
    fn eq(&self, other: &BlockBegin) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd<BlockBegin> for Length {
    fn partial_cmp(&self, other: &BlockBegin) -> Option<Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

/// A byte offset in a piece to begin the block at.
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct BlockBegin(u32);

impl From<u32> for BlockBegin {
    fn from(value: u32) -> Self {
        BlockBegin(value)
    }
}

impl From<BlockBegin> for u32 {
    fn from(value: BlockBegin) -> Self {
        value.0
    }
}

impl From<BlockBegin> for u64 {
    fn from(value: BlockBegin) -> Self {
        u64::from(value.0)
    }
}

impl PartialEq<Length> for BlockBegin {
    fn eq(&self, other: &Length) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd<Length> for BlockBegin {
    fn partial_cmp(&self, other: &Length) -> Option<Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl fmt::Display for BlockBegin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// A block's length.
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct BlockLength(u32);

impl From<u32> for BlockLength {
    fn from(value: u32) -> Self {
        BlockLength(value)
    }
}

impl From<BlockLength> for u32 {
    fn from(value: BlockLength) -> Self {
        value.0
    }
}

impl From<BlockLength> for u64 {
    fn from(value: BlockLength) -> Self {
        u64::from(value.0)
    }
}

impl BlockLength {
    /// Maximum length of a block.
    pub const MAX: u32 = 16384;

    /// Maximum length of a block.
    pub const MAX_USIZE: usize = 16384;

    /// Maximum length of a block.
    #[must_use]
    pub const fn max() -> Self {
        BlockLength(16384)
    }

    /// If the block is greater than the max
    #[must_use]
    pub const fn is_greater_than_max(&self) -> bool {
        self.0 > Self::MAX
    }
}

impl fmt::Display for BlockLength {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Identifies part of a piece.
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Block {
    /// The piece's index
    pub index: Index,
    /// The starting byte offset within the piece
    pub begin: BlockBegin,
    /// The length of the block
    pub length: BlockLength,
}

impl From<(Index, BlockBegin, BlockLength)> for Block {
    fn from(value: (Index, BlockBegin, BlockLength)) -> Self {
        Block::new(value.0, value.1, value.2)
    }
}

impl Block {
    /// Instantiates a block.
    #[must_use]
    pub const fn new(index: Index, begin: BlockBegin, length: BlockLength) -> Self {
        Self {
            index,
            begin,
            length,
        }
    }
}

/// Data within a piece.
#[derive(Clone, PartialEq)]
pub struct BlockData {
    /// The piece's index
    pub index: Index,
    /// The starting byte offset within the piece
    pub begin: BlockBegin,
    /// The data starting at the `begin` offset within the piece `index`
    pub data: Bytes,
}

impl From<(Index, BlockBegin, Bytes)> for BlockData {
    fn from(value: (Index, BlockBegin, Bytes)) -> Self {
        BlockData::new(value.0, value.1, value.2)
    }
}

impl BlockData {
    /// Instantiates a block data.
    #[must_use]
    pub const fn new(index: Index, begin: BlockBegin, data: Bytes) -> Self {
        Self { index, begin, data }
    }

    /// Returns a `Block` representation of the data.
    ///
    /// Useful when verifying a `BlockData` response matches a `Block` request.
    ///
    /// # Panics
    ///
    /// Panics if the data's length is greater than a [u32].
    pub fn to_block(&self) -> Block {
        Block {
            index: self.index,
            begin: self.begin,
            length: BlockLength::from(u32::try_from(self.data.len()).unwrap()),
        }
    }
}

impl fmt::Debug for BlockData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BlockData")
            .field("index", &self.index)
            .field("begin", &self.begin)
            .field("data.len", &self.data.len())
            .finish()
    }
}

/// Bitfield has an incorrect length or has bits set beyond the maximum piece index.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[cfg_attr(feature = "std", error("invalid bitfield"))]
pub struct InvalidBitfieldError;

/// Verifies a bitfield has the expected length and has no bits set beyond the maximum piece index.
///
/// # Errors
///
/// Returns an error if the bitfield is not the expected length or if it has
/// bits set beyond the maximum piece index.
///
/// # Panics
///
/// Panics if the expected bitfield length is greater than a [usize].
pub fn verify_bitfield<T: AsRef<[u8]>>(
    max_index: Index,
    bitfield: T,
) -> Result<(), InvalidBitfieldError> {
    let bitfield = bitfield.as_ref();

    let expected_bitfield_len =
        usize::try_from(max_index.0 / 8 + u32::from(max_index.0 % 8 != 0)).unwrap();
    if bitfield.len() != expected_bitfield_len {
        return Err(InvalidBitfieldError);
    }

    let remainder = usize::try_from(max_index.0 % 8).unwrap();
    if remainder != 0 {
        if let Some(last_byte) = bitfield.last() {
            for offset in remainder..8 {
                if (last_byte & 0x80 >> offset) != 0 {
                    return Err(InvalidBitfieldError);
                }
            }
        } else {
            return Err(InvalidBitfieldError);
        }
    }

    Ok(())
}

use bitvec::prelude::*;

/// A set of piece indexes.
///
/// Useful for identifying which pieces are available across all known peers or
/// by a specific peer.
#[derive(Debug, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct IndexBitfield(BitVec<u8, Msb0>);

impl IndexBitfield {
    /// Instantiates an `IndexBitfield` with the maximum piece index.
    ///
    /// # Panics
    ///
    /// Panics if the maximum index is greater than a [usize].
    #[must_use]
    pub fn with_max_index(max_index: Index) -> Self {
        let len = usize::try_from(max_index.0).unwrap();
        Self(bitvec![u8, Msb0; 0; len])
    }

    /// Resizes the `IndexBitfield` for the maximum piece index and sets all values to false.
    ///
    /// # Panics
    ///
    /// Panics if the maximum index is greater than a [usize].
    pub fn clear_with_max_index(&mut self, max_index: Index) {
        self.0.clear();
        self.0.resize(usize::try_from(max_index.0).unwrap(), false);
    }

    /// Sets the `IndexBitfield` with the raw bitfield bytes.
    ///
    /// # Important
    ///
    /// [`verify_bitfield`] should be called to verify the slice is a valid
    /// bitfield before calling this function
    #[must_use]
    pub fn from_slice(bitfield: &[u8]) -> Self {
        Self(BitVec::from_slice(bitfield))
    }

    /// View the underlying bytes of the index set.
    ///
    /// Useful when transmitting the bitfield message.
    #[must_use]
    pub fn as_raw_slice(&self) -> &[u8] {
        self.0.as_raw_slice()
    }

    /// Returns true if the index is set.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than a [usize].
    #[must_use]
    pub fn get(&self, index: Index) -> bool {
        *self.0.get(usize::try_from(index.0).unwrap()).unwrap()
    }

    /// Sets the state for the given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than a [usize].
    pub fn set(&mut self, index: Index, value: bool) {
        *self.0.get_mut(usize::try_from(index.0).unwrap()).unwrap() = value;
    }

    /// If no piece indexes are set.
    #[must_use]
    pub fn not_any(&self) -> bool {
        self.0.not_any()
    }

    /// Returns an iterator for piece indexes which are set.
    ///
    /// # Panics
    ///
    /// Panics if there is a set index in the bitfield where the index is
    /// greater than [u32].
    pub fn iter_set(&self) -> impl Iterator<Item = Index> + '_ {
        self.0
            .iter_ones()
            .map(|index| u32::try_from(index).unwrap())
            .map(Index)
    }

    #[cfg(test)]
    fn iter_not_set(&self) -> impl Iterator<Item = Index> + '_ {
        self.0
            .iter_zeros()
            .map(|index| u32::try_from(index).unwrap())
            .map(Index)
    }

    /// Calculates all of the piece indexes set in this `IndexBitfield` but are not set in the other `IndexBitfield`.
    #[must_use]
    pub fn difference(self, other: IndexBitfield) -> IndexBitfield {
        let orig = self.0;
        let not_other = !other.0;
        IndexBitfield(orig & not_other)
    }

    /// Determines if this `IndexBitfield` is a superset of the other `IndexBitfield`.
    ///
    /// # Panics
    ///
    /// Panics if the other bitfield is not the same length.
    #[must_use]
    pub fn is_superset(&self, other: &IndexBitfield) -> bool {
        assert_eq!(self.0.len(), other.0.len());
        for index in other.0.iter_ones() {
            if !*self.0.get(index).unwrap() {
                return false;
            }
        }
        true
    }

    /// Determines if this `IndexBitfield` is a subset of the other `IndexBitfield`.
    ///
    /// # Panics
    ///
    /// Panics if the other bitfield is not the same length.
    #[must_use]
    pub fn is_subset(&self, other: &IndexBitfield) -> bool {
        assert_eq!(self.0.len(), other.0.len());
        for index in self.0.iter_ones() {
            if !*other.0.get(index).unwrap() {
                return false;
            }
        }
        true
    }
}

/// Sealed trait for unsigned numbers.
///
/// Implemented for unsigned integers.
pub trait UnsignedInt: Sized + sealed::Private {
    /// Increments a number.
    ///
    /// # Panics
    ///
    /// Panics if the result is greater than the max value.
    #[must_use]
    fn inc(&self) -> Self;

    /// Decrements a number.
    ///
    /// # Panics
    ///
    /// Panics if the result is less than 0.
    #[must_use]
    fn dec(&self) -> Self;
}

/// A counted set of piece indexes.
///
/// Useful for keeping track of the number of peers which have a piece.
#[derive(Debug)]
pub struct IndexCountedSet<T>(Vec<T>);

impl<T> IndexCountedSet<T>
where
    T: UnsignedInt,
{
    /// Instantiates an `IndexCountedSet` with the maximum piece index.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than a [usize].
    #[must_use]
    pub fn new(max_index: Index) -> Self
    where
        T: Clone + Default,
    {
        let len = usize::try_from(max_index.0).unwrap();
        Self(vec![T::default(); len])
    }

    /// Increments the count for the given piece index.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than a [usize].
    pub fn inc(&mut self, index: Index)
    where
        T:,
    {
        let index = usize::try_from(index.0).unwrap();
        self.0[index] = self.0[index].inc();
    }

    /// Increments the count for all of the set bits in the given bitfield.
    ///
    /// # Important
    ///
    /// The `IndexBitfield` must represent the same number of pieces as this
    /// `IndexCountedSet.`
    ///
    /// # Panics
    ///
    /// Panics if the count becomes greater than a [u8].
    pub fn inc_bitfield(&mut self, bitfield: &IndexBitfield) {
        debug_assert_eq!(self.0.len(), bitfield.0.len());

        for index in bitfield.0.iter_ones() {
            self.0[index] = self.0[index].inc();
        }
    }

    /// Decrements the count for the given piece index.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than a [usize].
    ///
    /// Also panics if the count becomes less than 0.
    pub fn dec(&mut self, index: Index) {
        let index = usize::try_from(index.0).unwrap();
        self.0[index] = self.0[index].dec();
    }

    /// Decrements the count for all of the set bits in the given bitfield.
    ///
    /// # Important
    ///
    /// The `IndexBitfield` must represent the same number of pieces as this
    /// `IndexCountedSet.`
    ///
    /// # Panics
    ///
    /// Panics if the count becomes less than 0.
    pub fn dec_bitfield(&mut self, bitfield: &IndexBitfield) {
        debug_assert_eq!(self.0.len(), bitfield.0.len());

        for index in bitfield.0.iter_ones() {
            self.0[index] = self.0[index].dec();
        }
    }

    /// Sets the count to 0 for the given piece index.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than a [usize].
    pub fn reset(&mut self, index: Index)
    where
        T: Default,
    {
        let index = usize::try_from(index.0).unwrap();
        self.0[index] = T::default();
    }

    /// Returns the count for the given piece index.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than a [usize].
    pub fn count(&mut self, index: Index) -> T
    where
        T: Copy,
    {
        let index = usize::try_from(index.0).unwrap();
        self.0[index]
    }

    /// Returns an iterator which returns piece indexes with a non-zero count.
    ///
    /// # Panics
    ///
    /// Panics if an index is greater than a [u32].
    pub fn nonzero_iter(&self) -> impl Iterator<Item = Index> + '_
    where
        T: Copy + Default + PartialOrd,
    {
        self.0
            .iter()
            .enumerate()
            .filter(|(_, &req_count)| req_count > T::default())
            .map(|(index, _)| Index::from(u32::try_from(index).unwrap()))
    }
}

mod sealed {
    pub trait Private {}

    macro_rules! unsigned_int_impl {
        ($ty:ty) => {
            impl Private for $ty {}

            impl super::UnsignedInt for $ty {
                fn inc(&self) -> Self {
                    self.checked_add(1).unwrap()
                }

                fn dec(&self) -> Self {
                    self.checked_sub(1).unwrap()
                }
            }
        };
    }

    unsigned_int_impl!(u8);
    unsigned_int_impl!(u16);
    unsigned_int_impl!(u32);
    unsigned_int_impl!(u64);
    unsigned_int_impl!(usize);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_index_set() {
        let max_piece_index = Index(9);
        let mut pieces_set = IndexBitfield::with_max_index(max_piece_index);
        assert_eq!(pieces_set.0.as_raw_slice().len(), 2);

        assert_eq!(pieces_set.as_raw_slice()[0], 0x0);
        assert_eq!(pieces_set.as_raw_slice()[1], 0x0);
        assert_eq!(pieces_set.iter_set().count(), 0);
        assert_eq!(pieces_set.iter_not_set().count(), 9);

        assert!(!pieces_set.get(Index(3)));
        pieces_set.set(Index(3), true);
        assert_eq!(pieces_set.as_raw_slice()[0], 0x10);
        assert_eq!(pieces_set.as_raw_slice()[1], 0x00);
        assert!(pieces_set.get(Index(3)));
        assert_eq!(pieces_set.iter_set().count(), 1);
        assert_eq!(pieces_set.iter_not_set().count(), 8);

        assert!(!pieces_set.get(Index(8)));
        pieces_set.set(Index(8), true);
        assert_eq!(pieces_set.as_raw_slice()[0], 0x10);
        assert_eq!(pieces_set.as_raw_slice()[1], 0x80);
        assert!(pieces_set.get(Index(8)));
        assert_eq!(pieces_set.iter_set().count(), 2);
        assert_eq!(pieces_set.iter_not_set().count(), 7);

        assert!(pieces_set.get(Index(8)));
        pieces_set.set(Index(8), false);
        assert_eq!(pieces_set.as_raw_slice()[0], 0x10);
        assert_eq!(pieces_set.as_raw_slice()[1], 0x00);
        assert!(!pieces_set.get(Index(8)));
        assert_eq!(pieces_set.iter_set().count(), 1);
        assert_eq!(pieces_set.iter_not_set().count(), 8);
    }

    #[test]
    fn test_index_set_is_superset() {
        let mut pieces_set1 = IndexBitfield::with_max_index(Index(9));
        let mut pieces_set2 = IndexBitfield::with_max_index(Index(9));
        assert!(pieces_set1.is_superset(&pieces_set2));
        assert!(pieces_set2.is_superset(&pieces_set1));

        pieces_set1.set(Index(1), true);
        assert!(pieces_set1.is_superset(&pieces_set2));
        assert!(!pieces_set2.is_superset(&pieces_set1));

        pieces_set2.set(Index(1), true);
        assert!(pieces_set1.is_superset(&pieces_set2));
        assert!(pieces_set2.is_superset(&pieces_set1));

        pieces_set1.set(Index(4), true);
        pieces_set1.set(Index(8), true);
        assert!(pieces_set1.is_superset(&pieces_set2));
        assert!(!pieces_set2.is_superset(&pieces_set1));

        pieces_set2.set(Index(4), true);
        assert!(pieces_set1.is_superset(&pieces_set2));
        assert!(!pieces_set2.is_superset(&pieces_set1));

        pieces_set2.set(Index(8), true);
        assert!(pieces_set1.is_superset(&pieces_set2));
        assert!(pieces_set2.is_superset(&pieces_set1));

        pieces_set2.set(Index(7), true);
        assert!(!pieces_set1.is_superset(&pieces_set2));
        assert!(pieces_set2.is_superset(&pieces_set1));

        pieces_set1.set(Index(6), true);
        assert!(!pieces_set1.is_superset(&pieces_set2));
        assert!(!pieces_set2.is_superset(&pieces_set1));
    }

    #[test]
    fn test_index_set_is_subset() {
        let mut pieces_set1 = IndexBitfield::with_max_index(Index(9));
        let mut pieces_set2 = IndexBitfield::with_max_index(Index(9));
        assert!(pieces_set1.is_subset(&pieces_set2));
        assert!(pieces_set2.is_subset(&pieces_set1));

        pieces_set1.set(Index(1), true);
        assert!(!pieces_set1.is_subset(&pieces_set2));
        assert!(pieces_set2.is_subset(&pieces_set1));

        pieces_set2.set(Index(1), true);
        assert!(pieces_set1.is_subset(&pieces_set2));
        assert!(pieces_set2.is_subset(&pieces_set1));

        pieces_set1.set(Index(4), true);
        pieces_set1.set(Index(8), true);
        assert!(!pieces_set1.is_subset(&pieces_set2));
        assert!(pieces_set2.is_subset(&pieces_set1));

        pieces_set2.set(Index(4), true);
        assert!(!pieces_set1.is_subset(&pieces_set2));
        assert!(pieces_set2.is_subset(&pieces_set1));

        pieces_set2.set(Index(8), true);
        assert!(pieces_set1.is_subset(&pieces_set2));
        assert!(pieces_set2.is_subset(&pieces_set1));

        pieces_set2.set(Index(7), true);
        assert!(pieces_set1.is_subset(&pieces_set2));
        assert!(!pieces_set2.is_subset(&pieces_set1));

        pieces_set1.set(Index(6), true);
        assert!(!pieces_set1.is_subset(&pieces_set2));
        assert!(!pieces_set2.is_subset(&pieces_set1));
    }
}
