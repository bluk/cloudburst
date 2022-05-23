// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Lookup table for nodes in the DHT.
//!
//! Routing keeps a table of DHT nodes with their addresses. When a query is
//! sent, the lookup table is used to determined which nodes to send the query to.

use crate::dht::node::Id;
use core::ops::RangeInclusive;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{vec, vec::Vec};
#[cfg(feature = "std")]
use std::{vec, vec::Vec};

/// Information about a node.
pub trait Node {
    /// The node's ID.
    fn id(&self) -> Id;
}

impl<T> Node for &T
where
    T: Node,
{
    fn id(&self) -> Id {
        (*self).id()
    }
}

/// A bucket contains information about [`Node`]s which have an [`Id`] within a specific range.
///
/// Individual nodes should be pinged to ensure the node is still active.
///
/// Buckets may occasionally need to be refreshed if there is no activity for
/// the nodes within the bucket.
#[derive(Debug)]
pub struct Bucket<T, Instant> {
    range: RangeInclusive<Id>,
    nodes: Vec<T>,
    refresh_deadline: Instant,
}

impl<T, Instant> Bucket<T, Instant>
where
    T: Node,
    Instant: crate::time::Instant,
{
    /// Creates a new `Bucket` for nodes which are within the inclusive `Id` range.
    #[must_use]
    #[inline]
    pub const fn new(range: RangeInclusive<Id>, refresh_deadline: Instant) -> Self {
        Bucket {
            range,
            nodes: Vec::new(),
            refresh_deadline,
        }
    }

    /// Returns the bucket's `Id` range.
    #[must_use]
    #[inline]
    pub const fn range(&self) -> &RangeInclusive<Id> {
        &self.range
    }

    /// Returns a random `Id` which would be in the bucket's range.
    ///
    /// # Errors
    ///
    /// Returns a [`rand::Error`] if the random number generator cannot generate a random `Id`.
    #[must_use]
    #[inline]
    pub fn rand_id<R>(&self, rng: &mut R) -> Id
    where
        R: rand::RngCore,
    {
        internal::rand_in_inclusive_range(&self.range, rng)
    }

    /// Returns the deadline which a `Node` from within the bucket's range should be pinged or found.
    #[must_use]
    #[inline]
    pub const fn refresh_deadline(&self) -> &Instant {
        &self.refresh_deadline
    }

    /// Updates the refresh deadline.
    #[inline]
    pub fn set_refresh_deadline(&mut self, refresh_deadline: Instant) {
        self.refresh_deadline = refresh_deadline;
    }

    /// Returns the number of nodes in the bucket.
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns `true` if the bucket is empty.
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns an `Iterator` for the nodes.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &'_ T> {
        self.nodes.iter()
    }

    /// Returns an `Iterator` for the nodes.
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &'_ mut T> {
        self.nodes.iter_mut()
    }

    /// Called to insert a node into the bucket.
    ///
    /// # Panics
    ///
    /// Panics if the node's ID is not in the bucket's ID range.
    #[inline]
    pub fn insert(&mut self, node: T) {
        assert!(self.range.contains(&node.id()));
        self.nodes.push(node);
    }

    /// Removes all nodes.
    #[inline]
    pub fn clear(&mut self) {
        self.nodes.clear();
    }

    /// Retains nodes specified by the predicate.
    ///
    /// See [`Vec::retain()`].
    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.nodes.retain(f);
    }

    /// Splits a bucket into two by dividing using the middle of the `Id` range.
    ///
    /// The `Node`s previously stored in this `Bucket` may not be evenly split
    /// between the two new buckets because their `Id`s may be unevenly
    /// distributed between the two new `Id` ranges.
    ///
    /// # Panics
    ///
    /// Panics if the bucket range cannot be split (e.g. the range of the bucket
    /// includes only one ID).
    #[must_use]
    pub fn split(self) -> (Bucket<T, Instant>, Bucket<T, Instant>) {
        let Bucket {
            mut nodes,
            refresh_deadline,
            range,
        } = self;

        let middle = internal::middle(*range.end(), *range.start());
        assert_ne!(*range.start(), *range.end(), "cannot split bucket");
        let lower_bucket_range = *range.start()..=middle;
        let upper_bucket_range = internal::next(middle)..=*range.end();
        debug_assert!(*lower_bucket_range.start() <= *lower_bucket_range.end());
        debug_assert!(*upper_bucket_range.start() <= *upper_bucket_range.end());

        let mut upper_bucket_nodes = Vec::default();

        let mut index = 0;
        while index < nodes.len() {
            if upper_bucket_range.contains(&nodes[index].id()) {
                upper_bucket_nodes.push(nodes.remove(index));
            } else {
                index += 1;
            }
        }

        let lower_bucket = Bucket {
            range: lower_bucket_range,
            nodes,
            refresh_deadline: refresh_deadline.clone(),
        };
        let upper_bucket = Bucket {
            range: upper_bucket_range,
            nodes: upper_bucket_nodes,
            refresh_deadline,
        };

        (lower_bucket, upper_bucket)
    }
}

mod internal {

    use crate::dht::node::Id;

    #[must_use]
    pub(super) fn rand_in_inclusive_range<R>(
        range: &core::ops::RangeInclusive<Id>,
        rng: &mut R,
    ) -> Id
    where
        R: rand::Rng,
    {
        #[must_use]
        #[inline]
        fn difference(first: Id, second: Id) -> Id {
            let bigger: [u8; 20];
            let mut smaller: [u8; 20];
            if first < second {
                bigger = second.0;
                smaller = first.0;
            } else {
                bigger = first.0;
                smaller = second.0;
            }
            smaller = twos_complement(smaller);
            let (bigger, _) = overflowing_add(bigger, &smaller);
            Id::new(bigger)
        }

        let data_bit_diff = difference(*range.end(), *range.start());

        let rand_bits: [u8; 20] = randomize_up_to(<[u8; 20]>::from(data_bit_diff), rng);
        let (rand_bits, _) = overflowing_add(rand_bits, &<[u8; 20]>::from(*range.start()));
        Id::from(rand_bits)
    }

    /// Finds the middle id between this node ID and the node ID argument.
    #[must_use]
    #[inline]
    pub(super) const fn middle(first: Id, second: Id) -> Id {
        let data = first.0;
        let (data, overflow) = overflowing_add(data, &second.0);
        let mut data = shift_right(data);
        if overflow {
            data[0] |= 0x80;
        }
        Id::new(data)
    }

    // #[inline]
    // #[must_use]
    // pub(super) const fn prev(id: Id) -> Id {
    //     let id_bytes = id.0;
    //     let mut data: [u8; 20] = [0; 20];
    //     let offset_from_end;

    //     let mut idx = 19;
    //     loop {
    //         if id_bytes[idx] != 0 {
    //             offset_from_end = idx;
    //             break;
    //         }
    //         if idx == 0 {
    //             offset_from_end = 0;
    //             break;
    //         }
    //         idx -= 1;
    //     }

    //     let mut idx = 0;
    //     loop {
    //         data[idx] = id_bytes[idx];
    //         if idx == offset_from_end {
    //             break;
    //         }
    //         idx += 1;
    //     }

    //     data[offset_from_end] = if id_bytes[offset_from_end] == 0 {
    //         0xff
    //     } else {
    //         id_bytes[offset_from_end] - 1
    //     };

    //     let mut idx = offset_from_end + 2;
    //     loop {
    //         if idx >= 20 {
    //             break;
    //         }
    //         data[idx] = 0xff;
    //         idx += 1;
    //     }

    //     Id::new(data)
    // }

    #[must_use]
    #[inline]
    pub(super) const fn next(id: Id) -> Id {
        let (data, overflowing) = overflowing_add(
            id.0,
            &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        );
        assert!(!overflowing);

        Id::new(data)
    }

    #[must_use]
    #[inline]
    const fn overflowing_add(mut value: [u8; 20], other: &[u8; 20]) -> ([u8; 20], bool) {
        let mut carry_over: u8 = 0;

        let mut idx = 19;
        loop {
            let (partial_val, overflow) = value[idx].overflowing_add(other[idx]);
            let (final_val, carry_over_overflow) = partial_val.overflowing_add(carry_over);
            value[idx] = final_val;
            carry_over = if carry_over_overflow || overflow {
                1
            } else {
                0
            };
            if idx == 0 {
                break;
            }
            idx -= 1;
        }

        (value, carry_over == 1)
    }

    #[must_use]
    #[inline]
    const fn twos_complement(mut value: [u8; 20]) -> [u8; 20] {
        let mut idx = 0;
        loop {
            value[idx] = !(value[idx]);
            if idx == 19 {
                break;
            }
            idx += 1;
        }
        let one_bit = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let (value, _) = overflowing_add(value, &one_bit);
        value
    }

    #[inline]
    #[must_use]
    const fn shift_right(mut value: [u8; 20]) -> [u8; 20] {
        let mut add_high_bit = false;
        let mut idx = 0;
        loop {
            let is_lower_bit_set = (value[idx] & 0x01) == 1;
            value[idx] >>= 1;
            if add_high_bit {
                value[idx] |= 0x80;
            }
            add_high_bit = is_lower_bit_set;
            if idx == 19 {
                break;
            }
            idx += 1;
        }
        value
    }

    /// An inclusive randomize up to.
    #[must_use]
    fn randomize_up_to<R>(end: [u8; 20], rng: &mut R) -> [u8; 20]
    where
        R: rand::Rng,
    {
        let mut data = [0; 20];
        let mut lower_than_max = false;

        for idx in 0..data.len() {
            data[idx] = if lower_than_max {
                rng.gen()
            } else {
                let idx_val = end[idx];
                let val = rng.gen_range(0..=idx_val);
                if val < idx_val {
                    lower_than_max = true;
                }
                val
            };
        }

        data
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[cfg(all(feature = "alloc", not(feature = "std")))]
        use alloc::{format, vec};
        #[cfg(feature = "std")]
        use std::{format, vec};

        #[test]
        fn test_debug() {
            let node_id = Id::max();
            let debug_str = format!("{:?}", node_id);
            assert_eq!(debug_str, "Id(FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)");
        }

        #[test]
        fn test_overflowing_add() {
            let bytes: [u8; 20] = [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
            ];
            let (bytes, overflow) = overflowing_add(
                bytes,
                &[
                    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
                ],
            );
            assert!(!overflow);
            assert_eq!(
                bytes,
                [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39,]
            );
        }

        #[test]
        fn test_twos_complement() {
            let mut bytes: [u8; 20] = [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
            ];
            bytes = twos_complement(bytes);
            assert_eq!(
                bytes,
                [
                    255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240,
                    239, 238, 237, 237
                ]
            );
        }

        #[test]
        fn test_shift_right() {
            let bytes: [u8; 20] = [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
            ];
            let bytes = shift_right(bytes);
            assert_eq!(
                bytes,
                [0, 0, 129, 1, 130, 2, 131, 3, 132, 4, 133, 5, 134, 6, 135, 7, 136, 8, 137, 9]
            );
        }

        #[test]
        fn test_id_ord() {
            let mut node_ids = vec![
                Id::from([0xff; 20]),
                Id::from([0x00; 20]),
                middle(Id::from([0xff; 20]), Id::from([0x00; 20])),
            ];
            node_ids.sort();
            assert_eq!(
                node_ids,
                vec![
                    Id::from([0x00; 20]),
                    middle(Id::from([0xff; 20]), Id::from([0x00; 20])),
                    Id::from([0xff; 20]),
                ]
            );
        }

        #[test]
        fn test_id_distance_ord() {
            let mut node_ids = vec![
                Id::from([0x00; 20]),
                middle(Id::from([0xff; 20]), Id::from([0x00; 20])),
                Id::from([0xff; 20]),
            ];
            let pivot_id = middle(Id::from([0xef; 20]), Id::from([0x00; 20]));
            node_ids.sort_by_key(|a| a.distance(pivot_id));
            assert_eq!(
                node_ids,
                vec![
                    middle(Id::from([0xff; 20]), Id::from([0x00; 20])),
                    Id::from([0x00; 20]),
                    Id::from([0xff; 20]),
                ]
            );
        }
    }
}

/// A routing table based around a pivot `Id`.
///
/// More data for nodes which are "closer" to the pivot is stored compared to
/// data which is "farther" from the pivot `Id`.
#[derive(Debug)]
pub struct Table<T, Instant> {
    pivot: Id,
    buckets: Vec<Bucket<T, Instant>>,
}

impl<T, Instant> Table<T, Instant>
where
    T: Node,
    Instant: crate::time::Instant,
{
    /// Creates a new table based on the given pivot.
    ///
    /// The `refresh_deadline` is the `Instant` which the initial bucket(s) should be refreshed at.
    #[must_use]
    #[inline]
    pub fn new(pivot: Id, refresh_deadline: Instant) -> Self {
        Self {
            pivot,
            buckets: vec![Bucket::new(Id::min()..=Id::max(), refresh_deadline)],
        }
    }

    /// Returns the local ID which serves as the pivot around which the table is
    /// based on.
    ///
    /// More nodes which have an `Id` closer to the pivot `Id` are kept in the
    /// routing table compared to nodes which have an `Id` further away.
    #[must_use]
    #[inline]
    pub const fn pivot(&self) -> Id {
        self.pivot
    }

    /// Returns the number of nodes stored in the table.
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.buckets.iter().map(Bucket::len).sum()
    }

    /// Returns if there are no nodes in the table.
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an `Iterator` for the buckets.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &'_ Bucket<T, Instant>> {
        self.buckets.iter()
    }

    /// Returns an `Iterator` for the buckets.
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &'_ mut Bucket<T, Instant>> {
        self.buckets.iter_mut()
    }

    /// Finds the bucket which has the range containing the `id` argument.
    #[must_use]
    #[inline]
    pub fn find(&self, id: &Id) -> &Bucket<T, Instant> {
        self.buckets
            .iter()
            .find(|b| b.range.contains(id))
            .expect("bucket should exist")
    }

    /// Finds the bucket which has the range containing the `id` argument.
    #[must_use]
    #[inline]
    pub fn find_mut(&mut self, id: &Id) -> &mut Bucket<T, Instant> {
        self.buckets
            .iter_mut()
            .find(|b| b.range.contains(id))
            .expect("bucket should exist")
    }

    /// Finds a bucket which needs to be refreshed.
    ///
    /// A bucket is refreshed by attempting to find a random node `Id` in the
    /// bucket. See [`Bucket::rand_id()`] to find a random ID.
    ///
    /// Set the new refresh deadline by calling [`Bucket::set_refresh_deadline()`].
    #[must_use]
    #[inline]
    pub fn find_bucket_to_refresh(&mut self, now: &Instant) -> Option<&mut Bucket<T, Instant>> {
        self.buckets
            .iter_mut()
            .find(|b| *b.refresh_deadline() <= *now)
    }

    /// Splits the last bucket in half.
    ///
    /// The last bucket always contains the range which includes the pivot ID.
    pub fn split_last(&mut self) {
        let bucket = self.buckets.pop().expect("bucket should exist");
        debug_assert!(bucket.range.contains(&self.pivot));
        let (lower_bucket, upper_bucket) = bucket.split();
        if lower_bucket.range.contains(&self.pivot) {
            self.buckets.push(upper_bucket);
            self.buckets.push(lower_bucket);
        } else {
            self.buckets.push(lower_bucket);
            self.buckets.push(upper_bucket);
        }
        debug_assert!(self
            .buckets
            .last()
            .expect("bucket should exist")
            .range
            .contains(&self.pivot));
    }
}

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    struct MyNode {
        id: Id,
    }

    impl Node for MyNode {
        fn id(&self) -> Id {
            self.id
        }
    }

    #[test]
    fn test_split_bucket() {
        let now = std::time::Instant::now();
        let bucket: Bucket<MyNode, _> = Bucket::new(Id::min()..=Id::max(), now);
        let (first_bucket, second_bucket) = bucket.split();
        assert_eq!(
            first_bucket.range,
            Id::min()
                ..=Id::from([
                    0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
                ])
        );
        assert_eq!(
            second_bucket.range,
            Id::from([
                0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ])..=Id::max()
        );
    }

    #[test]
    fn test_split_range_three() {
        let now = std::time::Instant::now();
        let min_id = Id::min();
        let max_id = Id::from([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
        ]);
        let bucket: Bucket<MyNode, _> = Bucket::new(min_id..=max_id, now);
        let (first_bucket, second_bucket) = bucket.split();
        assert_eq!(
            first_bucket.range,
            Id::from([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ])
                ..=Id::from([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
                ])
        );
        assert_eq!(
            second_bucket.range,
            Id::from([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
            ])
                ..=Id::from([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
                ])
        );
    }

    #[test]
    fn test_split_range_two() {
        let now = std::time::Instant::now();
        let min_id = Id::from([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        ]);
        let max_id = Id::from([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
        ]);
        let bucket: Bucket<MyNode, _> = Bucket::new(min_id..=max_id, now);
        let (first_bucket, second_bucket) = bucket.split();
        assert_eq!(
            first_bucket.range,
            Id::from([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
            ])
                ..=Id::from([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
                ])
        );
        assert_eq!(
            second_bucket.range,
            Id::from([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
            ])
                ..=Id::from([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
                ])
        );
    }

    #[test]
    fn test_split_range_two_min() {
        let now = std::time::Instant::now();
        let min_id = Id::min();
        let max_id = Id::from([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        ]);
        let bucket: Bucket<MyNode, _> = Bucket::new(min_id..=max_id, now);
        let (first_bucket, second_bucket) = bucket.split();
        assert_eq!(first_bucket.range, Id::min()..=Id::min());
        assert_eq!(
            second_bucket.range,
            Id::from([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
            ])
                ..=Id::from([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
                ])
        );
    }

    #[test]
    fn test_split_range_two_max() {
        let now = std::time::Instant::now();
        let min_id = Id::from([
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
        ]);
        let max_id = Id::max();
        let bucket: Bucket<MyNode, _> = Bucket::new(min_id..=max_id, now);
        let (first_bucket, second_bucket) = bucket.split();
        assert_eq!(
            first_bucket.range,
            Id::from([
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
            ])
                ..=Id::from([
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
                ])
        );
        assert_eq!(
            second_bucket.range,
            Id::from([
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            ])..=Id::max()
        );
    }

    #[test]
    #[should_panic(expected = "cannot split bucket")]
    fn test_split_range_one() {
        let now = std::time::Instant::now();
        let min_id = Id::from([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        ]);
        let max_id = Id::from([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        ]);
        let bucket: Bucket<MyNode, _> = Bucket::new(min_id..=max_id, now);
        let (_, _) = bucket.split();
    }

    #[test]
    #[should_panic(expected = "cannot split bucket")]
    fn test_split_range_one_min() {
        let now = std::time::Instant::now();
        let bucket: Bucket<MyNode, _> = Bucket::new(Id::min()..=Id::min(), now);
        let (_, _) = bucket.split();
    }

    #[test]
    #[should_panic(expected = "cannot split bucket")]
    fn test_split_range_one_max() {
        let now = std::time::Instant::now();
        let bucket: Bucket<MyNode, _> = Bucket::new(Id::max()..=Id::max(), now);
        let (_, _) = bucket.split();
    }
}
