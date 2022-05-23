// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Transactions correlate a KRPC query with its response.

use core::convert::TryFrom;

use crate::dht::{
    krpc::RespMsg,
    node::{self, AddrOptId, LocalId},
};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;
use bt_bencode::Value;
#[cfg(feature = "std")]
use std::vec::Vec;

use super::ErrorMsg;

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

/// A local transaction.
#[derive(Debug)]
pub struct Transaction<Addr, TxId, Instant> {
    /// Returns the address which the message was sent to.
    addr_opt_id: AddrOptId<Addr>,
    /// The local transaction ID.
    tx_id: TxId,
    /// The deadline when the transaction is considered to have timed out
    timeout_deadline: Instant,
}

#[cfg(feature = "std")]
impl<Addr, TxId, Instant> std::hash::Hash for Transaction<Addr, TxId, Instant>
where
    TxId: std::hash::Hash,
    Addr: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.tx_id.hash(state);
        self.addr_opt_id.hash(state);
    }
}

impl<Addr, TxId, Instant> Transaction<Addr, TxId, Instant> {
    /// Instantiates a new `Transaction`.
    #[must_use]
    #[inline]
    pub const fn new(addr_opt_id: AddrOptId<Addr>, tx_id: TxId, timeout_deadline: Instant) -> Self {
        Self {
            addr_opt_id,
            tx_id,
            timeout_deadline,
        }
    }

    /// Returns the address associated with the transaction.
    #[must_use]
    #[inline]
    pub const fn addr_opt_id(&self) -> &AddrOptId<Addr> {
        &self.addr_opt_id
    }

    /// Returns the transaction ID associated with the transaction.
    #[must_use]
    #[inline]
    pub const fn tx_id(&self) -> &TxId {
        &self.tx_id
    }

    /// Returns the timeout deadline.
    #[must_use]
    #[inline]
    pub const fn timeout_deadline(&self) -> &Instant {
        &self.timeout_deadline
    }
}

/// Errors when processing a transaction.
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[cfg_attr(feature = "std", error(transparent))]
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl Error {
    #[must_use]
    #[inline]
    const fn unknown_tx() -> Self {
        Self {
            kind: ErrorKind::UnknownTx,
        }
    }

    /// If the message does not match an existing transaction.
    #[must_use]
    #[inline]
    pub const fn is_unknown_tx(&self) -> bool {
        matches!(self.kind, ErrorKind::UnknownTx)
    }

    #[must_use]
    #[inline]
    const fn invalid_queried_node_id() -> Self {
        Self {
            kind: ErrorKind::InvalidQueriedNodeId,
        }
    }

    /// If the message has an invalid queried node ID.
    #[must_use]
    #[inline]
    pub const fn is_invalid_queried_node_id(&self) -> bool {
        matches!(self.kind, ErrorKind::InvalidQueriedNodeId)
    }
}

#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[derive(Debug)]
enum ErrorKind {
    #[cfg_attr(feature = "std", error("unknown transaction"))]
    UnknownTx,
    #[cfg_attr(feature = "std", error("invalid input"))]
    InvalidQueriedNodeId,
}

/// A deserialized message event with the relevant node information and local
/// transaction identifier.
#[derive(Clone, Debug)]
pub struct ReadEvent<Addr, TxId> {
    addr_opt_id: AddrOptId<Addr>,
    tx_id: Option<TxId>,
    msg: Value,
}

impl<Addr, TxId> ReadEvent<Addr, TxId> {
    /// Returns the relevant node's network address and optional Id.
    #[must_use]
    #[inline]
    pub const fn addr_opt_id(&self) -> &AddrOptId<Addr> {
        &self.addr_opt_id
    }

    /// Returns the relevant local transaction Id if the event is related to a query sent by the local node.
    #[must_use]
    #[inline]
    pub const fn tx_id(&self) -> Option<&TxId> {
        self.tx_id.as_ref()
    }

    /// Returns the message which may contain a query, response, or error.
    #[must_use]
    #[inline]
    pub const fn msg(&self) -> &Value {
        &self.msg
    }
}

/// A collection of local transactions.
#[derive(Debug)]
pub struct Transactions<Addr, TxId, Instant> {
    txs: Vec<Transaction<Addr, TxId, Instant>>,
}

impl<Addr, TxId, Instant> Default for Transactions<Addr, TxId, Instant> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Addr, TxId, Instant> Transactions<Addr, TxId, Instant> {
    /// Instantiates a new instance.
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        Self { txs: Vec::new() }
    }

    /// Inserts a transaction into the collection.
    ///
    /// # Panics
    ///
    /// Panics if the transaction ID matches an existing transaction ID.
    #[inline]
    pub fn insert(&mut self, tx: Transaction<Addr, TxId, Instant>)
    where
        TxId: PartialEq,
    {
        assert!(!self.contains(&tx.tx_id));
        self.txs.push(tx);
    }

    /// Removes a transaction given a transaction ID.
    ///
    /// Returns the transaction if a matching transaction is found. Returns
    /// `None` if there is no matching transaction.
    #[inline]
    pub fn remove(&mut self, tx_id: &TxId) -> Option<Transaction<Addr, TxId, Instant>>
    where
        TxId: PartialEq,
    {
        self.txs
            .iter()
            .position(|t| t.tx_id == *tx_id)
            .map(|index| self.txs.remove(index))
    }

    /// Returns true if there is a transaction which has the given transaction ID .
    #[must_use]
    #[inline]
    pub fn contains(&self, tx_id: &TxId) -> bool
    where
        TxId: PartialEq,
    {
        self.txs.iter().any(|tx| tx.tx_id == *tx_id)
    }

    /// The number of transactions.
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.txs.len()
    }

    /// Returns true if the collection is empty.
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.txs.is_empty()
    }

    /// Returns the minimum timeout deadline of all the transactions in the collection.
    ///
    /// Returns `None` if there are no transactions.
    #[must_use]
    #[inline]
    pub fn timeout(&self) -> Option<Instant>
    where
        Instant: crate::time::Instant,
    {
        self.txs.iter().map(|t| &t.timeout_deadline).min().cloned()
    }

    /// Finds and removes a transaction which has timed out.
    #[inline]
    pub fn pop_timed_out_tx(&mut self, now: &Instant) -> Option<Transaction<Addr, TxId, Instant>>
    where
        Instant: crate::time::Instant,
    {
        if let Some(pos) = self.txs.iter().position(|tx| tx.timeout_deadline <= *now) {
            return Some(self.txs.remove(pos));
        }

        None
    }

    /// Proceses a received response message.
    ///
    /// `msg` is the received response message.
    ///
    /// When `is_queried_node_id_strictly_checked` is set to `true`, the method
    /// will only consider response messages valid if the `queried_node_id`
    /// matches what the expected node ID belonging to the queried node. If the
    /// value is set to `false`, either the expected node ID belonging to the
    /// queried node or the local node's ID are considered valid.
    ///
    /// `local_id` is the local node's ID. It is used to check the
    /// `queried_node_id` in response messages if
    /// `is_queried_node_id_strictly_checked` is `false`.
    ///
    /// # Errors
    ///
    /// Errors are returned if the message is invalid input or is missing a
    /// required transaction.
    ///
    /// # Important
    ///
    /// If the return result is `Ok`, then any associated transaction is
    /// removed.
    ///
    /// If an error is returned, any associated transaction is not removed. If
    /// the transaction should be removed in an error case, call the
    /// [`Transactions::remove()`] method.
    pub fn on_recv_resp(
        &mut self,
        msg: &dyn RespMsg,
        is_queried_node_id_strictly_checked: bool,
        local_id: LocalId,
    ) -> Result<Transaction<Addr, TxId, Instant>, Error>
    where
        Addr: PartialEq,
        TxId: PartialEq + for<'a> TryFrom<&'a [u8]>,
    {
        if let Some(tx) = msg
            .tx_id()
            .and_then(|tx_id| TxId::try_from(tx_id).ok())
            .and_then(|tx_id| self.remove(&tx_id))
        {
            let queried_node_id = RespMsg::queried_node_id(msg);
            let is_response_queried_id_valid =
                tx.addr_opt_id().id().map_or(true, |expected_node_id| {
                    queried_node_id == Some(expected_node_id)
                });
            if is_response_queried_id_valid
                || (!is_queried_node_id_strictly_checked
                    && queried_node_id == Some(node::Id::from(local_id)))
            {
                Ok(tx)
            } else {
                // re-insert the transaction
                self.insert(tx);
                Err(Error::invalid_queried_node_id())
            }
        } else {
            Err(Error::unknown_tx())
        }
    }

    /// Proceses a received error message.
    ///
    /// `msg` is the received error message.
    ///
    /// # Errors
    ///
    /// Errors are returned if there is no associated transaction found.
    pub fn on_recv_error(
        &mut self,
        msg: &dyn ErrorMsg,
    ) -> Result<Transaction<Addr, TxId, Instant>, Error>
    where
        Addr: PartialEq,
        TxId: PartialEq + for<'a> TryFrom<&'a [u8]>,
    {
        msg.tx_id()
            .and_then(|tx_id| TxId::try_from(tx_id).ok())
            .and_then(|tx_id| self.remove(&tx_id))
            .ok_or_else(Error::unknown_tx)
    }
}
