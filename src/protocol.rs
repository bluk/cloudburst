// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Protocol messages sent from peer to peer.
//!
//! [Frame] enumerates the various known messages.

use bytes::Buf;
use core::{borrow::Borrow, fmt};

use crate::{
    metainfo::InfoHash,
    peer::{self, Id, InvalidInput},
    piece::{Block, BlockBegin, BlockData, BlockLength, Index},
};

/// The initial protocol handshake string.
pub const PROTOCOL_STRING_BYTES: [u8; 20] = *b"\x13BitTorrent protocol";

/// The reserved bytes in the handshake.
#[derive(Default, Clone, Copy, PartialEq, Eq)]
pub struct ReservedBytes(pub [u8; 8]);

impl AsRef<[u8]> for ReservedBytes {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Borrow<[u8]> for ReservedBytes {
    fn borrow(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 8]> for ReservedBytes {
    fn from(other: [u8; 8]) -> Self {
        Self(other)
    }
}

impl From<&[u8; 8]> for ReservedBytes {
    fn from(other: &[u8; 8]) -> Self {
        Self(*other)
    }
}

fmt_byte_array!(ReservedBytes);

/// Message frame.
///
/// An individual message.
#[derive(Debug, PartialEq, Eq)]
pub enum Frame<'a> {
    /// Keep alive message
    ///
    /// Keeps the connection alive.
    ///
    /// Should be sent after a period of time has elapsed when no messages have
    /// been sent.
    ///
    /// When received, the connection should reset when the last message was sent.
    /// If no messages are received after a period of time, the connection
    /// should be closed.
    KeepAlive,
    /// Choke message
    ///
    /// Indicates the peer will not fulfill any requests.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * If the local peer will no longer fulfill requests.
    /// * Usually sent if the local peer changes which peers are choked and not
    /// choked based on which peer has sent more verified pieces.
    Choke,
    /// Unchoke message
    ///
    /// Indicates the peer will fulfill any requests.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * If the local peer will fulfill requests.
    /// * Usually sent if the local peer changes which peers are choked and not
    /// choked based on which peer has sent more verified pieces.
    /// * May be sent if the local peer is trying to find a peer which can send
    /// more piece data efficiently
    Unchoke,
    /// Interested message
    ///
    /// Indicates the remote peer has data which the local peer wants.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * After a remote peer's [BitfieldMsg] message is
    /// received and the remote peer has pieces which the local peer does not
    /// have.
    /// * After a remote peer's [HaveMsg] message is received and the
    /// [HaveMsg]'s piece index is a piece which the local peer does not have.
    Interested,
    /// Not interested message
    ///
    /// Indicates the remote peer does not have data which the local peer wants.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * After a local peer has a new piece, the local peer should check each
    /// remote peer to see if the remote peer is still interesting. If not
    /// interesting, the not interested message should be sent.
    NotInterested,
    /// Have piece index message
    ///
    /// Indicates the peer has a piece of data.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * After a local peer has a new piece, the local peer should check each
    /// remote peer to if they have the piece. If the remote peer does not have the piece,
    /// the have message should be sent.
    Have(HaveMsg),
    /// Have piece index bitfield message
    ///
    /// Indicates the peer has pieces of data.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * Must only be sent as the first message after the handshake.
    /// * Should only be sent if the local peer has any pieces.
    Bitfield(BitfieldMsg<'a>),
    /// Request block message
    ///
    /// Indicates the peer wants a block of data.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * Must only be sent when unchoked by the remote peer
    /// * Must only be sent when interested in the remote peer
    /// * Usually sent if the local peer wants a piece of data
    Request(RequestMsg),
    /// Fulfill block message
    ///
    /// Fulfills a previous request from a peer.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * Must only be sent if a request has been previously received for the data.
    Piece(PieceMsg<'a>),
    /// Cancel block request message
    ///
    /// Indicates the peer no longer wants a block of data.
    ///
    /// Should be sent at least in the following situations:
    ///
    /// * Must only be sent when unchoked by the remote peer
    /// * Must only be sent when interested in the remote peer
    /// * Must only be sent if a previous request was sent for the same data.
    /// * Usually sent if the local peer no longer wants a piece of data
    Cancel(CancelMsg),
    /// An unknown message with the message type byte and the message data
    Unknown(u8, &'a [u8]),
}

/// Protocol error.
///
/// Errors returned when parsing or checking a frame.
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[derive(Debug)]
pub enum Error {
    /// An incomplete frame
    #[cfg_attr(feature = "std", error("incomplete frame"))]
    IncompleteFrame,
    /// Message length is too large
    #[cfg_attr(feature = "std", error("message length too large {0}"))]
    MessageLengthTooLarge(usize),
    /// Invalid message length
    #[cfg_attr(feature = "std", error("invalid message length"))]
    InvalidMessageLength,
}

#[cfg(feature = "std")]
impl From<Error> for std::io::Error {
    fn from(error: Error) -> Self {
        std::io::Error::new(std::io::ErrorKind::InvalidInput, error)
    }
}

/// The expected maximum length of a message to be sent.
pub const MAX_EXPECTED_FRAME_LEN: usize = 1 + 4 + 4 + 16384;

impl<'a> Frame<'a> {
    /// Checks the buffer to verify the buffer contains a complete valid frame.
    ///
    /// # Errors
    ///
    /// Errors if the message frame is incomplete or if the message length is
    /// larger than an expected size.
    ///
    /// # Panics
    ///
    /// Panics if the message length cannot be converted into a [usize].
    #[cfg(feature = "std")]
    pub fn check<T: AsRef<[u8]>>(cursor: &mut std::io::Cursor<T>) -> Result<(), Error> {
        if cursor.remaining() < 4 {
            return Err(Error::IncompleteFrame);
        }

        let msg_len = cursor.get_u32();
        if msg_len == 0 {
            return Ok(());
        }

        let msg_len = usize::try_from(msg_len).unwrap();
        if msg_len > MAX_EXPECTED_FRAME_LEN {
            return Err(Error::MessageLengthTooLarge(msg_len));
        }
        if cursor.remaining() < msg_len {
            return Err(Error::IncompleteFrame);
        }

        let ty = cursor.get_u8();
        match ty {
            ChokeMsg::TYPE => {
                if msg_len != ChokeMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                Ok(())
            }
            UnchokeMsg::TYPE => {
                if msg_len != UnchokeMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                Ok(())
            }
            InterestedMsg::TYPE => {
                if msg_len != InterestedMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                Ok(())
            }
            NotInterestedMsg::TYPE => {
                if msg_len != NotInterestedMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                Ok(())
            }
            HaveMsg::TYPE => {
                if msg_len != HaveMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                cursor.advance(4);
                Ok(())
            }
            RequestMsg::TYPE => {
                if msg_len != RequestMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                cursor.advance(12);
                Ok(())
            }
            CancelMsg::TYPE => {
                if msg_len != CancelMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                cursor.advance(12);
                Ok(())
            }
            // BitfieldMsg::TYPE | PieceMsg::TYPE |
            _ => {
                cursor.advance(msg_len - 1);
                Ok(())
            }
        }
    }

    /// Parses the next frame.
    ///
    /// # Errors
    ///
    /// Errors if the message frame is incomplete or if the message length is
    /// larger than an expected size.
    ///
    /// # Panics
    ///
    /// Panics if the message length cannot be converted into a [usize].
    pub fn parse(buf: &'a [u8]) -> Result<Self, Error> {
        if buf.remaining() < 4 {
            return Err(Error::IncompleteFrame);
        }

        let msg_len = u32::from_be_bytes(<[u8; 4]>::try_from(&buf[..4]).unwrap());
        if msg_len == 0 {
            return Ok(Self::KeepAlive);
        }

        let msg_len = usize::try_from(msg_len).unwrap();
        if msg_len > MAX_EXPECTED_FRAME_LEN {
            return Err(Error::MessageLengthTooLarge(msg_len));
        }

        let buf = &buf[4..];
        if buf.remaining() < msg_len {
            return Err(Error::IncompleteFrame);
        }

        let ty = buf[0];
        match ty {
            ChokeMsg::TYPE => {
                if msg_len != ChokeMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                Ok(Self::Choke)
            }
            UnchokeMsg::TYPE => {
                if msg_len != UnchokeMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                Ok(Self::Unchoke)
            }
            InterestedMsg::TYPE => {
                if msg_len != InterestedMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                Ok(Self::Interested)
            }
            NotInterestedMsg::TYPE => {
                if msg_len != NotInterestedMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                Ok(Self::NotInterested)
            }
            HaveMsg::TYPE => {
                if msg_len != HaveMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                let index =
                    Index::from(u32::from_be_bytes(<[u8; 4]>::try_from(&buf[1..5]).unwrap()));
                Ok(Self::Have(HaveMsg(index)))
            }
            BitfieldMsg::TYPE => {
                todo!()
                // let bitfield = buf.split_to(msg_len - 1);
                // Ok(Self::Bitfield(BitfieldMsg(bitfield.freeze())))
            }
            RequestMsg::TYPE => {
                if msg_len != RequestMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                let index =
                    Index::from(u32::from_be_bytes(<[u8; 4]>::try_from(&buf[1..5]).unwrap()));
                let begin =
                    BlockBegin::from(u32::from_be_bytes(<[u8; 4]>::try_from(&buf[5..9]).unwrap()));
                let length = BlockLength::from(u32::from_be_bytes(
                    <[u8; 4]>::try_from(&buf[9..13]).unwrap(),
                ));
                Ok(Self::Request(RequestMsg(Block {
                    index,
                    begin,
                    length,
                })))
            }
            PieceMsg::TYPE => {
                let index =
                    Index::from(u32::from_be_bytes(<[u8; 4]>::try_from(&buf[1..5]).unwrap()));
                let begin =
                    BlockBegin::from(u32::from_be_bytes(<[u8; 4]>::try_from(&buf[5..9]).unwrap()));
                let length = msg_len - 1 - 4 - 4;
                let data = &buf[9..9 + length];
                Ok(Self::Piece(PieceMsg(BlockData { index, begin, data })))
            }
            CancelMsg::TYPE => {
                if msg_len != CancelMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                let index =
                    Index::from(u32::from_be_bytes(<[u8; 4]>::try_from(&buf[1..5]).unwrap()));
                let begin =
                    BlockBegin::from(u32::from_be_bytes(<[u8; 4]>::try_from(&buf[5..9]).unwrap()));
                let length = BlockLength::from(u32::from_be_bytes(
                    <[u8; 4]>::try_from(&buf[9..13]).unwrap(),
                ));
                Ok(Self::Cancel(CancelMsg(Block {
                    index,
                    begin,
                    length,
                })))
            }
            ty => Ok(Self::Unknown(ty, &buf[1..1 + msg_len - 1])),
        }
    }
}

/// Keep alive message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeepAliveMsg;

impl KeepAliveMsg {
    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        0
    }
}

/// Choke message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChokeMsg;

impl ChokeMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 0;

    /// Message length.
    pub const LEN: usize = 1;

    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        1
    }
}

/// Unchoke message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnchokeMsg;

impl UnchokeMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 1;

    /// Message length.
    pub const LEN: usize = 1;

    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        1
    }
}

/// Interested message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InterestedMsg;

impl InterestedMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 2;

    /// Message length.
    pub const LEN: usize = 1;

    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        1
    }
}

/// Not interested message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NotInterestedMsg;

impl NotInterestedMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 3;

    /// Message length.
    pub const LEN: usize = 1;

    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        1
    }
}

/// Have piece index message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HaveMsg(pub Index);

impl HaveMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 4;

    /// Message length.
    pub const LEN: usize = 5;

    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        1 + 4
    }
}

/// Bitfield of have piece indexes message.
#[derive(Clone, PartialEq, Eq)]
pub struct BitfieldMsg<'a>(pub &'a [u8]);

impl<'a> BitfieldMsg<'a> {
    /// Message type identifier.
    pub const TYPE: u8 = 5;

    /// Length of message.
    ///
    /// # Panics
    ///
    /// Panics if the size of the bitfield is greater than a [u32].
    #[must_use]
    pub fn msg_len(&self) -> u32 {
        1 + (u32::try_from(self.0.len()).unwrap())
    }
}

impl<'a> fmt::Debug for BitfieldMsg<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct BytesDebug<'a>(&'a [u8]);
        impl<'a> fmt::Debug for BytesDebug<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                for b in self.0 {
                    write!(f, "{b:02x}")?;
                }
                Ok(())
            }
        }

        f.debug_tuple("BitfieldMsg")
            .field(&BytesDebug(self.0))
            .finish()
    }
}

/// Request a block message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RequestMsg(pub Block);

impl RequestMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 6;

    /// Message length.
    pub const LEN: usize = 13;

    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        1 + 4 + 4 + 4
    }
}

/// Response fulfilling a block request with block data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PieceMsg<'a>(pub BlockData<'a>);

impl<'a> PieceMsg<'a> {
    /// Message type identifier.
    pub const TYPE: u8 = 7;

    /// Length of message.
    ///
    /// # Panics
    ///
    /// Panics if the length of the data is greater than a [u32].
    #[must_use]
    pub fn msg_len(&self) -> u32 {
        1 + 4 + 4 + u32::try_from(self.0.data.len()).unwrap()
    }
}

/// Cancels a block request message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CancelMsg(pub Block);

impl CancelMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 8;

    /// Message length.
    pub const LEN: usize = 13;

    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        1 + 4 + 4 + 4
    }
}

/// Identifies what completed parts of the handshake have been received.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReceivedHandshakeState {
    /// Have not received the complete protocol string yet.
    ///
    /// Contains the total number of bytes in the protocol string received so far.
    None(usize),
    /// Received the protocol string.
    ReceivedProtocol,
    /// Received the protocol string and the reserved bytes.
    ReceivedReservedBytes(ReservedBytes),
    /// Received the protocol string, reserved bytes, and the info hash.
    ReceivedReservedBytesAndInfoHash(ReservedBytes, InfoHash),
    /// Received the protocol string, reserved bytes, info hash, and peer Id.
    ReceivedHandshake(ReservedBytes, InfoHash, Id),
}

impl Default for ReceivedHandshakeState {
    fn default() -> Self {
        Self::None(0)
    }
}

/// Parses a handshake based on the current state.
///
/// Advances the buffer if any data is consumed.
///
/// If the next part of the handshake is completely received, then returns the next state. Otherwise, it returns None.
///
/// # Errors
///
/// If an invalid protocol input is received, returns an `InvalidInput`.
pub fn parse_handshake<B>(
    buf: &mut B,
    state: &ReceivedHandshakeState,
) -> Result<Option<ReceivedHandshakeState>, InvalidInput>
where
    B: Buf,
{
    match state {
        ReceivedHandshakeState::None(mut handshake_offset) => {
            let offset = handshake_offset;
            for _ in offset..core::cmp::min(20, buf.remaining()) {
                if PROTOCOL_STRING_BYTES[handshake_offset] != buf.get_u8() {
                    return Err(InvalidInput);
                }
                handshake_offset += 1;
            }

            debug_assert!(handshake_offset <= 20);
            if handshake_offset == 20 {
                Ok(Some(ReceivedHandshakeState::ReceivedProtocol))
            } else {
                Ok(Some(ReceivedHandshakeState::None(handshake_offset)))
            }
        }
        ReceivedHandshakeState::ReceivedProtocol => {
            if buf.remaining() < 8 {
                return Ok(None);
            }

            let reserved_bytes = {
                let mut tmp: [u8; 8] = [0; 8];
                buf.copy_to_slice(&mut tmp);
                ReservedBytes::from(tmp)
            };

            Ok(Some(ReceivedHandshakeState::ReceivedReservedBytes(
                reserved_bytes,
            )))
        }
        ReceivedHandshakeState::ReceivedReservedBytes(reserved_bytes) => {
            if buf.remaining() < 20 {
                return Ok(None);
            }

            let info_hash = {
                let mut tmp: [u8; 20] = [0; 20];
                buf.copy_to_slice(&mut tmp);
                InfoHash::from(tmp)
            };
            Ok(Some(
                ReceivedHandshakeState::ReceivedReservedBytesAndInfoHash(
                    *reserved_bytes,
                    info_hash,
                ),
            ))
        }
        ReceivedHandshakeState::ReceivedReservedBytesAndInfoHash(reserved_bytes, info_hash) => {
            if buf.remaining() < 20 {
                return Ok(None);
            }

            let peer_id = {
                let mut tmp: [u8; 20] = [0; 20];
                buf.copy_to_slice(&mut tmp);
                peer::Id::from(tmp)
            };

            Ok(Some(ReceivedHandshakeState::ReceivedHandshake(
                *reserved_bytes,
                *info_hash,
                peer_id,
            )))
        }
        ReceivedHandshakeState::ReceivedHandshake(..) => Ok(None),
    }
}

/// Protocol related metrics.
///
/// Useful to keep track of metrics about what messages are received and sent.
#[derive(Debug, Default, Clone, Copy)]
pub struct Metrics {
    /// Keepalive messages count
    pub keepalive_msgs: u64,
    /// Choke messages count
    pub choke_msgs: u64,
    /// Unchoke messages count
    pub unchoke_msgs: u64,
    /// Interested messages count
    pub interested_msgs: u64,
    /// Not interested messages count
    pub not_interested_msgs: u64,
    /// Have messages count
    pub have_msgs: u64,
    /// Bitfield messages count
    pub bitfield_msgs: u64,
    /// Bitfield bytes count
    pub bitfield_bytes: u64,
    /// Request messages count
    pub request_msgs: u64,
    /// Piece messages count
    pub piece_msgs: u64,
    /// Piece bytes count
    pub piece_bytes: u64,
    /// Unrequested piece bytes count
    pub unrequested_piece_bytes: u64,
    /// Cancel messages count
    pub cancel_msgs: u64,
    /// Unknown bytes count
    pub unknown_bytes: u64,
}

impl Metrics {
    /// Returns if any counter is not zero.
    ///
    /// Primarily used to determine if the bitfield message should be received after the protocol handshake.
    #[must_use]
    pub fn is_any_nonzero(&self) -> bool {
        self.keepalive_msgs != 0
            || self.choke_msgs != 0
            || self.unchoke_msgs != 0
            || self.interested_msgs != 0
            || self.not_interested_msgs != 0
            || self.have_msgs != 0
            || self.bitfield_bytes != 0
            || self.bitfield_msgs != 0
            || self.request_msgs != 0
            || self.piece_msgs != 0
            || self.piece_bytes != 0
            || self.unrequested_piece_bytes != 0
            || self.cancel_msgs != 0
            || self.unknown_bytes != 0
    }

    /// Increases the metrics for a request message.
    #[inline]
    pub fn add_request(&mut self) {
        self.request_msgs = self.request_msgs.saturating_add(1);
    }

    /// Increases the metrics for a piece message.
    #[inline]
    pub fn add_piece(&mut self, piece_msg: &PieceMsg<'_>) {
        let piece_bytes = piece_msg.0.data.len() as u64;
        self.piece_bytes = self.piece_bytes.saturating_add(piece_bytes);
        self.piece_msgs = self.piece_msgs.saturating_add(1);
    }

    /// Increases the metrics for a keep alive message.
    #[inline]
    pub fn add_keepalive(&mut self) {
        self.keepalive_msgs = self.keepalive_msgs.saturating_add(1);
    }

    /// Increases the metrics for a have message.
    #[inline]
    pub fn add_have(&mut self) {
        self.have_msgs = self.have_msgs.saturating_add(1);
    }

    /// Increases the metrics for a choke message.
    #[inline]
    pub fn add_choke(&mut self) {
        self.choke_msgs = self.choke_msgs.saturating_add(1);
    }

    /// Increases the metrics for an unchoke message.
    #[inline]
    pub fn add_unchoke(&mut self) {
        self.unchoke_msgs = self.unchoke_msgs.saturating_add(1);
    }

    /// Increases the metrics for an interested message.
    #[inline]
    pub fn add_interested(&mut self) {
        self.interested_msgs = self.interested_msgs.saturating_add(1);
    }

    /// Increases the metrics for a not interested message.
    #[inline]
    pub fn add_not_interested(&mut self) {
        self.not_interested_msgs = self.not_interested_msgs.saturating_add(1);
    }

    /// Increases the metrics for a cancel message.
    #[inline]
    pub fn add_cancel(&mut self) {
        self.cancel_msgs = self.cancel_msgs.saturating_add(1);
    }

    /// Increases the metrics for a bitfield message.
    #[inline]
    pub fn add_bitfield(&mut self, bitfield_msg: &BitfieldMsg<'_>) {
        let bitfield_msg_len = u64::from(bitfield_msg.msg_len() - 1);
        self.bitfield_msgs = self.bitfield_msgs.saturating_add(1);
        self.bitfield_bytes = self.bitfield_bytes.saturating_add(bitfield_msg_len);
    }

    /// Increases the metrics for an unknown message.
    #[inline]
    pub fn add_unknown(&mut self, len: u64) {
        self.unknown_bytes = self.unknown_bytes.saturating_add(len);
    }

    /// Adds a frame's info to the metrics.
    ///
    /// Useful to add a frame's metrics to the overall metrics.
    pub fn add_frame(&mut self, frame: &Frame<'_>) {
        match frame {
            Frame::Request(_) => self.add_request(),
            Frame::Piece(piece_msg) => self.add_piece(piece_msg),
            Frame::KeepAlive => self.add_keepalive(),
            Frame::Have(_) => self.add_have(),
            Frame::Choke => self.add_choke(),
            Frame::Unchoke => self.add_unchoke(),
            Frame::Interested => self.add_interested(),
            Frame::NotInterested => self.add_not_interested(),
            Frame::Cancel(_) => self.add_cancel(),
            Frame::Bitfield(bitfield_msg) => self.add_bitfield(bitfield_msg),
            Frame::Unknown(_, data) => {
                self.add_unknown(u64::try_from(data.len()).unwrap_or(u64::MAX));
            }
        }
    }
}

impl core::ops::Add for Metrics {
    type Output = Metrics;

    fn add(mut self, rhs: Metrics) -> Metrics {
        self += rhs;
        self
    }
}

impl core::ops::AddAssign for Metrics {
    fn add_assign(&mut self, rhs: Metrics) {
        self.keepalive_msgs = self.keepalive_msgs.saturating_add(rhs.keepalive_msgs);
        self.choke_msgs = self.choke_msgs.saturating_add(rhs.choke_msgs);
        self.unchoke_msgs = self.unchoke_msgs.saturating_add(rhs.unchoke_msgs);
        self.interested_msgs = self.interested_msgs.saturating_add(rhs.interested_msgs);
        self.not_interested_msgs = self
            .not_interested_msgs
            .saturating_add(rhs.not_interested_msgs);
        self.have_msgs = self.have_msgs.saturating_add(rhs.have_msgs);
        self.bitfield_msgs = self.bitfield_msgs.saturating_add(rhs.bitfield_msgs);
        self.bitfield_bytes = self.bitfield_bytes.saturating_add(rhs.bitfield_bytes);
        self.request_msgs = self.request_msgs.saturating_add(rhs.request_msgs);
        self.piece_msgs = self.piece_msgs.saturating_add(rhs.piece_msgs);
        self.piece_bytes = self.piece_bytes.saturating_add(rhs.piece_bytes);
        self.unrequested_piece_bytes = self
            .unrequested_piece_bytes
            .saturating_add(rhs.unrequested_piece_bytes);
        self.cancel_msgs = self.cancel_msgs.saturating_add(rhs.cancel_msgs);
        self.unknown_bytes = self.unknown_bytes.saturating_add(rhs.unknown_bytes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metrics_size() {
        assert_eq!(core::mem::size_of::<Metrics>(), 112);
    }
}
