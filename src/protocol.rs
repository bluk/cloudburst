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

use bytes::{Buf, Bytes, BytesMut};
use core::{borrow::Borrow, fmt};

use crate::{
    metainfo::InfoHash,
    peer::Id,
    piece::{Block, BlockBegin, BlockData, BlockLength, Index},
};

/// The initial protocol handshake string.
pub const PROTOCOL_STRING_BYTES: [u8; 20] = *b"\x13BitTorrent protocol";

/// The reserved bytes in the handshake.
#[derive(Default, Clone, Copy, PartialEq)]
pub struct ReservedBytes([u8; 8]);

impl fmt::Debug for ReservedBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct ReservedBytesDebug<'a>(&'a [u8; 8]);

        impl<'a> fmt::Debug for ReservedBytesDebug<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                for b in self.0.iter() {
                    write!(f, "{:02x}", b)?;
                }
                Ok(())
            }
        }

        f.debug_tuple("ReservedBytes")
            .field(&ReservedBytesDebug(&self.0))
            .finish()
    }
}

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

/// Message frame.
///
/// An individual message.
#[derive(Debug, PartialEq)]
pub enum Frame {
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
    Bitfield(BitfieldMsg),
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
    Piece(PieceMsg),
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
    Unknown(u8, Bytes),
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

/// The expected maximum length of a message to be sent.
pub const MAX_EXPECTED_FRAME_LEN: usize = 1 + 4 + 4 + 16384;

impl Frame {
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
        let msg_len = usize::try_from(msg_len).unwrap();

        if msg_len > MAX_EXPECTED_FRAME_LEN {
            return Err(Error::MessageLengthTooLarge(msg_len));
        }

        if cursor.remaining() < msg_len {
            return Err(Error::IncompleteFrame);
        }

        if msg_len == 0 {
            return Ok(());
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
    pub fn parse(buf: &mut BytesMut) -> Result<Self, Error> {
        if buf.remaining() < 4 {
            return Err(Error::IncompleteFrame);
        }

        let msg_len = buf.get_u32();
        let msg_len = usize::try_from(msg_len).unwrap();

        if msg_len > MAX_EXPECTED_FRAME_LEN {
            return Err(Error::MessageLengthTooLarge(msg_len));
        }

        if buf.remaining() < msg_len {
            return Err(Error::IncompleteFrame);
        }

        if msg_len == 0 {
            return Ok(Self::KeepAlive);
        }

        let ty = buf.get_u8();
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
                let index = Index::from(buf.get_u32());
                Ok(Self::Have(HaveMsg(index)))
            }
            BitfieldMsg::TYPE => {
                let bitfield = buf.split_to(msg_len - 1);
                Ok(Self::Bitfield(BitfieldMsg(bitfield.freeze())))
            }
            RequestMsg::TYPE => {
                if msg_len != RequestMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                let index = Index::from(buf.get_u32());
                let begin = BlockBegin::from(buf.get_u32());
                let length = BlockLength::from(buf.get_u32());
                Ok(Self::Request(RequestMsg(Block {
                    index,
                    begin,
                    length,
                })))
            }
            PieceMsg::TYPE => {
                let index = Index::from(buf.get_u32());
                let begin = BlockBegin::from(buf.get_u32());
                let data = buf.split_to(msg_len - 1 - 4 - 4).freeze();
                Ok(Self::Piece(PieceMsg(BlockData { index, begin, data })))
            }
            CancelMsg::TYPE => {
                if msg_len != CancelMsg::LEN {
                    return Err(Error::InvalidMessageLength);
                }
                let index = Index::from(buf.get_u32());
                let begin = BlockBegin::from(buf.get_u32());
                let length = BlockLength::from(buf.get_u32());
                Ok(Self::Cancel(CancelMsg(Block {
                    index,
                    begin,
                    length,
                })))
            }
            ty => {
                let data = buf.split_to(msg_len - 1);
                Ok(Self::Unknown(ty, data.freeze()))
            }
        }
    }
}

/// Keep alive message.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct KeepAliveMsg;

impl KeepAliveMsg {
    /// Length of message.
    #[must_use]
    pub const fn msg_len() -> u32 {
        0
    }
}

/// Choke message.
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[derive(Clone, PartialEq)]
pub struct BitfieldMsg(pub Bytes);

impl BitfieldMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 5;

    /// Length of message.
    ///
    /// # Panics
    ///
    /// Panics if the size of the bitfield is greater than a [u32].
    pub fn msg_len(&self) -> u32 {
        1 + (u32::try_from(self.0.len()).unwrap())
    }
}

impl fmt::Debug for BitfieldMsg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct BytesDebug<'a>(&'a Bytes);
        impl<'a> fmt::Debug for BytesDebug<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                for b in self.0.iter() {
                    write!(f, "{:02x}", b)?;
                }
                Ok(())
            }
        }

        f.debug_tuple("BitfieldMsg")
            .field(&BytesDebug(&self.0))
            .finish()
    }
}

/// Request a block message.
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
pub struct PieceMsg(pub BlockData);

impl PieceMsg {
    /// Message type identifier.
    pub const TYPE: u8 = 7;

    /// Length of message.
    ///
    /// # Panics
    ///
    /// Panics if the length of the data is greater than a [u32].
    pub fn msg_len(&self) -> u32 {
        1 + 4 + 4 + u32::try_from(self.0.data.len()).unwrap()
    }
}

/// Cancels a block request message.
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[derive(Debug, Clone, Copy, PartialEq)]
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
