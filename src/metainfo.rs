// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Information about what the torrent is for and how to join the peer to peer swarm.

use crate::piece;
use core::{borrow::Borrow, fmt, slice::ChunksExact};
use serde_derive::{Deserialize, Serialize};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{string::String, vec, vec::Vec};
#[cfg(feature = "std")]
use std::{path::PathBuf, string::String, vec, vec::Vec};

pub mod validation;

/// The version which the metainfo is compatible with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaVersion {
    /// Version 1
    V1,
    /// Version 2
    V2,
    /// An unknown version
    Unknown(u64),
}

impl Default for MetaVersion {
    fn default() -> Self {
        Self::V1
    }
}

impl From<u64> for MetaVersion {
    fn from(value: u64) -> Self {
        match value {
            1 => MetaVersion::V1,
            2 => MetaVersion::V2,
            n => MetaVersion::Unknown(n),
        }
    }
}

fn de_announce_list<'de, 'a, D>(deserializer: D) -> Result<Option<Vec<Vec<&'a str>>>, D::Error>
where
    D: serde::de::Deserializer<'de>,
    'de: 'a,
{
    use serde::de::{self, Visitor};

    struct AnnounceListOptionalVisitor;

    impl<'de> Visitor<'de> for AnnounceListOptionalVisitor {
        type Value = Option<Vec<Vec<&'de str>>>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("an announce list")
        }

        fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            match core::str::from_utf8(v) {
                Ok(s) => {
                    let urls = s.split(',').map(str::trim).collect();
                    Ok(Some(vec![urls]))
                }
                Err(_) => Err(E::custom(String::from(
                    "announce list was not a valid UTF-8 string",
                ))),
            }
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: de::SeqAccess<'de>,
        {
            let mut v = Vec::with_capacity(seq.size_hint().unwrap_or(0));
            while let Some(value) = seq.next_element()? {
                v.push(value);
            }
            Ok(Some(v))
        }
    }

    deserializer.deserialize_any(AnnounceListOptionalVisitor)
}

/// Describes how to join a torrent and how to verify data from the torrent.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Metainfo<'a> {
    /// URL of tracker
    #[serde(skip_serializing_if = "Option::is_none", borrow)]
    pub announce: Option<&'a str>,
    /// A multi-tier list of trackers.
    ///
    /// Optional extension described in [BEP 0012][bep_0012].
    ///
    /// [bep_0012]: http://bittorrent.org/beps/bep_0012.html
    #[serde(default)]
    #[serde(
        rename = "announce-list",
        deserialize_with = "de_announce_list",
        borrow
    )]
    pub announce_list: Option<Vec<Vec<&'a str>>>,
    /// An optional free-form comment about the torrent.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<&'a str>,
    /// An optional string about what program created the torrent.
    #[serde(rename = "created by")]
    #[serde(skip_serializing_if = "Option::is_none", borrow)]
    pub created_by: Option<&'a str>,
    /// The number of seconds since UNIX epoch time to indicate when the torrent was created.
    #[serde(rename = "creation date", skip_serializing_if = "Option::is_none")]
    pub creation_date: Option<u64>,
    /// Information about the torrent's data.
    #[serde(borrow)]
    pub info: Info<'a>,
}

impl<'a> Metainfo<'a> {}

/// Information about the data exchanged in the torrent.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct Info<'a> {
    /// Name of the suggested file/folder to save as.
    #[serde(borrow)]
    pub name: &'a str,
    /// The number of bytes for each piece of a file, except the last one which is the leftover bytes.
    #[serde(rename = "piece length")]
    pub piece_length: u64,
    /// If a single file, then the length of the file. If multiple files, None.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub length: Option<u64>,
    /// If multiple files, a list of file information.
    #[serde(skip_serializing_if = "Option::is_none", borrow)]
    pub files: Option<Vec<File<'a>>>,
    /// The SHA1 hashes of each piece
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none", borrow)]
    pub pieces: Option<&'a [u8]>,
    /// The version of the specification used.
    #[serde(rename = "meta version", skip_serializing_if = "Option::is_none")]
    pub meta_version: Option<u64>,
}

impl<'a> Info<'a> {
    /// The number of bytes for each piece of a file, except the last one which is the leftover bytes.
    ///
    /// # Panics
    ///
    /// Panics if the piece length is greater than a [u32].
    #[must_use]
    pub fn piece_length(&self) -> piece::Length {
        piece::Length::from(u32::try_from(self.piece_length).unwrap())
    }

    /// The length of a specific piece.
    ///
    /// # Panics
    ///
    /// Panics if the piece length is greater than a [u32] or if there is no piece data.
    #[must_use]
    pub fn length_for_piece(&self, index: piece::Index) -> piece::Length {
        if u32::from(index) == u32::try_from(self.pieces.as_ref().unwrap().len() - 1).unwrap() {
            piece::Length::from(
                u32::try_from(self.total_size() % self.piece_length as u64).unwrap(),
            )
        } else {
            self.piece_length()
        }
    }

    /// The number of blocks for a specific piece.
    #[must_use]
    pub fn block_count_for_piece(&self, index: piece::Index) -> u32 {
        let piece_len = self.length_for_piece(index);
        (u32::from(piece_len) / piece::BlockLength::MAX)
            + if u32::from(piece_len) % piece::BlockLength::MAX == 0 {
                0
            } else {
                1
            }
    }

    /// The SHA1 hashes of each piece
    #[must_use]
    pub fn pieces(&self) -> Option<ChunksExact<'_, u8>> {
        self.pieces.map(|pieces| pieces.chunks_exact(20))
    }

    /// The maximum piece index.
    ///
    /// # Panics
    ///
    /// Panics if the number of pieces is greater than a [u32].
    #[must_use]
    pub fn max_index(&self) -> Option<piece::Index> {
        self.pieces
            .as_ref()
            .map(|pieces| piece::Index::from(u32::try_from(pieces.len()).unwrap()))
    }

    /// The total size of all the files.
    #[must_use]
    pub fn total_size(&self) -> u64 {
        self.files
            .as_ref()
            .map(|f| f.iter().map(|f| f.length).sum())
            .or(self.length)
            .unwrap_or_default()
    }

    /// The version of the specification used.
    #[must_use]
    pub fn meta_version(&self) -> MetaVersion {
        self.meta_version.map(MetaVersion::from).unwrap_or_default()
    }
}

/// File specific information in the torrent.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct File<'a> {
    length: u64,
    #[serde(borrow)]
    path: Vec<&'a str>,
}

impl<'a> File<'a> {
    /// The length of the file.
    #[must_use]
    pub fn length(&self) -> u64 {
        self.length
    }

    /// The path of the file.
    #[must_use]
    pub fn path(&self) -> &[&str] {
        self.path.as_ref()
    }

    /// The path as a standard `PathBuf`
    #[cfg(feature = "std")]
    #[must_use]
    pub fn to_path_buf(&self) -> PathBuf {
        self.path.iter().collect::<PathBuf>()
    }
}

/// A 160-bit value which is used to identify a torrent.
#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct InfoHash(pub [u8; 20]);

impl InfoHash {
    /// Instantiate with the `info` as a Bencode [Value][bt_bencode::Value] and the expected metainfo version.
    ///
    /// # Errors
    ///
    /// Returns an error if the `info` value cannot be serialized.
    pub fn with_value_and_meta_version(
        info: &bt_bencode::Value,
        meta_version: MetaVersion,
    ) -> Result<Self, bt_bencode::Error> {
        let bytes = bt_bencode::to_vec(info)?;
        Ok(Self::with_bytes_and_meta_version(bytes, meta_version))
    }

    /// Instantiate with the `info` value's raw bytes and the expected metainfo version.
    ///
    /// # Panics
    ///
    /// Panics if the [`MetaVersion`] is unknown.
    pub fn with_bytes_and_meta_version<T: AsRef<[u8]>>(
        bytes: T,
        meta_version: MetaVersion,
    ) -> Self {
        match meta_version {
            MetaVersion::V1 => {
                use sha1::{Digest, Sha1};

                let mut hasher = Sha1::new();
                hasher.update(bytes.as_ref());
                let result = hasher.finalize();
                InfoHash(result.into())
            }
            MetaVersion::V2 | MetaVersion::Unknown(_) => {
                todo!()
            }
        }
    }
}

impl AsRef<[u8]> for InfoHash {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Borrow<[u8]> for InfoHash {
    fn borrow(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 20]> for InfoHash {
    fn from(bytes: [u8; 20]) -> Self {
        Self(bytes)
    }
}

impl From<InfoHash> for Vec<u8> {
    fn from(info_hash: InfoHash) -> Self {
        Vec::from(info_hash.0)
    }
}

impl From<InfoHash> for [u8; 20] {
    fn from(info_hash: InfoHash) -> Self {
        info_hash.0
    }
}

fmt_byte_array!(InfoHash);

impl serde::Serialize for InfoHash {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_bytes(&self.0)
    }
}

// TODO: Implement std::fmt::UpperHex, std::fmt::LowerHex, std::fmt::Octal and std::fmt::Binary for InfoHash?

impl TryFrom<&[u8]> for InfoHash {
    type Error = core::array::TryFromSliceError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        <[u8; 20]>::try_from(value).map(InfoHash)
    }
}

/// Errors when reading and validating the `Metainfo`.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[non_exhaustive]
pub enum Error {
    /// A bencode error
    #[cfg_attr(feature = "std", error(transparent))]
    BtBencode(bt_bencode::Error),
    /// A validation error
    #[cfg_attr(feature = "std", error(transparent))]
    Validation(validation::Error),
}

impl From<bt_bencode::Error> for Error {
    fn from(other: bt_bencode::Error) -> Self {
        Self::BtBencode(other)
    }
}

impl From<validation::Error> for Error {
    fn from(other: validation::Error) -> Self {
        Self::Validation(other)
    }
}

/// Reads `Metainfo`.
///
/// # Important
///
/// Call [`validation::check`] to validate the data.
///
/// # Errors
///
/// Returns an error if there is a deserialization or validation error such as
/// a required field for the [Metainfo] is missing.
pub fn from_slice<'a>(buf: &'a [u8]) -> Result<(InfoHash, Metainfo<'a>), Error> {
    let torrent_value: bt_bencode::Value = bt_bencode::from_slice(buf)?;

    let info: &bt_bencode::Value = torrent_value
        .get("info")
        .ok_or(validation::Error::MissingInfo)?;

    let meta_version = info
        .get("meta_version")
        .unwrap_or(&bt_bencode::Value::Int(
            bt_bencode::value::Number::Unsigned(1),
        ))
        .as_u64()
        .map(MetaVersion::from)
        .ok_or(validation::Error::UnknownMetaversion)?;

    let info_hash = InfoHash::with_value_and_meta_version(info, meta_version)?;

    {
        #[derive(Debug, Deserialize)]
        struct MetainfoBytes<'a> {
            info: &'a [u8],
        }
        let raw_metainfo_bytes: MetainfoBytes<'_> = bt_bencode::from_slice(buf)?;
        let raw_bytes_info_hash =
            InfoHash::with_bytes_and_meta_version(raw_metainfo_bytes.info, meta_version);
        if info_hash != raw_bytes_info_hash {
            return Err(Error::BtBencode(bt_bencode::Error::new(
                bt_bencode::ErrorKind::InvalidDict,
                0,
            )));
        }
    }

    let metainfo: Metainfo<'_> = bt_bencode::from_slice(buf)?;

    Ok((info_hash, metainfo))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(feature = "alloc", not(feature = "std")))]
    use alloc::format;

    #[cfg(feature = "std")]
    use std::format;

    #[test]
    fn test_formats() {
        let info_hash = InfoHash(hex_literal::hex!(
            "8EFA979AD7627693BA91D48E941F025BAE78CB77"
        ));
        assert_eq!(
            format!("{:X}", info_hash),
            "8EFA979AD7627693BA91D48E941F025BAE78CB77"
        );
        assert_eq!(
            format!("{:#X}", info_hash),
            "0x8EFA979AD7627693BA91D48E941F025BAE78CB77"
        );
        assert_eq!(
            format!("{:x}", info_hash),
            "8efa979ad7627693ba91d48e941f025bae78cb77"
        );
        assert_eq!(
            format!("{:#x}", info_hash),
            "0x8efa979ad7627693ba91d48e941f025bae78cb77"
        );
        assert_eq!(
            format!("{:b}", info_hash),
            "10001110111110101001011110011010110101111100010111011010010011101110101001000111010100100011101001010011111101011011101011101111000110010111110111"
        );
        assert_eq!(
            format!("{:#b}", info_hash),
            "0b10001110111110101001011110011010110101111100010111011010010011101110101001000111010100100011101001010011111101011011101011101111000110010111110111"
        );
    }
}
