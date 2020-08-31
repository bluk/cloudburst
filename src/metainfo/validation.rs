// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Validates the metainfo.

#[cfg(feature = "std")]
use std::path::{Path, PathBuf};

/// A validation error.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[non_exhaustive]
pub enum Error {
    /// No file information
    #[cfg_attr(feature = "std", error("no file info"))]
    NoFileInfo,
    /// Invalid path
    #[cfg_attr(feature = "std", error("invalid path"))]
    InvalidPath,
    /// Duplicate file paths
    #[cfg_attr(feature = "std", error("duplicate file paths"))]
    DuplicatePaths,
    /// Invalid file info
    #[cfg_attr(feature = "std", error("invalid file info"))]
    InvalidFileInfo,
    /// Unknown meta version
    #[cfg_attr(feature = "std", error("unknown meta version"))]
    UnknownMetaversion,
    /// Missing required fields
    #[cfg_attr(feature = "std", error("missing information"))]
    MissingInfo,
}

#[cfg(feature = "std")]
fn validate_path<P: AsRef<Path>>(path: P) -> Result<(), Error> {
    use std::path::Component;

    let path = path.as_ref();
    let mut is_not_empty = false;

    for c in path.components() {
        match c {
            Component::Normal(_) => {
                is_not_empty = true;
            }
            Component::ParentDir => {
                return Err(Error::InvalidPath);
            }
            Component::CurDir | Component::RootDir | Component::Prefix(_) => {
                return Err(Error::InvalidPath)
            }
        }
    }

    if is_not_empty {
        Ok(())
    } else {
        Err(Error::InvalidPath)
    }
}

#[cfg(feature = "std")]
fn check_info(info: &super::Info) -> Result<(), Error> {
    use super::MetaVersion;

    match info.meta_version() {
        MetaVersion::V1 => {}
        MetaVersion::V2 => {
            todo!()
        }
        MetaVersion::Unknown(_) => return Err(Error::UnknownMetaversion),
    }

    let base_name = info.name();
    let piece_len = u64::from(info.piece_length());
    let pieces = info.pieces().ok_or(Error::MissingInfo)?;

    if let Some(files) = info.files() {
        if info.length().is_some() {
            return Err(Error::InvalidFileInfo);
        }
        let mut paths = Vec::with_capacity(files.len());
        for path in files.iter().map(super::File::to_path_buf) {
            validate_path(&path)?;
            paths.push(path);
        }

        let dir_path = PathBuf::from(base_name);
        validate_path(dir_path)?;

        paths.sort();
        paths.dedup();
        if paths.len() != files.len() {
            return Err(Error::DuplicatePaths);
        }

        let total_len = files.iter().fold(0, |acc, file| acc + file.length());
        let expected_num_of_pieces = total_len / piece_len + u64::from(total_len % piece_len != 0);
        if expected_num_of_pieces != u64::try_from(pieces.len()).unwrap() {
            return Err(Error::InvalidFileInfo);
        }

        Ok(())
    } else if let Some(total_len) = info.length() {
        let path = PathBuf::from(base_name);
        validate_path(path)?;

        let expected_num_of_pieces = total_len / piece_len + u64::from(total_len % piece_len != 0);
        if expected_num_of_pieces != u64::try_from(pieces.len()).unwrap() {
            return Err(Error::InvalidFileInfo);
        }

        Ok(())
    } else {
        Err(Error::NoFileInfo)
    }
}

/// Checks the [Metainfo][super::Metainfo] is valid.
///
/// Verify the metainfo is well formed and any paths are valid.
///
/// # Errors
///
/// If there is a validation error such as a missing required field.
#[cfg(feature = "std")]
pub fn check(metainfo: &super::Metainfo) -> Result<(), Error> {
    check_info(metainfo.info())
}
