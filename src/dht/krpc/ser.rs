// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Serialization of KRPC messages.

use bt_bencode::Value;
use serde::{ser::SerializeMap, Serialize, Serializer};
use serde_bytes::Bytes;

/// Query message.
#[derive(Debug)]
pub struct QueryMsg<'a> {
    /// Query arguments
    pub a: Option<&'a Value>,
    /// Method name of query
    pub q: &'a Bytes,
    /// Transaction id
    pub t: &'a Bytes,
    /// Client version
    pub v: Option<&'a Bytes>,
}

impl<'a> Serialize for QueryMsg<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        if self.a.is_some() {
            map.serialize_entry("a", &self.a)?;
        }
        map.serialize_entry("q", &self.q)?;
        map.serialize_entry("t", &self.t)?;
        if self.v.is_some() {
            map.serialize_entry("v", &self.v)?;
        }
        map.serialize_entry("y", "q")?;
        map.end()
    }
}

/// Response message.
#[derive(Debug)]
pub struct RespMsg<'a> {
    /// Return values
    pub r: Option<&'a Value>,
    /// Transaction id
    pub t: &'a Bytes,
    /// Client version
    pub v: Option<&'a Bytes>,
}

impl<'a> Serialize for RespMsg<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        if self.r.is_some() {
            map.serialize_entry("r", &self.r)?;
        }
        map.serialize_entry("t", &self.t)?;
        if self.v.is_some() {
            map.serialize_entry("v", &self.v)?;
        }
        map.serialize_entry("y", "r")?;
        map.end()
    }
}

/// Error message.
#[derive(Debug)]
pub struct ErrMsg<'a> {
    /// Error details
    pub e: Option<&'a Value>,
    /// Transaction id
    pub t: &'a Bytes,
    /// Client version
    pub v: Option<&'a Bytes>,
}

impl<'a> Serialize for ErrMsg<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        if self.e.is_some() {
            map.serialize_entry("e", &self.e)?;
        }
        map.serialize_entry("t", &self.t)?;
        if self.v.is_some() {
            map.serialize_entry("v", &self.v)?;
        }
        map.serialize_entry("y", "e")?;
        map.end()
    }
}
