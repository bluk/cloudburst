// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Serialization of KRPC messages.

use serde::{ser::SerializeMap, Serialize, Serializer};
use serde_bytes::Bytes;

/// Query message.
#[derive(Debug)]
pub struct QueryMsg<'a, T> {
    /// Query arguments
    pub a: T,
    /// Method name of query
    pub q: &'a Bytes,
    /// Transaction id
    pub t: &'a Bytes,
    /// Client version
    pub v: Option<&'a Bytes>,
}

impl<'a, T> Serialize for QueryMsg<'a, T>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("a", &self.a)?;
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
pub struct RespMsg<'a, T> {
    /// Return values
    pub r: T,
    /// Transaction id
    pub t: &'a Bytes,
    /// Client version
    pub v: Option<&'a Bytes>,
}

impl<'a, T> Serialize for RespMsg<'a, T>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("r", &self.r)?;
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
pub struct ErrMsg<'a, T> {
    /// Error details
    pub e: T,
    /// Transaction id
    pub t: &'a Bytes,
    /// Client version
    pub v: Option<&'a Bytes>,
}

impl<'a, T> Serialize for ErrMsg<'a, T>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("e", &self.e)?;
        map.serialize_entry("t", &self.t)?;
        if self.v.is_some() {
            map.serialize_entry("v", &self.v)?;
        }
        map.serialize_entry("y", "e")?;
        map.end()
    }
}

#[cfg(test)]
mod tests {
    use serde_bytes::Bytes;

    use super::*;

    use crate::dht::krpc::{Error, ErrorCode, Msg, Ty};

    #[test]
    fn test_serde_error() -> Result<(), Error> {
        let encoded_error = b"d1:eli201e23:A Generic Error Ocurrede1:t2:aa1:y1:ee";

        let error_msg: Msg<'_> = bt_bencode::from_slice(encoded_error)?;
        assert_eq!(error_msg.ty(), Ty::Error);
        assert_eq!(error_msg.tx_id(), b"aa".as_ref());
        assert_eq!(
            error_msg.error(),
            Some((ErrorCode::GenericError, "A Generic Error Ocurred"))
        );

        let ser_error_msg = ErrMsg {
            e: &(201, "A Generic Error Ocurred"),
            t: Bytes::new(b"aa"),
            v: None,
        };
        let ser_msg = bt_bencode::to_vec(&ser_error_msg).unwrap();
        assert_eq!(ser_msg, encoded_error);
        Ok(())
    }
}
