// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Pings a node.
//!
//! The query and response are described in [BEP 5][bep_0005].
//!
//! [bep_0005]: http://bittorrent.org/beps/bep_0005.html

use bt_bencode::Value;
use core::convert::TryFrom;
use serde_bytes::{ByteBuf, Bytes};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{collections::BTreeMap, string::String};

#[cfg(feature = "std")]
use std::{collections::BTreeMap, string::String};

use crate::dht::node::{Id, LocalId};

/// The "ping" query method name.
pub const METHOD_PING: &[u8] = b"ping";

/// The arguments for the ping query message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QueryArgs {
    id: Id,
}

impl QueryArgs {
    /// Instantiates a new query message.
    #[must_use]
    #[inline]
    pub const fn new(id: LocalId) -> Self {
        Self {
            id: Id::new((id.0).0),
        }
    }

    /// Sets the querying node ID in the arguments.
    #[inline]
    pub fn set_id(&mut self, id: LocalId) {
        self.id = Id::new((id.0).0);
    }
}

impl crate::dht::krpc::QueryArgs for QueryArgs {
    fn method_name() -> &'static [u8] {
        METHOD_PING
    }

    fn id(&self) -> Id {
        self.id
    }

    fn to_value(&self) -> Value {
        Value::from(self)
    }
}

impl TryFrom<Value> for QueryArgs {
    type Error = crate::dht::krpc::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}

impl TryFrom<&Value> for QueryArgs {
    type Error = crate::dht::krpc::Error;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .as_dict()
                .ok_or(crate::dht::krpc::Error::is_deserialize_error())?,
        )
    }
}

impl TryFrom<&BTreeMap<ByteBuf, Value>> for QueryArgs {
    type Error = crate::dht::krpc::Error;

    fn try_from(args: &BTreeMap<ByteBuf, Value>) -> Result<Self, Self::Error> {
        args.get(Bytes::new(b"id"))
            .and_then(bt_bencode::Value::as_byte_str)
            .and_then(|id| Id::try_from(id.as_slice()).ok())
            .map(|id| QueryArgs { id })
            .ok_or(crate::dht::krpc::Error::is_deserialize_error())
    }
}

impl From<QueryArgs> for Value {
    fn from(args: QueryArgs) -> Self {
        let mut d: BTreeMap<ByteBuf, Value> = BTreeMap::new();
        d.insert(
            ByteBuf::from(String::from("id")),
            Value::ByteStr(ByteBuf::from(args.id)),
        );
        Value::Dict(d)
    }
}

impl From<&QueryArgs> for Value {
    fn from(args: &QueryArgs) -> Self {
        Value::from(*args)
    }
}

/// The value for the ping response.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RespValues {
    id: Id,
}

impl RespValues {
    /// Instantiates a new instance.
    #[must_use]
    #[inline]
    pub const fn new(id: LocalId) -> Self {
        Self {
            id: Id::new((id.0).0),
        }
    }

    /// Sets the queried node Id.
    #[inline]
    pub fn set_id(&mut self, id: LocalId) {
        self.id = Id::new((id.0).0);
    }
}

impl crate::dht::krpc::RespVal for RespValues {
    fn id(&self) -> Id {
        self.id
    }

    fn to_value(&self) -> Value {
        Value::from(*self)
    }
}

impl TryFrom<&BTreeMap<ByteBuf, Value>> for RespValues {
    type Error = crate::dht::krpc::Error;

    fn try_from(values: &BTreeMap<ByteBuf, Value>) -> Result<Self, Self::Error> {
        values
            .get(Bytes::new(b"id"))
            .and_then(bt_bencode::Value::as_byte_str)
            .and_then(|id| Id::try_from(id.as_slice()).ok())
            .map(|id| RespValues { id })
            .ok_or(crate::dht::krpc::Error::is_deserialize_error())
    }
}

impl From<RespValues> for Value {
    fn from(values: RespValues) -> Self {
        Value::from(&values)
    }
}

impl From<&RespValues> for Value {
    fn from(values: &RespValues) -> Self {
        let mut args: BTreeMap<ByteBuf, Value> = BTreeMap::new();
        args.insert(
            ByteBuf::from(String::from("id")),
            Value::ByteStr(ByteBuf::from(values.id)),
        );
        Value::Dict(args)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::dht::krpc::{Error, Msg, QueryArgs, QueryMsg, RespMsg, RespVal, Ty};

    #[test]
    fn test_serde_ping_query() -> Result<(), Error> {
        let ping_query = b"d1:ad2:id20:abcdefghij0123456789e1:q4:ping1:t2:aa1:y1:qe";

        let msg_value: Value = bt_bencode::from_slice(&ping_query[..])?;
        assert_eq!(msg_value.ty(), Some(Ty::Query));
        assert_eq!(msg_value.method_name(), Some(METHOD_PING));
        assert_eq!(
            msg_value.method_name_str(),
            Some(core::str::from_utf8(METHOD_PING).unwrap())
        );
        assert_eq!(msg_value.tx_id(), Some(b"aa".as_ref()));
        if let Some(args) = msg_value
            .args()
            .and_then(|a| crate::dht::krpc::ping::QueryArgs::try_from(a).ok())
        {
            assert_eq!(args.id(), Id::from(*b"abcdefghij0123456789"));

            let args_value = args.into();
            let ser_query_msg = crate::dht::krpc::ser::QueryMsg {
                a: Some(&args_value),
                q: Bytes::new(METHOD_PING),
                t: Bytes::new(b"aa"),
                v: None,
            };
            let ser_msg = bt_bencode::to_vec(&ser_query_msg).unwrap();
            assert_eq!(ser_msg, ping_query);
            Ok(())
        } else {
            panic!()
        }
    }

    #[test]
    fn test_serde_ping_response_values() -> Result<(), Error> {
        let ping_resp = b"d1:rd2:id20:mnopqrstuvwxyz123456e1:t2:aa1:y1:re";

        let msg_value: Value = bt_bencode::from_slice(&ping_resp[..])?;
        assert_eq!(msg_value.ty(), Some(Ty::Response));
        assert_eq!(msg_value.method_name(), None);
        assert_eq!(msg_value.method_name_str(), None);
        assert_eq!(msg_value.tx_id(), Some(b"aa".as_ref()));

        if let Some(values) = msg_value
            .values()
            .and_then(|a| RespValues::try_from(a).ok())
        {
            assert_eq!(values.id(), Id::from(*b"mnopqrstuvwxyz123456"));

            let resp_values = values.into();
            let ser_resp_msg = crate::dht::krpc::ser::RespMsg {
                r: Some(&resp_values),
                t: Bytes::new(b"aa"),
                v: None,
            };
            let ser_msg = bt_bencode::to_vec(&ser_resp_msg).unwrap();
            assert_eq!(ser_msg, ping_resp);
            Ok(())
        } else {
            panic!()
        }
    }
}
