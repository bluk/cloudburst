// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Announces a peer for a torrent.
//!
//! The query and response are described in [BEP 5][bep_0005].
//!
//! [bep_0005]: http://bittorrent.org/beps/bep_0005.html

use bt_bencode::{value::Number, Value};
use core::convert::TryFrom;
use serde_bytes::{ByteBuf, Bytes};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{collections::BTreeMap, string::String, vec::Vec};

#[cfg(feature = "std")]
use std::{collections::BTreeMap, string::String, vec::Vec};

use crate::{
    dht::{
        krpc::Error,
        node::{Id, LocalId},
    },
    metainfo::InfoHash,
};

/// The `announce_peer` query method name.
pub const METHOD_ANNOUNCE_PEER: &[u8] = b"announce_peer";

/// The arguments for the announce peer query message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryArgs {
    id: Id,
    info_hash: InfoHash,
    token: Vec<u8>,
    port: Option<u16>,
    implied_port: Option<bool>,
}

impl QueryArgs {
    /// Instantiates a new query message.
    pub fn new<L>(
        id: L,
        info_hash: InfoHash,
        token: Vec<u8>,
        port: Option<u16>,
        implied_port: Option<bool>,
    ) -> Self
    where
        L: Into<LocalId>,
    {
        Self {
            id: Id::from(id.into()),
            info_hash,
            token,
            port,
            implied_port,
        }
    }

    /// Sets the querying node ID in the arguments.
    pub fn set_id<I>(&mut self, id: I)
    where
        I: Into<LocalId>,
    {
        self.id = Id::from(id.into());
    }

    /// Returns the `InfoHash` for the relevant torrent.
    #[must_use]
    pub fn info_hash(&self) -> InfoHash {
        self.info_hash
    }

    /// Sets the `InfoHash` for the relevant torrent.
    pub fn set_info_hash(&mut self, info_hash: InfoHash) {
        self.info_hash = info_hash;
    }

    /// Returns the token which is used by the queried node for verification.
    #[must_use]
    pub fn token(&self) -> &[u8] {
        &self.token
    }

    /// Sets the token which is used by the queried node for verification.
    pub fn set_token(&mut self, token: Vec<u8>) {
        self.token = token;
    }

    /// Returns the port which peers in the torrent should connect to.
    #[must_use]
    pub fn port(&self) -> Option<u16> {
        self.port
    }

    /// Sets the port which peers in the torrent should connect to.
    pub fn set_port(&mut self, port: Option<u16>) {
        self.port = port;
    }

    /// Returns if the port should be implied from the querying node's DHT sending port.
    #[must_use]
    pub fn implied_port(&self) -> Option<bool> {
        self.implied_port
    }

    /// Sets if the port should be implied from the querying node's DHT sending port.
    pub fn set_implied_port(&mut self, implied_port: Option<bool>) {
        self.implied_port = implied_port;
    }
}

impl crate::dht::krpc::QueryArgs for QueryArgs {
    fn method_name() -> &'static [u8] {
        METHOD_ANNOUNCE_PEER
    }

    fn id(&self) -> Id {
        self.id
    }

    fn to_value(&self) -> Value {
        Value::from(self)
    }
}

impl TryFrom<Value> for QueryArgs {
    type Error = Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}

impl TryFrom<&Value> for QueryArgs {
    type Error = Error;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        Self::try_from(value.as_dict().ok_or(Error::is_deserialize_error())?)
    }
}

impl TryFrom<&BTreeMap<ByteBuf, Value>> for QueryArgs {
    type Error = Error;

    fn try_from(args: &BTreeMap<ByteBuf, Value>) -> Result<Self, Self::Error> {
        match (
            args.get(Bytes::new(b"id"))
                .and_then(bt_bencode::Value::as_byte_str)
                .and_then(|id| Id::try_from(id.as_slice()).ok()),
            args.get(Bytes::new(b"info_hash"))
                .and_then(bt_bencode::Value::as_byte_str)
                .and_then(|info_hash| InfoHash::try_from(info_hash.as_slice()).ok()),
            args.get(Bytes::new(b"token"))
                .and_then(bt_bencode::Value::as_byte_str),
            args.get(Bytes::new(b"port"))
                .and_then(bt_bencode::Value::as_u64)
                .and_then(|port| u16::try_from(port).ok()),
            args.get(Bytes::new(b"implied_port"))
                .and_then(bt_bencode::Value::as_u64)
                .map(|implied_port| implied_port != 0),
        ) {
            (Some(id), Some(info_hash), Some(token), port, implied_port) => Ok(QueryArgs {
                id,
                info_hash,
                token: token.to_vec(),
                port,
                implied_port,
            }),
            _ => Err(Error::is_deserialize_error()),
        }
    }
}

impl From<QueryArgs> for Value {
    fn from(args: QueryArgs) -> Self {
        Value::from(&args)
    }
}

impl From<&QueryArgs> for Value {
    fn from(args: &QueryArgs) -> Self {
        let mut d: BTreeMap<ByteBuf, Value> = BTreeMap::new();
        d.insert(
            ByteBuf::from(String::from("id")),
            Value::ByteStr(ByteBuf::from(args.id)),
        );
        if let Some(implied_port) = args.implied_port {
            d.insert(
                ByteBuf::from(String::from("implied_port")),
                Value::Int(if implied_port {
                    Number::Unsigned(1)
                } else {
                    Number::Unsigned(0)
                }),
            );
        }
        d.insert(
            ByteBuf::from(String::from("info_hash")),
            Value::ByteStr(ByteBuf::from(args.info_hash)),
        );
        d.insert(
            ByteBuf::from(String::from("port")),
            Value::Int(args.port.map_or(Number::Unsigned(0), |port| {
                Number::Unsigned(u64::from(port))
            })),
        );
        d.insert(
            ByteBuf::from(String::from("token")),
            Value::ByteStr(ByteBuf::from(args.token.clone())),
        );
        Value::Dict(d)
    }
}

/// The value for the announce peer response.
#[derive(Debug)]
pub struct RespValues {
    id: Id,
}

impl RespValues {
    /// Instantiates a new instance.
    pub fn new<L>(id: L) -> Self
    where
        L: Into<LocalId>,
    {
        Self {
            id: id.into().into(),
        }
    }

    /// Sets the queried node Id.
    pub fn set_id<I>(&mut self, id: I)
    where
        I: Into<LocalId>,
    {
        self.id = Id::from(id.into());
    }
}

impl crate::dht::krpc::RespVal for RespValues {
    fn id(&self) -> Id {
        self.id
    }

    fn to_value(&self) -> Value {
        Value::from(self)
    }
}

impl TryFrom<&BTreeMap<ByteBuf, Value>> for RespValues {
    type Error = Error;

    fn try_from(values: &BTreeMap<ByteBuf, Value>) -> Result<Self, Self::Error> {
        match values
            .get(Bytes::new(b"id"))
            .and_then(bt_bencode::Value::as_byte_str)
            .and_then(|id| Id::try_from(id.as_slice()).ok())
        {
            Some(id) => Ok(RespValues { id }),
            _ => Err(Error::is_deserialize_error()),
        }
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
    use serde_bytes::Bytes;

    use super::*;

    use crate::dht::krpc::{Msg, QueryArgs, QueryMsg, RespMsg, RespVal, Ty};

    #[test]
    fn test_serde_announce_peer_query() -> Result<(), Error> {
        let announce_peer_query = b"d1:ad2:id20:abcdefghij01234567899:info_hash20:mnopqrstuvwxyz1234564:porti6331e5:token8:abcd1234e1:q13:announce_peer1:t2:aa1:y1:qe";

        let msg_value: Value = bt_bencode::from_slice(&announce_peer_query[..])?;
        assert_eq!(msg_value.ty(), Some(Ty::Query));
        assert_eq!(msg_value.method_name(), Some(METHOD_ANNOUNCE_PEER));
        assert_eq!(
            msg_value.method_name_str(),
            Some(core::str::from_utf8(METHOD_ANNOUNCE_PEER).unwrap())
        );
        assert_eq!(msg_value.tx_id(), Some(b"aa".as_ref()));
        if let Some(args) = msg_value
            .args()
            .and_then(|a| crate::dht::krpc::announce_peer::QueryArgs::try_from(a).ok())
        {
            assert_eq!(args.id(), Id::from(*b"abcdefghij0123456789"));
            assert_eq!(args.info_hash(), InfoHash::from(*b"mnopqrstuvwxyz123456"));
            assert_eq!(args.token(), b"abcd1234");
            assert_eq!(args.port(), Some(6331));
            assert!(args.implied_port().is_none());

            let args_value = args.into();
            let ser_query_msg = crate::dht::krpc::ser::QueryMsg {
                a: Some(&args_value),
                q: Bytes::new(METHOD_ANNOUNCE_PEER),
                t: Bytes::new(b"aa"),
                v: None,
            };
            let ser_msg =
                bt_bencode::to_vec(&ser_query_msg).map_err(|_| Error::is_deserialize_error())?;
            assert_eq!(ser_msg, announce_peer_query);
            Ok(())
        } else {
            panic!()
        }
    }

    #[test]
    fn test_serde_announce_peer_response_values() -> Result<(), Error> {
        let announce_peer_resp = b"d1:rd2:id20:0123456789abcdefghije1:t2:aa1:y1:re";

        let msg_value: Value = bt_bencode::from_slice(&announce_peer_resp[..])?;
        assert_eq!(msg_value.ty(), Some(Ty::Response));
        assert_eq!(msg_value.method_name(), None);
        assert_eq!(msg_value.method_name_str(), None);
        assert_eq!(msg_value.tx_id(), Some(b"aa".as_ref()));

        if let Some(values) = msg_value
            .values()
            .and_then(|a| RespValues::try_from(a).ok())
        {
            assert_eq!(values.id(), Id::from(*b"0123456789abcdefghij"));

            let resp_values = values.into();
            let ser_resp_msg = crate::dht::krpc::ser::RespMsg {
                r: Some(&resp_values),
                t: Bytes::new(b"aa"),
                v: None,
            };
            let ser_msg =
                bt_bencode::to_vec(&ser_resp_msg).map_err(|_| Error::is_deserialize_error())?;
            assert_eq!(ser_msg, announce_peer_resp);
            Ok(())
        } else {
            panic!()
        }
    }
}
