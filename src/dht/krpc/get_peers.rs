// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Gets peers for a torrent.
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
use crate::dht::{
    krpc::{CompactAddrV4Info, CompactAddrV6Info},
    node::AddrId,
};
#[cfg(feature = "std")]
use std::{
    collections::BTreeMap,
    net::{SocketAddr, SocketAddrV4, SocketAddrV6},
    string::String,
    vec,
    vec::Vec,
};

use crate::{
    dht::{
        krpc::Error,
        node::{Id, LocalId},
    },
    metainfo::InfoHash,
};

/// The `get_peers` query method name.
pub const METHOD_GET_PEERS: &[u8] = b"get_peers";

/// The arguments for the get peers query message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QueryArgs {
    id: Id,
    info_hash: InfoHash,
}

impl QueryArgs {
    /// Instantiates a new query message.
    pub fn new<L>(id: L, info_hash: InfoHash) -> Self
    where
        L: Into<LocalId>,
    {
        Self {
            id: Id::from(id.into()),
            info_hash,
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
}

impl crate::dht::krpc::QueryArgs for QueryArgs {
    fn method_name() -> &'static [u8] {
        METHOD_GET_PEERS
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
            args.get(Bytes::new("info_hash".as_bytes()))
                .and_then(bt_bencode::Value::as_byte_str)
                .and_then(|t| InfoHash::try_from(t.as_slice()).ok()),
        ) {
            (Some(id), Some(info_hash)) => Ok(QueryArgs { id, info_hash }),
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
        d.insert(
            ByteBuf::from(String::from("info_hash")),
            Value::ByteStr(ByteBuf::from(args.info_hash)),
        );
        Value::Dict(d)
    }
}

/// The value for the get peers response.
#[cfg(feature = "std")]
#[derive(Debug)]
pub struct RespValues {
    id: Id,
    token: Vec<u8>,
    values: Option<Vec<SocketAddr>>,
    nodes: Option<Vec<AddrId<SocketAddrV4>>>,
    nodes6: Option<Vec<AddrId<SocketAddrV6>>>,
}

#[cfg(feature = "std")]
impl RespValues {
    /// Instantiates a new instance.
    pub fn new<L>(
        id: L,
        token: Vec<u8>,
        values: Option<Vec<SocketAddr>>,
        nodes: Option<Vec<AddrId<SocketAddrV4>>>,
        nodes6: Option<Vec<AddrId<SocketAddrV6>>>,
    ) -> Self
    where
        L: Into<LocalId>,
    {
        Self {
            id: Id::from(id.into()),
            token,
            values,
            nodes,
            nodes6,
        }
    }

    /// Sets the queried node Id.
    pub fn set_id<I>(&mut self, id: I)
    where
        I: Into<LocalId>,
    {
        self.id = Id::from(id.into());
    }

    /// Returns an opaque token which can be used in an announce peer message.
    #[must_use]
    pub fn token(&self) -> &[u8] {
        &self.token
    }

    /// Sets an opaque token which can be used in an announce peer message.
    pub fn set_token(&mut self, token: Vec<u8>) {
        self.token = token;
    }

    /// Returns peers' socket addresses for the torrent.
    #[must_use]
    pub fn values(&self) -> Option<&Vec<SocketAddr>> {
        self.values.as_ref()
    }

    /// Sets peers' socket addresses for the torrent.
    pub fn set_values(&mut self, values: Option<Vec<SocketAddr>>) {
        self.values = values;
    }

    /// Returns IPv4 nodes which may have more relevant information for the torrent.
    #[must_use]
    pub fn nodes(&self) -> Option<&Vec<AddrId<SocketAddrV4>>> {
        self.nodes.as_ref()
    }

    /// Sets IPv4 nodes which may have more relevant information for the torrent.
    pub fn set_nodes(&mut self, nodes: Option<Vec<AddrId<SocketAddrV4>>>) {
        self.nodes = nodes;
    }

    /// Returns IPv6 nodes which may have more relevant information for the torrent.
    #[must_use]
    pub fn nodes6(&self) -> Option<&Vec<AddrId<SocketAddrV6>>> {
        self.nodes6.as_ref()
    }

    /// Sets IPv6 nodes which may have more relevant information for the torrent.
    pub fn set_nodes6(&mut self, nodes6: Option<Vec<AddrId<SocketAddrV6>>>) {
        self.nodes6 = nodes6;
    }
}

#[cfg(feature = "std")]
impl crate::dht::krpc::RespVal for RespValues {
    fn id(&self) -> Id {
        self.id
    }

    fn to_value(&self) -> Value {
        Value::from(self)
    }
}

#[cfg(feature = "std")]
impl TryFrom<&BTreeMap<ByteBuf, Value>> for RespValues {
    type Error = Error;

    fn try_from(values: &BTreeMap<ByteBuf, Value>) -> Result<Self, Self::Error> {
        match (
            values
                .get(Bytes::new(b"id"))
                .and_then(bt_bencode::Value::as_byte_str)
                .and_then(|id| Id::try_from(id.as_slice()).ok()),
            values
                .get(Bytes::new(b"token"))
                .and_then(|id| id.as_byte_str().cloned()),
            values
                .get(Bytes::new(b"values"))
                .and_then(bt_bencode::Value::as_array)
                .map(|values| {
                    values
                        .iter()
                        .map(|v| {
                            if let Some(v) = v.as_byte_str() {
                                match v.len() {
                                    6 => {
                                        let mut compact_addr: [u8; 6] = [0; 6];
                                        compact_addr.copy_from_slice(&v.as_slice()[0..6]);
                                        Ok(SocketAddr::V4(SocketAddrV4::from_compact_addr(
                                            compact_addr,
                                        )))
                                    }
                                    18 => {
                                        let mut compact_addr: [u8; 18] = [0; 18];
                                        compact_addr.copy_from_slice(&v.as_slice()[0..18]);
                                        Ok(SocketAddr::V6(SocketAddrV6::from_compact_addr(
                                            compact_addr,
                                        )))
                                    }
                                    _ => Err(Error::is_invalid_compact_addr()),
                                }
                            } else {
                                Err(Error::is_invalid_compact_addr())
                            }
                        })
                        .collect::<Result<Vec<SocketAddr>, Error>>()
                }),
            values
                .get(Bytes::new(b"nodes"))
                .and_then(bt_bencode::Value::as_byte_str)
                .map(super::decode_addr_ipv4_list),
            values
                .get(Bytes::new(b"nodes6"))
                .and_then(bt_bencode::Value::as_byte_str)
                .map(super::decode_addr_ipv6_list),
        ) {
            (Some(id), Some(token), values, nodes, nodes6) => {
                let values = values.transpose()?;
                let nodes = nodes.transpose()?;
                let nodes6 = nodes6.transpose()?;

                Ok(RespValues {
                    id,
                    token: token.into_vec(),
                    values,
                    nodes,
                    nodes6,
                })
            }
            _ => Err(Error::is_deserialize_error()),
        }
    }
}

#[cfg(feature = "std")]
impl From<RespValues> for Value {
    fn from(values: RespValues) -> Self {
        Value::from(&values)
    }
}

#[cfg(feature = "std")]
impl From<&RespValues> for Value {
    fn from(values: &RespValues) -> Self {
        let mut args: BTreeMap<ByteBuf, Value> = BTreeMap::new();
        args.insert(
            ByteBuf::from(String::from("id")),
            Value::ByteStr(ByteBuf::from(values.id)),
        );

        if let Some(nodes) = &values.nodes {
            let mut byte_str: Vec<u8> = vec![];
            for n in nodes {
                byte_str.extend_from_slice(n.id().as_ref());
                byte_str.extend_from_slice(&n.addr().to_compact_addr());
            }
            args.insert(
                ByteBuf::from(String::from("nodes")),
                Value::ByteStr(ByteBuf::from(byte_str)),
            );
        }

        if let Some(nodes6) = &values.nodes6 {
            let mut byte_str: Vec<u8> = vec![];
            for n in nodes6 {
                byte_str.extend_from_slice(n.id().as_ref());
                byte_str.extend_from_slice(&n.addr().to_compact_addr());
            }
            args.insert(
                ByteBuf::from(String::from("nodes6")),
                Value::ByteStr(ByteBuf::from(byte_str)),
            );
        }

        args.insert(
            ByteBuf::from(String::from("token")),
            Value::ByteStr(ByteBuf::from(values.token.clone())),
        );

        if let Some(values) = &values.values {
            args.insert(
                ByteBuf::from(String::from("values")),
                Value::List(
                    values
                        .iter()
                        .map(|addr| {
                            Value::ByteStr(match addr {
                                SocketAddr::V4(addr) => ByteBuf::from(addr.to_compact_addr()),
                                SocketAddr::V6(addr) => ByteBuf::from(addr.to_compact_addr()),
                            })
                        })
                        .collect::<Vec<Value>>(),
                ),
            );
        }

        Value::Dict(args)
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use serde_bytes::Bytes;

    use super::*;

    use crate::dht::krpc::{Msg, QueryArgs, QueryMsg, RespMsg, RespVal, Ty};

    #[test]
    fn test_serde_get_peers_query() -> Result<(), Error> {
        let get_peers_query = b"d1:ad2:id20:abcdefghij01234567899:info_hash20:mnopqrstuvwxyz123456e1:q9:get_peers1:t2:aa1:y1:qe";

        let msg_value: Value = bt_bencode::from_reader(&get_peers_query[..])?;
        assert_eq!(msg_value.ty(), Some(Ty::Query));
        assert_eq!(msg_value.method_name(), Some(METHOD_GET_PEERS));
        assert_eq!(
            msg_value.method_name_str(),
            Some(core::str::from_utf8(METHOD_GET_PEERS).unwrap())
        );
        assert_eq!(msg_value.tx_id(), Some(b"aa".as_ref()));
        if let Some(args) = msg_value
            .args()
            .and_then(|a| crate::dht::krpc::get_peers::QueryArgs::try_from(a).ok())
        {
            assert_eq!(args.id(), Id::from(*b"abcdefghij0123456789"));
            assert_eq!(args.info_hash(), InfoHash::from(*b"mnopqrstuvwxyz123456"));

            let args_value = args.into();
            let ser_query_msg = crate::dht::krpc::ser::QueryMsg {
                a: Some(&args_value),
                q: Bytes::new(METHOD_GET_PEERS),
                t: Bytes::new(b"aa"),
                v: None,
            };
            let ser_msg =
                bt_bencode::to_vec(&ser_query_msg).map_err(|_| Error::is_deserialize_error())?;
            assert_eq!(ser_msg, get_peers_query);
            Ok(())
        } else {
            panic!()
        }
    }

    #[test]
    fn test_serde_get_peers_response_values_one_node() -> Result<(), Error> {
        use crate::dht::node::IdAllocator;
        use std::net::Ipv4Addr;

        let addr = SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 1234);
        let compact_addr = addr.to_compact_addr();
        let node_id = addr.ip().rand_id(None, &mut rand::thread_rng()).unwrap();
        let mut get_peers_resp = vec![];
        get_peers_resp.extend_from_slice(b"d1:rd2:id20:0123456789abcdefghij5:nodes26:");
        get_peers_resp.extend_from_slice(node_id.as_ref());
        get_peers_resp.extend_from_slice(&compact_addr[..]);
        get_peers_resp.extend_from_slice(b"5:token8:12345678e1:t2:aa1:y1:re");

        let msg_value: Value = bt_bencode::from_reader(&get_peers_resp[..])?;
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
            assert_eq!(ser_msg, get_peers_resp);
            Ok(())
        } else {
            panic!()
        }
    }
}
