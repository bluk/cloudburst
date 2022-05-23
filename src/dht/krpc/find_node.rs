// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Finds nodes in the distributed hash table.
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
use std::{
    collections::BTreeMap,
    net::{SocketAddrV4, SocketAddrV6},
    string::String,
};

#[cfg(feature = "std")]
use crate::dht::{
    krpc::{CompactAddrV4Info, CompactAddrV6Info},
    node::AddrId,
};

use crate::dht::node::{Id, LocalId};

/// The `find_node` query method name.
pub const METHOD_FIND_NODE: &[u8] = b"find_node";

/// The arguments for the find node query message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QueryArgs {
    id: Id,
    target: Id,
}

impl QueryArgs {
    /// Instantiates a new query message with the local querying node Id and the target Id.
    #[must_use]
    #[inline]
    pub const fn new(id: LocalId, target: Id) -> Self {
        Self {
            id: Id::new((id.0).0),
            target,
        }
    }

    /// Sets the querying node ID in the arguments.
    #[inline]
    pub fn set_id(&mut self, id: LocalId) {
        self.id = Id::new((id.0).0);
    }

    /// Returns the target Id.
    #[must_use]
    #[inline]
    pub const fn target(&self) -> Id {
        self.target
    }

    /// Sets the target Id.
    #[inline]
    pub fn set_target(&mut self, target: Id) {
        self.target = target;
    }
}

impl crate::dht::krpc::QueryArgs for QueryArgs {
    fn method_name() -> &'static [u8] {
        METHOD_FIND_NODE
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
        match (
            args.get(Bytes::new(b"id"))
                .and_then(bt_bencode::Value::as_byte_str)
                .and_then(|id| Id::try_from(id.as_slice()).ok()),
            args.get(Bytes::new(b"target"))
                .and_then(bt_bencode::Value::as_byte_str)
                .and_then(|t| Id::try_from(t.as_slice()).ok()),
        ) {
            (Some(id), Some(target)) => Ok(QueryArgs { id, target }),
            _ => Err(crate::dht::krpc::Error::is_deserialize_error()),
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
            ByteBuf::from(String::from("target")),
            Value::ByteStr(ByteBuf::from(args.target)),
        );
        Value::Dict(d)
    }
}

/// The value for the find node response.
#[cfg(feature = "std")]
#[derive(Debug)]
pub struct RespValues {
    id: Id,
    nodes: Option<Vec<AddrId<SocketAddrV4>>>,
    nodes6: Option<Vec<AddrId<SocketAddrV6>>>,
}

#[cfg(feature = "std")]
impl RespValues {
    /// Instantiates a new instance.
    #[must_use]
    #[inline]
    pub const fn with_id_and_nodes_and_nodes6(
        id: LocalId,
        nodes: Option<Vec<AddrId<SocketAddrV4>>>,
        nodes6: Option<Vec<AddrId<SocketAddrV6>>>,
    ) -> Self {
        Self {
            id: Id::new((id.0).0),
            nodes,
            nodes6,
        }
    }

    /// Sets the queried node Id.
    #[inline]
    pub fn set_id(&mut self, id: Id) {
        self.id = id;
    }

    /// Returns the IPv4 nodes.
    #[must_use]
    #[inline]
    pub const fn nodes(&self) -> Option<&Vec<AddrId<SocketAddrV4>>> {
        self.nodes.as_ref()
    }

    /// Sets the IPv4 nodes.
    #[inline]
    pub fn set_nodes(&mut self, nodes: Option<Vec<AddrId<SocketAddrV4>>>) {
        self.nodes = nodes;
    }

    /// Returns the IPv6 nodes.
    #[must_use]
    #[inline]
    pub const fn nodes6(&self) -> Option<&Vec<AddrId<SocketAddrV6>>> {
        self.nodes6.as_ref()
    }

    /// Sets the IPv6 nodes.
    #[inline]
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
    type Error = crate::dht::krpc::Error;

    fn try_from(values: &BTreeMap<ByteBuf, Value>) -> Result<Self, Self::Error> {
        match (
            values
                .get(Bytes::new(b"id"))
                .and_then(bt_bencode::Value::as_byte_str)
                .and_then(|id| Id::try_from(id.as_slice()).ok()),
            values
                .get(Bytes::new(b"nodes"))
                .and_then(bt_bencode::Value::as_byte_str)
                .map(super::decode_addr_ipv4_list),
            values
                .get(Bytes::new(b"nodes6"))
                .and_then(bt_bencode::Value::as_byte_str)
                .map(super::decode_addr_ipv6_list),
        ) {
            (Some(id), nodes, nodes6) => {
                let nodes = nodes.transpose()?;
                let nodes6 = nodes6.transpose()?;
                Ok(RespValues { id, nodes, nodes6 })
            }
            _ => Err(crate::dht::krpc::Error::is_deserialize_error()),
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

        Value::Dict(args)
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use serde_bytes::Bytes;

    use super::*;

    use crate::dht::krpc::{Error, Msg, QueryArgs, QueryMsg, RespMsg, RespVal, Ty};

    #[test]
    fn test_serde_find_node_query() -> Result<(), Error> {
        let find_node_query = b"d1:ad2:id20:abcdefghij01234567896:target20:mnopqrstuvwxyz123456e1:q9:find_node1:t2:aa1:y1:qe";

        let msg_value: Value = bt_bencode::from_slice(&find_node_query[..])?;
        assert_eq!(msg_value.ty(), Some(Ty::Query));
        assert_eq!(msg_value.method_name(), Some(METHOD_FIND_NODE));
        assert_eq!(
            msg_value.method_name_str(),
            Some(core::str::from_utf8(METHOD_FIND_NODE).unwrap())
        );
        assert_eq!(msg_value.tx_id(), Some(b"aa".as_ref()));
        if let Some(args) = msg_value
            .args()
            .and_then(|a| crate::dht::krpc::find_node::QueryArgs::try_from(a).ok())
        {
            assert_eq!(args.id(), Id::from(*b"abcdefghij0123456789"));
            assert_eq!(args.target(), Id::from(*b"mnopqrstuvwxyz123456"));

            let args_value = args.into();
            let ser_query_msg = crate::dht::krpc::ser::QueryMsg {
                a: Some(&args_value),
                q: Bytes::new(METHOD_FIND_NODE),
                t: Bytes::new(b"aa"),
                v: None,
            };
            let ser_msg =
                bt_bencode::to_vec(&ser_query_msg).map_err(|_| Error::is_deserialize_error())?;
            assert_eq!(ser_msg, find_node_query);
            Ok(())
        } else {
            panic!()
        }
    }

    #[test]
    fn test_serde_find_node_response_values_one_node() -> Result<(), Error> {
        use crate::dht::node::IdAllocator;
        use std::net::Ipv4Addr;

        let addr = SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 1234);
        let compact_addr = addr.to_compact_addr();
        let node_id = addr.ip().rand_id(None, &mut rand::thread_rng()).unwrap();
        let mut find_node_resp = vec![];
        find_node_resp.extend_from_slice(b"d1:rd2:id20:0123456789abcdefghij5:nodes26:");
        find_node_resp.extend_from_slice(node_id.as_ref());
        find_node_resp.extend_from_slice(&compact_addr[..]);
        find_node_resp.extend_from_slice(b"e1:t2:aa1:y1:re");

        let msg_value: Value = bt_bencode::from_slice(&find_node_resp[..])?;
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
            assert_eq!(ser_msg, find_node_resp);
            Ok(())
        } else {
            panic!()
        }
    }
}
