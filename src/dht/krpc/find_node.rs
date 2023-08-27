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

use core::convert::TryFrom;
use serde_bytes::Bytes;
use serde_derive::{Deserialize, Serialize};

use crate::dht::{
    krpc::{CompactAddrV4, CompactAddrV6, Error},
    node::{AddrId, Id, LocalId},
};

/// The `find_node` query method name.
pub const METHOD_FIND_NODE: &[u8] = b"find_node";

/// The arguments for the find node query message.
#[derive(Debug, Deserialize, Serialize)]
pub struct QueryArgs<'a> {
    /// The querying node's ID
    #[serde(borrow)]
    pub id: &'a Bytes,
    /// The target node's ID
    #[serde(borrow)]
    pub target: &'a Bytes,
}

impl<'a> QueryArgs<'a> {
    /// Instantiates a new query message with the local querying node Id and the target Id.
    #[must_use]
    #[inline]
    pub fn new(id: &'a LocalId, target: &'a Id) -> Self {
        Self {
            id: Bytes::new(&(id.0).0),
            target: Bytes::new(&target.0),
        }
    }

    /// Returns the querying node's ID.
    #[must_use]
    #[inline]
    pub fn id(&self) -> Option<Id> {
        Id::try_from(self.id.as_ref()).ok()
    }

    /// Returns the target node's ID.
    #[must_use]
    #[inline]
    pub fn target(&self) -> Option<Id> {
        Id::try_from(self.target.as_ref()).ok()
    }
}

/// The value for the find node response.
#[derive(Debug, Serialize, Deserialize)]
pub struct RespValues<'a> {
    /// The queried node's ID
    pub id: &'a Bytes,
    /// IPv4 nodes which may have relevant information
    #[serde(skip_serializing_if = "Option::is_none", borrow)]
    pub nodes: Option<&'a Bytes>,
    /// IPv6 nodes which may have relevant information
    #[serde(skip_serializing_if = "Option::is_none", borrow)]
    pub nodes6: Option<&'a Bytes>,
}

impl<'a> RespValues<'a> {
    /// Instantiates a new instance.
    #[must_use]
    #[inline]
    pub fn new(id: &'a LocalId, nodes: Option<&'a Bytes>, nodes6: Option<&'a Bytes>) -> Self {
        Self {
            id: Bytes::new(&(id.0).0),
            nodes,
            nodes6,
        }
    }

    /// Returns the queried node's ID.
    #[must_use]
    #[inline]
    pub fn id(&self) -> Option<Id> {
        Id::try_from(self.id.as_ref()).ok()
    }

    /// Returns IPv4 nodes which may have more relevant information for the torrent.
    #[must_use]
    #[inline]
    pub fn nodes(&self) -> Option<Result<impl Iterator<Item = AddrId<CompactAddrV4>> + 'a, Error>> {
        self.nodes.as_ref().map(|nodes| {
            if nodes.len() % 26 != 0 {
                return Err(Error::is_invalid_compact_addr());
            }

            Ok(nodes.chunks_exact(26).map(|bytes| {
                let (Ok(id), Ok(compact_addr)) = (
                    <[u8; 20]>::try_from(&bytes[..20]),
                    <[u8; 6]>::try_from(&bytes[20..]),
                ) else {
                    unreachable!()
                };
                AddrId::new(CompactAddrV4::from(compact_addr), Id::from(id))
            }))
        })
    }

    /// Returns IPv6 nodes which may have more relevant information for the torrent.
    #[must_use]
    #[inline]
    pub fn nodes6(
        &self,
    ) -> Option<Result<impl Iterator<Item = AddrId<CompactAddrV6>> + 'a, Error>> {
        self.nodes6.as_ref().map(|nodes| {
            if nodes.len() % 38 != 0 {
                return Err(Error::is_invalid_compact_addr());
            }

            Ok(nodes.chunks_exact(38).map(|bytes| {
                let (Ok(id), Ok(compact_addr)) = (
                    <[u8; 20]>::try_from(&bytes[..20]),
                    <[u8; 18]>::try_from(&bytes[20..]),
                ) else {
                    unreachable!()
                };
                AddrId::new(CompactAddrV6::from(compact_addr), Id::from(id))
            }))
        })
    }
}

#[cfg(test)]
mod tests {
    use serde_bytes::Bytes;

    use super::*;

    use crate::dht::krpc::{ser, Error, Msg, Ty};

    #[test]
    fn test_serde_find_node_query() -> Result<(), Error> {
        let find_node_query = b"d1:ad2:id20:abcdefghij01234567896:target20:mnopqrstuvwxyz123456e1:q9:find_node1:t2:aa1:y1:qe";

        let msg: Msg<'_> = bt_bencode::from_slice(find_node_query)?;
        assert_eq!(msg.tx_id(), b"aa".as_ref());
        assert_eq!(msg.ty(), Ty::Query);
        assert_eq!(msg.client_version(), None);
        assert_eq!(msg.method_name(), Some(METHOD_FIND_NODE));
        assert_eq!(
            msg.method_name_str(),
            Some(core::str::from_utf8(METHOD_FIND_NODE).unwrap())
        );

        let query_args: QueryArgs<'_> = msg.args().unwrap()?;
        assert_eq!(query_args.id(), Some(Id::from(*b"abcdefghij0123456789")));
        assert_eq!(
            query_args.target(),
            Some(Id::from(*b"mnopqrstuvwxyz123456"))
        );

        let ser_query_msg = ser::QueryMsg {
            a: query_args,
            q: Bytes::new(METHOD_FIND_NODE),
            t: Bytes::new(b"aa"),
            v: None,
        };
        let ser_msg = bt_bencode::to_vec(&ser_query_msg)?;
        assert_eq!(ser_msg, find_node_query);

        Ok(())
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_serde_find_node_response_values_one_node() -> Result<(), Error> {
        use crate::dht::node::IdAllocator;
        use std::net::{Ipv4Addr, SocketAddrV4};

        let addr = SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 1234);
        let compact_addr = CompactAddrV4::from(addr);
        let node_id = addr.ip().rand_id(None, &mut rand::thread_rng()).unwrap();
        let mut find_node_resp = vec![];
        find_node_resp.extend_from_slice(b"d1:rd2:id20:0123456789abcdefghij5:nodes26:");
        find_node_resp.extend_from_slice(node_id.as_ref());
        find_node_resp.extend_from_slice(compact_addr.as_ref());
        find_node_resp.extend_from_slice(b"e1:t2:aa1:y1:re");

        let msg: Msg<'_> = bt_bencode::from_slice(&find_node_resp)?;
        assert_eq!(msg.tx_id(), b"aa");
        assert_eq!(msg.ty(), Ty::Response);
        assert_eq!(msg.client_version(), None);

        let resp_values: RespValues<'_> = msg.values().unwrap()?;
        assert_eq!(resp_values.id(), Some(Id::from(*b"0123456789abcdefghij")));
        assert_eq!(
            resp_values.nodes().unwrap().unwrap().collect::<Vec<_>>(),
            vec![AddrId::new(compact_addr, node_id)]
        );
        assert!(resp_values.nodes6().is_none());

        let ser_resp_msg = ser::RespMsg {
            r: &resp_values,
            t: Bytes::new(b"aa"),
            v: None,
        };
        let ser_msg = bt_bencode::to_vec(&ser_resp_msg)?;
        assert_eq!(ser_msg, find_node_resp);

        Ok(())
    }
}
