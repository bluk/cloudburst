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

use core::convert::TryFrom;
use serde_bytes::Bytes;
use serde_derive::{Deserialize, Serialize};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::vec::Vec;

use crate::{
    dht::{
        krpc::{CompactAddr, CompactAddrV4, CompactAddrV6},
        node::{AddrId, Id, LocalId},
    },
    metainfo::InfoHash,
};

use super::{Error, ErrorKind};

/// The `get_peers` query method name.
pub const METHOD_GET_PEERS: &[u8] = b"get_peers";

/// The arguments for the get peers query message.
#[derive(Debug, Deserialize, Serialize)]
pub struct QueryArgs<'a> {
    /// The querying node's ID
    #[serde(borrow)]
    pub id: &'a Bytes,
    /// The `InfoHash` associated with the torrent
    #[serde(borrow)]
    pub info_hash: &'a Bytes,
}

impl<'a> QueryArgs<'a> {
    /// Instantiates a new query message.
    #[must_use]
    #[inline]
    pub fn new(id: &'a LocalId, info_hash: &'a InfoHash) -> Self {
        Self {
            id: Bytes::new(&(id.0).0),
            info_hash: Bytes::new(&info_hash.0),
        }
    }

    /// Returns the querying node's ID.
    #[must_use]
    #[inline]
    pub fn id(&self) -> Option<Id> {
        Id::try_from(self.id.as_ref()).ok()
    }

    /// Returns the `InfoHash` for the relevant torrent.
    #[must_use]
    #[inline]
    pub fn info_hash(&self) -> Option<InfoHash> {
        InfoHash::try_from(self.info_hash.as_ref()).ok()
    }
}

/// The value for the get peers response.
#[derive(Debug, Serialize, Deserialize)]
pub struct RespValues<'a, V> {
    /// The queried node's ID
    #[serde(borrow)]
    pub id: &'a Bytes,
    /// IPv4 nodes which may have relevant information
    #[serde(skip_serializing_if = "Option::is_none", borrow)]
    pub nodes: Option<&'a Bytes>,
    /// IPv6 nodes which may have relevant information
    #[serde(skip_serializing_if = "Option::is_none", borrow)]
    pub nodes6: Option<&'a Bytes>,
    /// An opaque token which can be used in an announce peer message.
    #[serde(borrow)]
    pub token: &'a Bytes,
    /// Peer compact addresses
    #[serde(skip_serializing_if = "Option::is_none")]
    pub values: Option<V>,
}

impl<'a, V> RespValues<'a, V> {
    /// Instantiates a new instance.
    #[must_use]
    #[inline]
    pub fn new(
        id: &'a LocalId,
        token: &'a Bytes,
        values: Option<V>,
        nodes: Option<&'a Bytes>,
        nodes6: Option<&'a Bytes>,
    ) -> Self {
        Self {
            id: Bytes::new(&(id.0).0),
            token,
            values,
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

    /// Returns the token which is used by the queried node for verification.
    #[must_use]
    #[inline]
    pub fn token(&self) -> &[u8] {
        self.token
    }

    /// Returns IPv4 nodes which may have more relevant information for the torrent.
    #[must_use]
    #[inline]
    pub fn nodes(&self) -> Option<Result<impl Iterator<Item = AddrId<CompactAddrV4>> + 'a, Error>> {
        self.nodes.as_ref().map(|nodes| {
            if nodes.len() % 26 != 0 {
                return Err(Error {
                    kind: ErrorKind::InvalidCompactAddr,
                });
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
                return Err(Error {
                    kind: ErrorKind::InvalidCompactAddr,
                });
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

impl<'a> RespValues<'a, Vec<&'a Bytes>> {
    /// Returns peers' socket addresses for the torrent.
    #[must_use]
    #[inline]
    pub fn values(&'a self) -> Option<impl Iterator<Item = CompactAddr> + 'a> {
        self.values.as_ref().map(|values| {
            values.iter().filter_map(|&v| match v.len() {
                6 => <[u8; 6]>::try_from(v.as_ref())
                    .ok()
                    .map(CompactAddrV4::from)
                    .map(CompactAddr::from),
                18 => <[u8; 18]>::try_from(v.as_ref())
                    .ok()
                    .map(CompactAddrV6::from)
                    .map(CompactAddr::from),
                _ => None,
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use bt_bencode::Error;
    use serde_bytes::Bytes;

    use super::*;

    use crate::dht::krpc::{ser, Msg, Ty};

    #[test]
    fn test_serde_get_peers_query() -> Result<(), Error> {
        let get_peers_query = b"d1:ad2:id20:abcdefghij01234567899:info_hash20:mnopqrstuvwxyz123456e1:q9:get_peers1:t2:aa1:y1:qe";

        let msg: Msg<'_> = bt_bencode::from_slice(get_peers_query)?;
        assert_eq!(msg.tx_id(), b"aa");
        assert_eq!(msg.ty(), Ty::Query);
        assert_eq!(msg.client_version(), None);
        assert_eq!(msg.method_name().unwrap(), METHOD_GET_PEERS);
        assert_eq!(
            msg.method_name_str(),
            Some(core::str::from_utf8(METHOD_GET_PEERS).unwrap())
        );

        let query_args: QueryArgs<'_> = msg.args().unwrap()?;
        assert_eq!(query_args.id(), Some(Id::from(*b"abcdefghij0123456789")));
        assert_eq!(
            query_args.info_hash(),
            Some(InfoHash::from(*b"mnopqrstuvwxyz123456"))
        );

        let ser_query_msg = ser::QueryMsg {
            t: Bytes::new(b"aa"),
            v: None,
            q: Bytes::new(METHOD_GET_PEERS),
            a: query_args,
        };
        let ser_msg = bt_bencode::to_vec(&ser_query_msg)?;
        assert_eq!(ser_msg, get_peers_query);

        Ok(())
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_serde_get_peers_response_values_one_node_borrowed() -> Result<(), Error> {
        use crate::dht::node::IdAllocator;
        use std::net::{Ipv4Addr, SocketAddrV4};

        let addr = SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 1234);
        let compact_addr = CompactAddrV4::from(addr);
        let node_id = addr.ip().rand_id(None, &mut rand::thread_rng()).unwrap();
        let mut get_peers_resp = vec![];
        get_peers_resp.extend_from_slice(b"d1:rd2:id20:0123456789abcdefghij5:nodes26:");
        get_peers_resp.extend_from_slice(node_id.as_ref());
        get_peers_resp.extend_from_slice(compact_addr.as_ref());
        get_peers_resp.extend_from_slice(b"5:token8:12345678e1:t2:aa1:y1:re");

        let msg: Msg<'_> = bt_bencode::from_slice(&get_peers_resp)?;
        assert_eq!(msg.tx_id(), b"aa");
        assert_eq!(msg.ty(), Ty::Response);
        assert_eq!(msg.client_version(), None);

        let resp_values: RespValues<'_, Vec<&'_ Bytes>> = msg.values().unwrap()?;
        assert_eq!(resp_values.id(), Some(Id::from(*b"0123456789abcdefghij")));
        assert!(resp_values.values().is_none());
        assert_eq!(
            resp_values.nodes().unwrap().unwrap().collect::<Vec<_>>(),
            vec![AddrId::new(compact_addr, node_id)]
        );
        assert!(resp_values.nodes6().is_none());

        let ser_resp_msg = ser::RespMsg {
            t: Bytes::new(b"aa"),
            v: None,
            r: &resp_values,
        };
        let ser_msg = bt_bencode::to_vec(&ser_resp_msg)?;
        assert_eq!(ser_msg, get_peers_resp);

        Ok(())
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_serde_get_peers_response_values_compact_addr() -> Result<(), Error> {
        use core::str::FromStr;
        use std::net::{Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6};

        let compact_addr_v4 =
            CompactAddrV4::from(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 1234));
        let compact_addr_v6 = CompactAddrV6::from(SocketAddrV6::new(
            Ipv6Addr::from_str("2001:0db8:0001:0000:0000:8a2e:0370:7335").unwrap(),
            1234,
            0,
            0,
        ));
        let values: Vec<CompactAddr> = vec![compact_addr_v4.into(), compact_addr_v6.into()];

        let resp_values: RespValues<'_, Vec<CompactAddr>> = RespValues {
            id: Bytes::new(b"0123456789abcdefghij"),
            nodes: None,
            nodes6: None,
            token: Bytes::new(b"abcd1234"),
            values: Some(values),
        };

        let ser_resp_msg = ser::RespMsg {
            t: Bytes::new(b"aa"),
            v: None,
            r: &resp_values,
        };
        let ser_msg = bt_bencode::to_vec(&ser_resp_msg)?;

        let msg: Msg<'_> = bt_bencode::from_slice(&ser_msg)?;
        assert_eq!(msg.tx_id(), b"aa");
        assert_eq!(msg.ty(), Ty::Response);
        assert_eq!(msg.client_version(), None);

        let resp_values: RespValues<'_, Vec<&'_ Bytes>> = msg.values().unwrap().unwrap();
        assert_eq!(resp_values.id(), Some(Id::from(*b"0123456789abcdefghij")));
        assert_eq!(
            resp_values.values().unwrap().collect::<Vec<_>>(),
            vec![compact_addr_v4.into(), compact_addr_v6.into()]
        );
        assert!(resp_values.nodes().is_none());
        assert!(resp_values.nodes6().is_none());

        let resp_values: RespValues<'_, Vec<CompactAddr>> = msg.values().unwrap().unwrap();
        assert_eq!(resp_values.id(), Some(Id::from(*b"0123456789abcdefghij")));
        assert_eq!(
            resp_values.values,
            Some(vec![compact_addr_v4.into(), compact_addr_v6.into()])
        );
        assert!(resp_values.nodes().is_none());
        assert!(resp_values.nodes6().is_none());

        Ok(())
    }
}
