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

use core::convert::TryFrom;
use serde_bytes::Bytes;
use serde_derive::{Deserialize, Serialize};

use crate::{
    dht::node::{Id, LocalId},
    metainfo::InfoHash,
};

/// The `announce_peer` query method name.
pub const METHOD_ANNOUNCE_PEER: &[u8] = b"announce_peer";

/// The arguments for the announce peer query message.
#[derive(Debug, Deserialize, Serialize)]
pub struct QueryArgs<'a> {
    /// The querying node's ID
    #[serde(borrow)]
    pub id: &'a Bytes,
    /// The `InfoHash` associated with the torrent
    #[serde(borrow)]
    pub info_hash: &'a Bytes,
    /// Opaque token received from a [`crate::dht::krpc::get_peers::RespValues`] to authenticate the announce.
    #[serde(borrow)]
    pub token: &'a Bytes,
    /// The port listened on
    #[serde(skip_serializing_if = "Option::is_none")]
    pub port: Option<u16>,
    /// If the node is behind a DHT, a "true" implied port value (`Some(non-zero)`) indicates to use the port from the received message.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub implied_port: Option<u8>,
}

impl<'a> QueryArgs<'a> {
    /// Instantiates a new query message.
    #[must_use]
    #[inline]
    pub fn new(
        id: &'a LocalId,
        info_hash: &'a InfoHash,
        token: &'a Bytes,
        port: Option<u16>,
        implied_port: Option<bool>,
    ) -> Self {
        Self {
            id: Bytes::new(&(id.0).0),
            info_hash: Bytes::new(&info_hash.0),
            token,
            port,
            implied_port: implied_port.map(u8::from),
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

    /// Returns the token which is used by the queried node for verification.
    #[must_use]
    #[inline]
    pub fn token(&self) -> &[u8] {
        self.token
    }

    /// Returns if the port should be implied from the querying node's DHT sending port.
    #[must_use]
    #[inline]
    pub fn implied_port(&self) -> Option<bool> {
        self.implied_port.map(|v| v != 0)
    }
}

/// The value for the announce peer response.
#[derive(Debug, Serialize, Deserialize)]
pub struct RespValues<'a> {
    /// The queried node's ID
    #[serde(borrow)]
    pub id: &'a Bytes,
}

impl<'a> RespValues<'a> {
    /// Instantiates a new instance.
    #[must_use]
    #[inline]
    pub fn new(id: &'a LocalId) -> Self {
        Self {
            id: Bytes::new(&(id.0).0),
        }
    }

    /// Returns the queried node's ID.
    #[must_use]
    #[inline]
    pub fn id(&self) -> Option<Id> {
        Id::try_from(self.id.as_ref()).ok()
    }
}

#[cfg(test)]
mod tests {
    use serde_bytes::Bytes;

    use super::*;

    use crate::dht::krpc::{ser, Error, Msg, Ty};

    #[test]
    fn test_serde_announce_peer_query() -> Result<(), Error> {
        let announce_peer_query = b"d1:ad2:id20:abcdefghij01234567899:info_hash20:mnopqrstuvwxyz1234564:porti6331e5:token8:abcd1234e1:q13:announce_peer1:t2:aa1:y1:qe";

        let msg: Msg<'_> = bt_bencode::from_slice(announce_peer_query)?;
        assert_eq!(msg.tx_id(), b"aa");
        assert_eq!(msg.ty(), Ty::Query);
        assert_eq!(msg.client_version(), None);
        assert_eq!(msg.method_name(), Some(METHOD_ANNOUNCE_PEER));
        assert_eq!(
            msg.method_name_str(),
            Some(core::str::from_utf8(METHOD_ANNOUNCE_PEER).unwrap())
        );

        let query_args: QueryArgs<'_> = msg.args().unwrap()?;
        assert_eq!(query_args.id(), Some(Id::from(*b"abcdefghij0123456789")));
        assert_eq!(
            query_args.info_hash(),
            Some(InfoHash::from(*b"mnopqrstuvwxyz123456"))
        );
        assert_eq!(query_args.token, b"abcd1234");
        assert_eq!(query_args.port, Some(6331));
        assert_eq!(query_args.implied_port(), None);

        let ser_query_msg = ser::QueryMsg {
            t: Bytes::new(b"aa"),
            v: None,
            q: Bytes::new(METHOD_ANNOUNCE_PEER),
            a: query_args,
        };
        let ser_msg = bt_bencode::to_vec(&ser_query_msg)?;
        assert_eq!(ser_msg, announce_peer_query);

        Ok(())
    }

    #[test]
    fn test_serde_announce_peer_response_values() -> Result<(), Error> {
        let announce_peer_resp = b"d1:rd2:id20:0123456789abcdefghije1:t2:aa1:y1:re";

        let msg: Msg<'_> = bt_bencode::from_slice(announce_peer_resp)?;
        assert_eq!(msg.tx_id(), b"aa");
        assert_eq!(msg.ty(), Ty::Response);
        assert_eq!(msg.client_version(), None);

        let resp_values: RespValues<'_> = msg.values().unwrap()?;
        assert_eq!(resp_values.id(), Some(Id::from(*b"0123456789abcdefghij")));

        let ser_resp_msg = ser::RespMsg {
            t: Bytes::new(b"aa"),
            v: None,
            r: &resp_values,
        };
        let ser_msg = bt_bencode::to_vec(&ser_resp_msg)?;
        assert_eq!(ser_msg, announce_peer_resp);

        Ok(())
    }
}
