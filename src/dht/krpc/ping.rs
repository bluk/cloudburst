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

use core::convert::TryFrom;
use serde_derive::{Deserialize, Serialize};

use crate::dht::node::{Id, LocalId};

/// The "ping" query method name.
pub const METHOD_PING: &[u8] = b"ping";

/// The arguments for the ping query message.
#[derive(Debug, Deserialize, Serialize)]
pub struct QueryArgs<'a> {
    /// The querying node's ID
    #[serde(with = "serde_bytes")]
    pub id: &'a [u8],
}

impl<'a> QueryArgs<'a> {
    /// Constructs a new `QueryArgs` based on the local node ID.
    #[must_use]
    #[inline]
    pub fn new(id: &'a LocalId) -> Self {
        Self { id: &(id.0).0 }
    }

    /// Returns the querying node's ID.
    #[must_use]
    #[inline]
    pub fn id(&self) -> Option<Id> {
        Id::try_from(self.id).ok()
    }
}

/// The arguments for the ping query message.
#[derive(Debug, Deserialize, Serialize)]
pub struct RespValues<'a> {
    /// The queried node's ID
    #[serde(with = "serde_bytes")]
    pub id: &'a [u8],
}

impl<'a> RespValues<'a> {
    /// Constructs a new `RespValue` based on the local node ID.
    #[must_use]
    #[inline]
    pub fn new(id: &'a LocalId) -> Self {
        Self { id: &(id.0).0 }
    }

    /// Returns the queried node's ID.
    #[must_use]
    #[inline]
    pub fn id(&self) -> Option<Id> {
        Id::try_from(self.id).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::dht::krpc::{ser, Error, Msg, Ty};

    #[test]
    fn test_serde_ping_query() -> Result<(), Error> {
        let ping_query = b"d1:ad2:id20:abcdefghij0123456789e1:q4:ping1:t2:aa1:y1:qe";

        let msg: Msg<'_> = bt_bencode::from_slice(ping_query.as_slice())?;
        assert_eq!(msg.tx_id(), b"aa");
        assert_eq!(msg.ty(), Ty::Query);
        assert_eq!(msg.client_version(), None);
        assert_eq!(msg.method_name().unwrap(), METHOD_PING);
        assert_eq!(
            msg.method_name_str(),
            Some(core::str::from_utf8(METHOD_PING).unwrap())
        );

        let query_args: QueryArgs<'_> = msg.args().unwrap()?;
        assert_eq!(query_args.id(), Some(Id::from(*b"abcdefghij0123456789")));

        let ser_query_msg = ser::QueryMsg {
            t: b"aa".as_slice(),
            v: None,
            q: METHOD_PING,
            a: query_args,
        };
        let ser_msg = bt_bencode::to_vec(&ser_query_msg)?;
        assert_eq!(ser_msg, ping_query);

        Ok(())
    }

    #[test]
    fn test_serde_ping_response() -> Result<(), Error> {
        let ping_resp = b"d1:rd2:id20:mnopqrstuvwxyz123456e1:t2:aa1:y1:re";

        let msg: Msg<'_> = bt_bencode::from_slice(&ping_resp[..])?;
        assert_eq!(msg.tx_id(), b"aa");
        assert_eq!(msg.ty(), Ty::Response);
        assert_eq!(msg.client_version(), None);

        let resp_values: RespValues<'_> = msg.values().unwrap()?;
        assert_eq!(resp_values.id(), Some(Id::from(*b"mnopqrstuvwxyz123456")));

        let ser_resp_msg = ser::RespMsg {
            t: b"aa".as_slice(),
            v: None,
            r: &resp_values,
        };
        let ser_msg = bt_bencode::to_vec(&ser_resp_msg)?;
        assert_eq!(ser_msg, ping_resp);

        Ok(())
    }
}
