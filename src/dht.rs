// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Distributed hash table.
//!
//! The distributed hash table is a source of information for torrents. It can be
//! used to find peers for a torrent or even the metainfo given an identifying
//! hash value.

pub mod krpc;
pub mod node;
pub mod routing;
