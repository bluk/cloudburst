// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bt_bencode::Value;
use cloudburst::metainfo::{MetaVersion, Metainfo};

const TORRENT_BYTES: &[u8] = include_bytes!("ubuntu-20.04.4-live-server-amd64.iso.torrent");

#[test]
fn test_info_hash() -> Result<(), bt_bencode::Error> {
    let metainfo: Value = bt_bencode::from_slice(TORRENT_BYTES)?;

    let info = metainfo.get("info").expect("info value to exist");

    let info_hash =
        cloudburst::metainfo::InfoHash::with_value_and_meta_version(info, MetaVersion::V1)?;
    assert_eq!(
        info_hash,
        cloudburst::metainfo::InfoHash::from([
            0xb4, 0x4a, 0x0e, 0x20, 0xfa, 0x5b, 0x7c, 0xec, 0xb7, 0x71, 0x56, 0x33, 0x3b, 0x42,
            0x68, 0xdf, 0xd7, 0xc3, 0x0a, 0xfb,
        ])
    );

    Ok(())
}

#[test]
fn test_deserialize_torrent_file_via_type() -> Result<(), bt_bencode::Error> {
    let metainfo: Metainfo = bt_bencode::from_slice(TORRENT_BYTES)?;
    #[cfg(feature = "std")]
    cloudburst::metainfo::validation::check(&metainfo).unwrap();

    // dbg!(&metainfo);

    assert_eq!(
        metainfo.announce,
        Some("https://torrent.ubuntu.com/announce")
    );
    assert_eq!(
        metainfo.announce_list,
        Some(vec![
            vec!["https://torrent.ubuntu.com/announce"],
            vec!["https://ipv6.torrent.ubuntu.com/announce"]
        ])
    );
    assert_eq!(metainfo.comment, Some("Ubuntu CD releases.ubuntu.com"));
    assert_eq!(metainfo.created_by, Some("mktorrent 1.1"));
    assert_eq!(metainfo.creation_date, Some(1_645_734_525));

    let info = metainfo.info;

    assert_eq!(info.name, "ubuntu-20.04.4-live-server-amd64.iso");
    assert_eq!(
        info.piece_length(),
        cloudburst::piece::Length::from(262_144)
    );
    assert_eq!(info.length, Some(1_331_691_520));
    assert_eq!(info.pieces().unwrap().len(), 5080);
    assert!(info.files.is_none());

    Ok(())
}

#[test]
fn test_metainfo_read() -> Result<(), cloudburst::metainfo::Error> {
    let res = cloudburst::metainfo::from_slice(TORRENT_BYTES)?;
    #[cfg(feature = "std")]
    cloudburst::metainfo::validation::check(&res.1)?;

    assert_eq!(
        res.0,
        cloudburst::metainfo::InfoHash::from([
            0xb4, 0x4a, 0x0e, 0x20, 0xfa, 0x5b, 0x7c, 0xec, 0xb7, 0x71, 0x56, 0x33, 0x3b, 0x42,
            0x68, 0xdf, 0xd7, 0xc3, 0x0a, 0xfb,
        ])
    );

    Ok(())
}
