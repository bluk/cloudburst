// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(
    rust_2018_idioms,
    missing_docs,
    missing_debug_implementations,
    unused_lifetimes,
    unused_qualifications
)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(feature = "alloc", not(feature = "std")))]
extern crate alloc;

macro_rules! fmt_byte_array {
    ($id:ident) => {
        impl fmt::Debug for $id {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                struct DebugFmt<'a>(&'a $id);

                impl<'a> fmt::Debug for DebugFmt<'a> {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        for b in (self.0).0 {
                            write!(f, "{:02X}", b)?;
                        }
                        Ok(())
                    }
                }

                f.debug_tuple(stringify!($id))
                    .field(&DebugFmt(self))
                    .finish()
            }
        }

        impl fmt::Display for $id {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                for b in self.0 {
                    write!(f, "{:02X}", b)?;
                }
                Ok(())
            }
        }

        impl core::fmt::UpperHex for $id {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                if f.alternate() {
                    write!(f, "0x")?;
                }

                for b in self.0 {
                    write!(f, "{:02X}", b)?;
                }

                Ok(())
            }
        }

        impl fmt::LowerHex for $id {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                if f.alternate() {
                    write!(f, "0x")?;
                }

                for b in self.0 {
                    write!(f, "{:02x}", b)?;
                }

                Ok(())
            }
        }

        impl fmt::Binary for $id {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                if f.alternate() {
                    write!(f, "0b")?;
                }

                for b in self.0 {
                    write!(f, "{:b}", b)?;
                }

                Ok(())
            }
        }
    };
}

pub mod conn;
pub mod dht;
pub mod metainfo;
pub mod peer;
pub mod piece;
pub mod protocol;
pub mod time;
pub mod torrent;
