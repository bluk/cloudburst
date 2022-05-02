// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Error message values.
//!
//! Error messages are described in [BEP 5][bep_0005].
//!
//! [bep_0005]: http://bittorrent.org/beps/bep_0005.html

use bt_bencode::{value::Number, Value};
use core::convert::TryFrom;
use serde_bytes::ByteBuf;

use crate::dht::krpc::ErrorCode;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{string::String, vec, vec::Vec};

#[cfg(feature = "std")]
use std::{string::String, vec, vec::Vec};

/// The error message values.
#[derive(Clone, Debug, PartialEq)]
pub struct Values {
    code: ErrorCode,
    description: String,
}

impl Values {
    /// Instantiates a standard error value with a code and description.
    #[must_use]
    pub fn new(code: ErrorCode, description: String) -> Self {
        Self { code, description }
    }
}

impl Values {
    /// Sets the code.
    pub fn set_code(&mut self, code: ErrorCode) {
        self.code = code;
    }

    /// Sets the description.
    pub fn set_description(&mut self, description: String) {
        self.description = description;
    }
}

impl crate::dht::krpc::ErrorVal for Values {
    fn code(&self) -> ErrorCode {
        self.code
    }

    fn description(&self) -> &str {
        &self.description
    }

    fn to_value(&self) -> Value {
        Value::from(self)
    }
}

impl TryFrom<Value> for Values {
    type Error = crate::dht::krpc::Error;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .as_array()
                .ok_or(crate::dht::krpc::Error::is_deserialize_error())?,
        )
    }
}

impl TryFrom<&Vec<Value>> for Values {
    type Error = crate::dht::krpc::Error;

    fn try_from(value: &Vec<Value>) -> Result<Self, Self::Error> {
        match (
            value.get(0).and_then(|code| {
                code.as_i64()
                    .map(Number::Signed)
                    .or_else(|| code.as_u64().map(Number::Unsigned))
            }),
            value
                .get(1)
                .and_then(bt_bencode::Value::as_byte_str)
                .and_then(|bs| core::str::from_utf8(bs).ok())
                .map(String::from),
        ) {
            (Some(code), Some(description)) => {
                let code = match code {
                    Number::Signed(code) => match code {
                        201 => ErrorCode::GenericError,
                        202 => ErrorCode::ServerError,
                        203 => ErrorCode::ProtocolError,
                        204 => ErrorCode::MethodUnknown,
                        _ => ErrorCode::Other(
                            i32::try_from(code)
                                .map_err(|_| crate::dht::krpc::Error::is_deserialize_error())?,
                        ),
                    },
                    Number::Unsigned(code) => match code {
                        201 => ErrorCode::GenericError,
                        202 => ErrorCode::ServerError,
                        203 => ErrorCode::ProtocolError,
                        204 => ErrorCode::MethodUnknown,
                        _ => ErrorCode::Other(
                            i32::try_from(code)
                                .map_err(|_| crate::dht::krpc::Error::is_deserialize_error())?,
                        ),
                    },
                };
                Ok(Values { code, description })
            }
            _ => Err(crate::dht::krpc::Error::is_deserialize_error()),
        }
    }
}

impl From<Values> for Value {
    fn from(value: Values) -> Self {
        Value::from(&value)
    }
}

impl From<&Values> for Value {
    fn from(value: &Values) -> Self {
        Value::List(vec![
            Value::Int(Number::Signed(i64::from(value.code.code()))),
            Value::ByteStr(ByteBuf::from(value.description.clone())),
        ])
    }
}
