// use crate::bytes::Bytes;
use bytes::Bytes;
use pyo3::{prelude::*, types::IntoPyDict};
use std::{boxed::Box, convert::AsRef};

/// converts a `u64` to an 8-byte `Bytes` in little endian order
pub fn u64_to_bytes_le(x: u64) -> Bytes { Bytes::from(u64::to_le_bytes(x).to_vec()) }

/// converts a `u64` to the smallest possible vec of digits, little-endian
pub fn u64_to_digits(val: u64) -> Vec<u8> {
    let len = 8 - u64::leading_zeros(val) / 8;
    if len == 0 {
        vec![0]
    } else {
        let bytes = u64::to_le_bytes(val);
        let mut out = bytes.to_vec();
        out.truncate(len as usize);
        out
    }
}

/// Converts a `str` to a `Bytes`.
pub fn str_to_bs(s: &str) -> Bytes { Bytes::from(Vec::from(s.as_bytes())) }

// /// Tries to unwrap a value. If this fails, return a clone.
// pub fn unwrap_or_clone<T: Sized + Clone>(ptr: Arc<T>) -> T {
//     Arc::try_unwrap(ptr).unwrap_or_else(|a| a.as_ref().clone())
// }

#[macro_export]
macro_rules! compose_from {
    ($to:tt, $mid:tt, $from:ty) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to { $to::from($mid::from(f)) }
        }
    };
}

#[macro_export]
macro_rules! from_fn {
    ($to:ty, $from:ty, $fn:expr) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to { $fn(f) }
        }
    };
}

#[macro_export]
macro_rules! from_as {
    ($to:tt, $from:ty, $as:ty) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to { $to::from(f as $as) }
        }
    };
}
