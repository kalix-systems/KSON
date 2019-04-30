// use crate::bytes::Bytes;
use bytes::Bytes;
use pyo3::{prelude::*, types::IntoPyDict};
use std::{boxed::Box, convert::AsRef};

/// converts a `u64` to an 8-byte `Bytes` in little endian order
pub fn u64_to_bytes_le(x: u64) -> Bytes {
    Bytes::from(&u64::to_le_bytes(x) as &[u8])
}

/// converts an 8-byte `Bytes` to a `u64` in little endian order
pub fn bytes_to_u64_le(bs: Bytes) -> u64 {
    assert!(bs.len() == 8);
    let mut res: [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
    for (r, b) in res.iter_mut().zip(bs) {
        *r = b;
    }
    u64::from_le_bytes(res)
}

/// converts a `u64` to an 8-byte `Bytes` in big endian order
pub fn u64_to_bytes_be(x: u64) -> Bytes {
    Bytes::from(&u64::to_be_bytes(x) as &[u8])
}

/// converts an 8-byte `Bytes` to a `u64` in big endian order
pub fn bytes_to_u64_be(bs: Bytes) -> u64 {
    assert!(bs.len() == 8);
    let mut res: [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
    for (r, b) in res.iter_mut().zip(bs) {
        *r = b;
    }
    u64::from_be_bytes(res)
}

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

/// Returns a vector of `n` 0 bytes
pub fn vec_n_0_bytes(n: usize) -> Vec<u8> {
    vec![0; n]
}

/// Converts a `str` to a `Bytes`.
pub fn str_to_bs(s: &str) -> Bytes {
    Bytes::from(Vec::from(s.as_bytes()))
}

// /// Tries to unwrap a value. If this fails, return a clone.
// pub fn unwrap_or_clone<T: Sized + Clone>(ptr: Arc<T>) -> T {
//     Arc::try_unwrap(ptr).unwrap_or_else(|a| a.as_ref().clone())
// }

/// A macro for saner error handling.
#[macro_export]
macro_rules! womp {
    ($sus: expr, $message: expr) => {
        match $sus {
            Ok(legit_val) => legit_val,
            Err(_e) => panic!($message),
        }
    };
}

#[macro_export]
macro_rules! compose_from {
    ($to: tt, $mid: tt, $from: ty) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to {
                $to::from($mid::from(f))
            }
        }
    };
}

#[macro_export]
macro_rules! from_fn {
    ($to: ty, $from: ty, $fn: expr) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to {
                $fn(f)
            }
        }
    };
}

#[macro_export]
macro_rules! from_as {
    ($to: tt, $from: ty, $as: ty) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to {
                $to::from(f as $as)
            }
        }
    };
}
