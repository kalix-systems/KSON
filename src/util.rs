use bytes::Bytes;

/// Converts a `u64` to an 8-byte `Bytes` in little endian order
pub fn u64_to_bytes_le(x: u64) -> Bytes { Bytes::from(u64::to_le_bytes(x).to_vec()) }

/// Converts a `u64` to the smallest possible vec of digits, little-endian
pub fn u64_to_digits(val: u64) -> Vec<u8> {
    let len = 8 - u64::leading_zeros(val) / 8;
    if len == 0 {
        vec![0]
    } else {
        let mut out = u64::to_le_bytes(val).to_vec();
        out.truncate(len as usize);
        out
    }
}

/// Converts `&str` to `Bytes`.
pub fn str_to_bs(s: &str) -> Bytes { Bytes::from(Vec::from(s.as_bytes())) }

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
