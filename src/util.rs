/// Converts a [`u64`] to the smallest possible vector of digits in little-endian order.
///
/// # Arguments
///
/// * `num: u64` - The integer to be converted.
/// ```
pub(crate) fn u64_to_digits(num: u64) -> Vec<u8> {
    let len = 8 - u64::leading_zeros(num) / 8;
    if len == 0 {
        coldvec()
    } else {
        let mut out = u64::to_le_bytes(num).to_vec();
        out.truncate(len as usize);
        out
    }
}

#[cold]
fn coldvec() -> Vec<u8> { vec![0] }

#[macro_export]
/// Helper macro for implementing `From`.
macro_rules! from_fn {
    ($to:ty, $from:ty, $fn:expr) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to { $fn(f) }
        }
    };
}

#[macro_export]
/// Helper macro for implementing `From`.
macro_rules! from_as {
    ($to:tt, $from:ty, $as:ty) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to { $to::from(f as $as) }
        }
    };
}

#[macro_export]
/// Helper macro for implementing `TryFrom`.
macro_rules! try_from_ctor {
    ($from:ty, $to:ty, $ctor:tt) => {
        impl TryFrom<$from> for $to {
            type Error = $from;

            fn try_from(from: $from) -> Result<$to, $from> {
                match from {
                    $ctor(a) => Ok(a),
                    f => Err(f),
                }
            }
        }
    };
}

#[macro_export]
/// Helper macro for chaining `TryFrom` implementations.
macro_rules! chain_try_from {
    ($e: expr) => { $e.and_then(|x| x.try_into().map_err(|_| ())) };
    ($e: expr, $i: tt) => {
        chain_try_from!($e.and_then(|x| $i::try_from(x).map_err(|_| ())))
    };
    ($e: expr, $i: tt, $($is:tt)*) => {
        chain_try_from!($e.and_then(|x| $i::try_from(x).map_err(|_| ())), $($is)*)
    };
}
