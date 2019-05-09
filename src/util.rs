/// Converts a `u64` to the smallest possible vec of digits in little-endian order.
///
/// # Arguments
///
/// * `num: u64` - The integer to be converted.
///
/// # Example
///
/// ```
/// use kson::util::u64_to_digits;
///
/// let num = 4u64;
///
/// let some_vec = u64_to_digits(4);
///
/// // first byte should be 4
/// assert_eq!(some_vec[0], 4);
/// // there should only be one element
/// assert_eq!(some_vec.len(), 1);
/// ```
pub fn u64_to_digits(num: u64) -> Vec<u8> {
    let len = 8 - u64::leading_zeros(num) / 8;
    if len == 0 {
        vec![0]
    } else {
        let mut out = u64::to_le_bytes(num).to_vec();
        out.truncate(len as usize);
        out
    }
}

#[macro_export]
/// Helper macro to compose `From` implementations.
macro_rules! compose_from {
    ($to:tt, $mid:tt, $from:ty) => {
        impl From<$from> for $to {
            fn from(f: $from) -> Self { Self::from($mid::from(f)) }
        }
    };
}

#[macro_export]
/// Helper macro to make implementing `From` easier.
macro_rules! from_fn {
    ($to:ty, $from:ty, $fn:expr) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to { $fn(f) }
        }
    };
}

#[macro_export]
/// Helper macro to make implementing `From` easier.
macro_rules! from_as {
    ($to:tt, $from:ty, $as:ty) => {
        impl From<$from> for $to {
            fn from(f: $from) -> $to { $to::from(f as $as) }
        }
    };
}
