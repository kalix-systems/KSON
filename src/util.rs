/// Converts a `u64` to the smallest possible vec of digits in little-endian order.
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

#[macro_export]
/// Try from constructor
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
/// Try TryFrom impls together.
macro_rules! chain_try_from {
    ($e: expr) => { $e.and_then(|x| x.try_into().map_err(|_| ())) };
    ($e: expr, $i: tt) => {
        chain_try_from!($e.and_then(|x| $i::try_from(x).map_err(|_| ())))
    };
    ($e: expr, $i: tt, $($is:tt)*) => {
        chain_try_from!($e.and_then(|x| $i::try_from(x).map_err(|_| ())), $($is)*)
    };
}

#[macro_export]
/// Helper macro for implementing `TryFrom` for `Kson`.
macro_rules! try_from_kson {
    ($t: ty) => {
        impl TryFrom<Kson> for $t {
            type Error = ();
            fn try_from(ks: Kson) -> Result<$t, ()> {
                ks.try_into().map_err(|_| ())
            }
        }
    };
    ($t: ty, $($is:tt)*) => {
        impl TryFrom<Kson> for $t {
            type Error = ();
            fn try_from(ks: Kson) -> Result<$t, ()> {
                chain_try_from!(Ok(ks), $($is)*)
            }
        }
    };
}

#[macro_export]
/// KsonRep given TryFrom<Kson>
macro_rules! try_from_kson_rep {
    ($t:ty) => {
        impl KsonRep for $t {
            fn into_kson(self) -> Kson { self.into() }

            fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
                match ks.try_into() {
                    Ok(v) => Ok(v),
                    Err(_) => {
                        Err(KsonConversionError::new(&format!(
                            "Conversion was not possible"
                        )))
                    }
                }
            }
        }
    };
}
