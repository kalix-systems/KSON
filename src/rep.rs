//! # Values representable as KSON.

use crate::*;
use bytes::{buf::Buf, Bytes};
use hashbrown::HashMap;
use std::{
    net::{Ipv4Addr, SocketAddrV4},
    vec::IntoIter,
};
pub use vecmap::VecMap;

/// A value representable as [`Kson`].
pub trait KsonRep: Clone + Sized {
    /// Converts value into [`Kson`].
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let k_num = 1.to_kson();
    /// ```
    fn to_kson(&self) -> Kson;

    /// Consumes value, converting it into [`Kson`].
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let k_num = 1.into_kson();
    /// ```
    fn into_kson(self) -> Kson;

    /// Consumes value, converting it from [`Kson`].
    ///
    /// # Arguments
    ///
    /// `ks: Kson` - The value to be converted from [`Kson`].
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let ks = "foo".to_string().into_kson();
    ///
    /// // should be equal
    /// assert_eq!(String::from_kson(ks).unwrap(), "foo");
    /// ```
    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError>;

    /// Converts value from [`Kson`].
    ///
    /// # Arguments
    ///
    /// `ks: &Kson` - The value to be converted from [`Kson`].
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let ks = "foo".to_string().into_kson();
    ///
    /// // should be equal
    /// assert_eq!(String::from_kson_ref(&ks).unwrap(), "foo");
    /// ```
    fn from_kson_ref(ks: &Kson) -> Result<Self, KsonConversionError> { Self::from_kson(ks.clone()) }
}

// TryFrom<Kson> implementations
/// Helper macro for implementing `TryFrom` for [`Kson`].
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

// sizes
try_from_kson!(usize, Inum);
try_from_kson!(isize, Inum);

// 8-bit integers
try_from_kson!(u8, Inum, i64);
try_from_kson!(i8, Inum, i64);

// 16-bit integers
try_from_kson!(u16, Inum, i64);
try_from_kson!(i16, Inum, i64);

// 32-bit integers
try_from_kson!(u32, Inum, i64);
try_from_kson!(i32, Inum, i64);

// 64-bit integers
try_from_kson!(i64, Inum);
try_from_kson!(u64, Inum);

// 128-bit integers
try_from_kson!(i128, Inum);
try_from_kson!(u128, Inum);

// BigInt
try_from_kson!(BigInt, Inum);

// Floating point numbers
try_from_kson!(f16, Float);
try_from_kson!(f32, Float);
try_from_kson!(f64, Float);

// `KsonRep` implementations
/// [`KsonRep`] given TryFrom<Kson>
macro_rules! try_from_kson_rep {
    ($t:ty) => {
        impl KsonRep for $t {
            fn to_kson(&self) -> Kson { self.clone().into() }

            fn into_kson(self) -> Kson { self.into() }

            fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
                match ks.try_into() {
                    Ok(v) => Ok(v),
                    Err(_) => {
                        Err(KsonConversionError::new(&format!(
                            "Could not convert `Kson` to `{}`",
                            stringify!($t)
                        )))
                    }
                }
            }
        }
    };
}

// Kson
try_from_kson_rep!(Kson);

// Inum
try_from_kson_rep!(Inum);

// Bytes
try_from_kson_rep!(Bytes);

// BigInt
try_from_kson_rep!(BigInt);

// bool
try_from_kson_rep!(bool);

// sizes
try_from_kson_rep!(usize);
try_from_kson_rep!(isize);

// 8-bit integers
try_from_kson_rep!(u8);
try_from_kson_rep!(i8);

// 16-bit integers
try_from_kson_rep!(u16);
try_from_kson_rep!(i16);

// 32-bit integers
try_from_kson_rep!(u32);
try_from_kson_rep!(i32);

// 64-bit integers
try_from_kson_rep!(u64);
try_from_kson_rep!(i64);

// 128-bit integers
try_from_kson_rep!(i128);
try_from_kson_rep!(u128);

// Floating point numbers
try_from_kson_rep!(f16);
try_from_kson_rep!(f32);
try_from_kson_rep!(f64);

macro_rules! kson_rep_kson_from {
    ($from:tt) => {
        impl From<$from> for Kson {
            fn from(f: $from) -> Self { f.into_kson() }
        }
    };
}

// String -> Kson
kson_rep_kson_from!(String);
// char -> Kson
kson_rep_kson_from!(char);
// () -> Kson
kson_rep_kson_from!(());
// Ipv4Addr -> Kson
kson_rep_kson_from!(Ipv4Addr);
// SocketAddrV4 -> Kson
kson_rep_kson_from!(SocketAddrV4);

/// Helper macro for tuples
macro_rules! tuple_kson {
    ($len:expr, $($idx:tt : $typ:ident),*) => {
        impl<$($typ: KsonRep),*> KsonRep for ($($typ,)*) {
            fn to_kson(&self) -> Kson {
                vec![ $(self.$idx.to_kson()),* ].into_kson()
            }

            fn into_kson(self) -> Kson  {
                vec![ $(self.$idx.into_kson()),* ].into_kson()
            }

            fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
                let exp_len = $len;
                let arr = ks.into_vec()?;

                if arr.len() == exp_len {
                    let mut k_iter = arr.into_iter();

                    let tuple = ($(match $typ::from_kson(k_iter.next().unwrap()) {
                        Ok(val) => val,
                        Err(e) => return Err(e),
                    },)*);
                    Ok(tuple)

                } else {
                    Err(KsonConversionError::new(&format!(
                                "Tuple has wrong number of fields; expected {}, found {}",
                                exp_len,
                                arr.len()
                    )))
                }
            }
        }

        impl<$($typ: KsonRep),*> From<($($typ,)*)> for Kson {
            fn from(f: ($($typ,)*)) -> Self {
                f.into_kson()
            }
        }
    }
}

// implement KsonRep for tuples up to length 12
tuple_kson!(1, 0: A);
tuple_kson!(2, 0: A, 1: B);
tuple_kson!(3, 0: A, 1: B, 2: C);
tuple_kson!(4, 0: A, 1: B, 2: C, 3: D);
tuple_kson!(5, 0: A, 1: B, 2: C, 3: D, 4: E);
tuple_kson!(6, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F);
tuple_kson!(7, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G);
tuple_kson!(8, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H);
tuple_kson!(9, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I);
tuple_kson!(
    10,
    0: A,
    1: B,
    2: C,
    3: D,
    4: E,
    5: F,
    6: G,
    7: H,
    8: I,
    9: J
);
tuple_kson!(
    11,
    0: A,
    1: B,
    2: C,
    3: D,
    4: E,
    5: F,
    6: G,
    7: H,
    8: I,
    9: J,
    10: K
);
tuple_kson!(
    12,
    0: A,
    1: B,
    2: C,
    3: D,
    4: E,
    5: F,
    6: G,
    7: H,
    8: I,
    9: J,
    10: K,
    11: L
);

impl KsonRep for String {
    fn into_kson(self) -> Kson { Kson::from_buf(self) }

    fn to_kson(&self) -> Kson { Kson::from_buf(self) }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        let bs = Bytes::from_kson(ks)?;

        match String::from_utf8(bs.to_vec()) {
            Ok(s) => Ok(s),
            Err(_) => {
                // pre-allocate
                let mut chars = Vec::with_capacity(bs.len() / 2 + 1);

                // bytestring into buffer
                let buf = &mut bs.into_buf();

                // get u16s
                for _ in 0..buf.remaining() {
                    chars.push(buf.get_u16_le());
                }

                // try to read
                match String::from_utf16(&chars) {
                    Ok(s) => Ok(s),
                    Err(_) => {
                        Err(KsonConversionError::new(
                            "Bytestring was neither valid utf-8 nor utf-16",
                        ))
                    }
                }
            }
        }
    }
}

impl KsonRep for char {
    fn into_kson(self) -> Kson { Kson::from_buf(self.to_string()) }

    fn to_kson(&self) -> Kson { Kson::from_buf(self.to_string()) }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        let mut s = String::from_kson(ks)?;

        match s.pop() {
            None => {
                Err(KsonConversionError::new(
                    "Tried to get character from empty string",
                ))
            }
            Some(c) => {
                if s.is_empty() {
                    Ok(c)
                } else {
                    Err(KsonConversionError::new("More than one character found"))
                }
            }
        }
    }
}

impl<T: KsonRep> KsonRep for Vec<T> {
    fn into_kson(self) -> Kson { Array(self.into_iter().map(T::into_kson).collect()) }

    fn to_kson(&self) -> Kson { Array(self.iter().map(T::to_kson).collect()) }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        ks.into_vec()?.into_iter().map(T::from_kson).collect()
    }
}

impl<T: KsonRep> KsonRep for VecMap<Bytes, T> {
    fn into_kson(self) -> Kson {
        Map(VecMap::from_sorted(
            self.into_iter().map(|(k, v)| (k, v.into_kson())).collect(),
        ))
    }

    fn to_kson(&self) -> Kson { Map(self.iter().map(|(k, v)| (k.clone(), v.to_kson())).collect()) }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        let vm = ks.into_vecmap()?;
        let mut out = Vec::with_capacity(vm.len());
        for (k, v) in vm {
            out.push((k, T::from_kson(v)?));
        }
        Ok(VecMap::from_sorted(out))
    }
}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonRep for HashMap<Bytes, T, S> {
    fn into_kson(self) -> Kson { Map(self.into_iter().map(|(k, v)| (k, v.into_kson())).collect()) }

    fn to_kson(&self) -> Kson { Map(self.iter().map(|(k, v)| (k.clone(), v.to_kson())).collect()) }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        let vmap = ks.into_vecmap()?;

        let mut pairs: Vec<(Bytes, T)> = Vec::with_capacity(vmap.len());

        for (k, v) in vmap.into_iter() {
            pairs.push((k, T::from_kson(v)?));
        }

        Ok(pairs.into_iter().collect())
    }
}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonRep for HashMap<String, T, S> {
    fn into_kson(self) -> Kson {
        Map(self
            .into_iter()
            .map(|(k, v)| (Bytes::from_buf(k.into_buf()), v.into_kson()))
            .collect())
    }

    fn to_kson(&self) -> Kson {
        Map(self
            .iter()
            .map(|(k, v)| (Bytes::from_buf(k.clone().into_buf()), v.to_kson()))
            .collect())
    }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        let vmap = ks.into_vecmap()?;

        let mut pairs: Vec<(String, T)> = Vec::with_capacity(vmap.len());

        for (k, v) in vmap.into_iter() {
            let str_key = String::from_utf8(k.to_vec())
                .map_err(|e| KsonConversionError::new(&e.to_string()))?;
            pairs.push((str_key, T::from_kson(v)?));
        }

        Ok(pairs.into_iter().collect())
    }
}

impl KsonRep for () {
    fn to_kson(&self) -> Kson { Array(vec![]) }

    fn into_kson(self) -> Kson { Array(vec![]) }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        let v = ks.into_vec()?;

        if v.is_empty() {
            Ok(())
        } else {
            Err(KsonConversionError::new(&format!(
                "Value is not 'nil', but rather a vector of length {}",
                v.len()
            )))
        }
    }
}

impl<T: KsonRep> KsonRep for Option<T> {
    fn into_kson(self) -> Kson {
        match self {
            Some(x) => Array(vec![x.into_kson()]),
            None => Null,
        }
    }

    fn to_kson(&self) -> Kson {
        match self {
            Some(x) => Array(vec![x.to_kson()]),
            _ => Null,
        }
    }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        match ks {
            Null => Ok(None),
            Array(v) => {
                let mut iter = v.into_iter();
                let val = iter
                    .next()
                    .ok_or_else(|| KsonConversionError::new("Value is not an `Option`"))?;
                if iter.next().is_none() {
                    Ok(Some(T::from_kson(val)?))
                } else {
                    Err(KsonConversionError::new("Value is not an `Option`"))
                }
            }
            _ => Err(KsonConversionError::new("Value is not an `Option`")),
        }
    }
}

impl KsonRep for Ipv4Addr {
    fn to_kson(&self) -> Kson {
        let octs: &[u8] = &self.octets();

        Bytes::from(octs).into_kson()
    }

    fn into_kson(self) -> Kson {
        let octs: &[u8] = &self.octets();

        Bytes::from(octs).into_kson()
    }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        let bs: Bytes = KsonRep::from_kson(ks)?;
        if bs.len() == 4 {
            Ok(Self::new(bs[0], bs[1], bs[2], bs[3]))
        } else {
            Err(KsonConversionError::new(&format!(
                "Value is {} bytes long, an `Ipv4Addr` should be 4 bytes long",
                bs.len(),
            )))
        }
    }
}

impl KsonRep for SocketAddrV4 {
    fn to_kson(&self) -> Kson { (*self.ip(), self.port()).into_kson() }

    fn into_kson(self) -> Kson { (*self.ip(), self.port()).into_kson() }

    fn from_kson(ks: Kson) -> Result<Self, KsonConversionError> {
        let (ip, port) = KsonRep::from_kson(ks)?;
        Ok(Self::new(ip, port))
    }
}

/// Gets the next element from an iterator of [`Kson`] values as `T`.
///
/// # Arguments
///
/// * `iter: &mut IntoIter<Kson>` - An iterator of [`Kson`] values to be converted into
///   `T`.
///
/// # Example
///
/// ```
/// use kson::prelude::*;
///
/// // vector of `Kson` values
/// let ks_values = vec![1, 2, 3].into_kson().into_vec().unwrap();
///
/// // get first value
/// let first: u8 = pop_kson(&mut ks_values.into_iter()).unwrap();
/// // should be 1
/// assert_eq!(first, 1);
/// ```
pub fn pop_kson<T: KsonRep>(iter: &mut IntoIter<Kson>) -> Result<T, KsonConversionError> {
    match iter.next() {
        None => Err(KsonConversionError::new("Iterator is empty or exhausted")),
        Some(v) => T::from_kson(v),
    }
}

/// Values whose KSON representation is never [`Null`].
pub trait KsonNotNull: KsonRep {}
impl<T: KsonRep> KsonNotNull for Vec<T> {}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonNotNull
    for HashMap<Bytes, T, S>
{
}
impl KsonNotNull for () {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kson_macro::*;

    #[test]
    // Test `KsonRep` auto-derive for unit-like struct
    fn unit_struct() {
        #[derive(KsonRep, Clone)]
        struct UnitStruct;

        // to_kson
        match UnitStruct::from_kson(UnitStruct.to_kson()) {
            Ok(UnitStruct) => {}
            Err(_e) => panic!("Couldn't retrieve unit struct"),
        }

        // into_kson
        match UnitStruct::from_kson(UnitStruct.into_kson()) {
            Ok(UnitStruct) => (),
            Err(_e) => panic!("Couldn't retrieve unit struct"),
        }
    }

    #[test]
    // Test `KsonRep` autoderive for named-tuple struct
    fn tuple() {
        #[derive(KsonRep, Clone, Debug)]
        struct Foo(u8, String);

        match Foo::from_kson(Foo(1, "hello".to_string()).to_kson()) {
            Ok(Foo(num, s)) => {
                assert_eq!(num, 1);
                assert_eq!(s, "hello".to_string());
            }
            _ => panic!("No Foo"),
        }
    }

    #[test]
    // Test `KsonRep` auto-derive for C-style struct
    fn c_struct() {
        #[derive(KsonRep, Clone)]
        struct CStruct {
            fu: u8,
        };

        let c_struct = CStruct { fu: 1 };

        // to_kson
        match CStruct::from_kson(c_struct.to_kson()) {
            Ok(CStruct { fu }) => assert_eq!(fu, 1),
            Err(_e) => panic!("Couldn't retrieve c-type struct"),
        }

        // into_kson
        match CStruct::from_kson(c_struct.into_kson()) {
            Ok(CStruct { fu }) => assert_eq!(fu, 1),
            Err(_e) => panic!("Couldn't retrieve c-type struct"),
        }
    }

    #[test]
    // Test `KsonRep` auto-derive for enum of unit-like structs
    fn unit_enum() {
        #[derive(KsonRep, Clone, Debug)]
        enum UnitEnum {
            Foo,
            Bar(u8),
        }

        use UnitEnum::*;

        // to_kson
        match UnitEnum::from_kson(Foo.to_kson()) {
            Ok(Foo) => (),
            _ => panic!("Failed to retrieve unit-like struct"),
        }

        // into_kson
        match UnitEnum::from_kson(Foo.into_kson()) {
            Ok(Foo) => (),
            _ => panic!("Failed to retrieve unit-like struct"),
        }
    }

    #[test]
    // Test `KsonRep` autoderive for enum of named-tuple structs
    fn named_tuple_enum() {
        #[derive(KsonRep, Clone, Debug)]
        enum Named {
            Foo(u8, String),
            Bar(Option<u8>),
        }

        use Named::*;

        let fu = Foo(1, "hello".to_string());

        // to_kson
        match Named::from_kson(fu.to_kson()) {
            Ok(Foo(num, string)) => {
                assert_eq!(num, 1);
                assert_eq!(string, "hello".to_string());
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }

        // into_kson
        match Named::from_kson(fu.into_kson()) {
            Ok(Foo(num, string)) => {
                assert_eq!(num, 1);
                assert_eq!(&string, "hello");
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }
    }

    // Test `KsonRep` auto-derive for enum of C-style structs
    #[test]
    fn c_style_enum() {
        #[derive(KsonRep, Clone, Debug)]
        enum CStyle {
            Foo { num: u8, string: String },
            Bar,
        }

        use CStyle::*;

        let fu = Foo {
            num:    1,
            string: "hello".to_string(),
        };

        // to_kson
        match CStyle::from_kson(fu.to_kson()) {
            Ok(Foo { num, string }) => {
                assert_eq!(num, 1);
                assert_eq!(&string, "hello");
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }

        // into_kson
        match CStyle::from_kson(fu.into_kson()) {
            Ok(Foo { num, string }) => {
                assert_eq!(num, 1);
                assert_eq!(&string, "hello");
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }
    }

}
