use crate::*;
use bytes::Bytes;
use hashbrown::HashMap;
use std::{
    net::{Ipv4Addr, SocketAddrV4},
    vec::{IntoIter, Vec},
};
pub use vecmap::VecMap;

/// A value representable as `Kson`.
pub trait KsonRep: Clone + Sized {
    /// Converts value into `Kson`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let k_num = 1.to_kson();
    /// ```
    fn to_kson(&self) -> Kson { self.clone().into_kson() }

    /// Consumes value, converting it into kson.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let k_num = 1.into_kson();
    /// ```
    fn into_kson(self) -> Kson { self.to_kson() }

    /// Converts value from `Kson`.
    ///
    /// # Arguments
    ///
    /// `ks: Kson` - The value to be converted from `Kson`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let k_num = "foo".to_string().into_kson();
    ///
    /// // should be equal
    /// assert_eq!(String::from_kson(k_num).unwrap(), "foo");
    /// ```
    fn from_kson(ks: Kson) -> Option<Self>;
}

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

macro_rules! try_from_kson_rep {
    ($t:ty) => {
        impl KsonRep for $t {
            fn into_kson(self) -> Kson { self.into() }

            fn from_kson(ks: Kson) -> Option<Self> { ks.try_into().ok() }
        }
    };
}

// Kson
try_from_kson_rep!(Kson);

// bool
try_from_kson_rep!(bool);

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

// BigInt
try_from_kson_rep!(BigInt);

// Floating point numbers
try_from_kson_rep!(f16);
try_from_kson_rep!(f32);
try_from_kson_rep!(f64);

// Inum
try_from_kson_rep!(Inum);

// Bytes
try_from_kson_rep!(Bytes);

impl KsonRep for String {
    fn into_kson(self) -> Kson { Byt(Bytes::from(self)) }

    fn to_kson(&self) -> Kson { Byt(Bytes::from(self.as_bytes())) }

    fn from_kson(ks: Kson) -> Option<Self> {
        String::from_utf8(Bytes::from_kson(ks)?.to_vec()).ok()
    }
}

impl KsonRep for char {
    fn into_kson(self) -> Kson { Byt(Bytes::from(self.to_string())) }

    fn to_kson(&self) -> Kson { Byt(Bytes::from(self.to_string())) }

    fn from_kson(ks: Kson) -> Option<Self> {
        let mut s = String::from_kson(ks)?;
        if s.len() == 1 {
            s.pop()
        } else {
            None
        }
    }
}

impl<T: KsonRep> KsonRep for Vec<T> {
    fn into_kson(self) -> Kson { Array(self.into_iter().map(T::into_kson).collect()) }

    fn to_kson(&self) -> Kson { Array(self.iter().map(T::to_kson).collect()) }

    fn from_kson(ks: Kson) -> Option<Self> {
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

    fn from_kson(ks: Kson) -> Option<Self> {
        let vm = ks.into_vecmap()?;
        let mut out = Vec::with_capacity(vm.len());
        for (k, v) in vm {
            out.push((k, T::from_kson(v)?));
        }
        Some(VecMap::from_sorted(out))
    }
}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonRep for HashMap<Bytes, T, S> {
    fn into_kson(self) -> Kson { Map(self.into_iter().map(|(k, v)| (k, v.into_kson())).collect()) }

    fn to_kson(&self) -> Kson { Map(self.iter().map(|(k, v)| (k.clone(), v.to_kson())).collect()) }

    fn from_kson(ks: Kson) -> Option<Self> {
        ks.into_vecmap()?
            .into_iter()
            .map(|(k, v)| Some((k, T::from_kson(v)?)))
            .collect()
    }
}

impl KsonRep for () {
    fn into_kson(self) -> Kson { Array(vec![]) }

    fn from_kson(ks: Kson) -> Option<()> {
        if ks.into_vec()?.is_empty() {
            Some(())
        } else {
            None
        }
    }
}

impl<A: KsonRep, B: KsonRep> KsonRep for (A, B) {
    fn into_kson(self) -> Kson { Array(vec![self.0.into_kson(), self.1.into_kson()]) }

    fn from_kson(ks: Kson) -> Option<Self> {
        let arr = ks.into_vec()?;
        if arr.len() == 2 {
            let mut iter = arr.into_iter();
            let k1 = iter.next()?;
            let k2 = iter.next()?;
            Some((A::from_kson(k1)?, B::from_kson(k2)?))
        } else {
            None
        }
    }
}

impl<A: KsonRep, B: KsonRep, C: KsonRep> KsonRep for (A, B, C) {
    fn into_kson(self) -> Kson {
        Array(vec![
            self.0.into_kson(),
            self.1.into_kson(),
            self.2.into_kson(),
        ])
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let arr = ks.into_vec()?;
        if arr.len() == 3 {
            let mut iter = arr.into_iter();
            let k1 = iter.next().unwrap();
            let k2 = iter.next().unwrap();
            let k3 = iter.next().unwrap();
            Some((A::from_kson(k1)?, B::from_kson(k2)?, C::from_kson(k3)?))
        } else {
            None
        }
    }
}
impl<A: KsonRep, B: KsonRep, C: KsonRep, D: KsonRep> KsonRep for (A, B, C, D) {
    fn into_kson(self) -> Kson {
        Array(vec![
            self.0.into_kson(),
            self.1.into_kson(),
            self.2.into_kson(),
            self.3.into_kson(),
        ])
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let arr = ks.into_vec()?;
        if arr.len() == 4 {
            let mut iter = arr.into_iter();
            let k1 = iter.next().unwrap();
            let k2 = iter.next().unwrap();
            let k3 = iter.next().unwrap();
            let k4 = iter.next().unwrap();
            Some((
                A::from_kson(k1)?,
                B::from_kson(k2)?,
                C::from_kson(k3)?,
                D::from_kson(k4)?,
            ))
        } else {
            None
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

    fn from_kson(ks: Kson) -> Option<Self> {
        match ks {
            Null => Some(None),
            Array(v) => {
                let mut iter = v.into_iter();
                let val = iter.next()?;
                if iter.next().is_none() {
                    Some(Some(T::from_kson(val)?))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl KsonRep for Ipv4Addr {
    fn into_kson(self) -> Kson {
        let octs: &[u8] = &self.octets();

        Bytes::from(octs).into_kson()
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let bs: Bytes = KsonRep::from_kson(ks)?;
        if bs.len() == 4 {
            Some(Self::new(bs[0], bs[1], bs[2], bs[3]))
        } else {
            None
        }
    }
}

impl KsonRep for SocketAddrV4 {
    fn into_kson(self) -> Kson { (*self.ip(), self.port()).into_kson() }

    fn from_kson(ks: Kson) -> Option<Self> {
        let (ip, port) = KsonRep::from_kson(ks)?;
        Some(Self::new(ip, port))
    }
}

/// Gets the next element from an iterator of `Kson` values as `T`.
///
/// # Arguments
///
/// * `iter: &mut IntoIter<Kson>` - An interator of `Kson` values to be converted into
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
pub fn pop_kson<T: KsonRep>(iter: &mut IntoIter<Kson>) -> Option<T> {
    KsonRep::from_kson(iter.next()?)
}

/// Values whose KSON representation is never `Null`.
pub trait KsonNotNull: KsonRep {}
// impl KsonNotNull for u8 {}
// impl KsonNotNull for u16 {}
// impl KsonNotNull for u32 {}
// impl KsonNotNull for u64 {}
// impl KsonNotNull for i8 {}
// impl KsonNotNull for i16 {}
// impl KsonNotNull for i32 {}
// impl KsonNotNull for i64 {}
// impl KsonNotNull for Bytes {}
impl<T: KsonRep> KsonNotNull for Vec<T> {}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonNotNull
    for HashMap<Bytes, T, S>
{
}
impl KsonNotNull for () {}
impl<A: KsonRep, B: KsonRep> KsonNotNull for (A, B) {}
impl<A: KsonRep, B: KsonRep, C: KsonRep> KsonNotNull for (A, B, C) {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kson_macro::*;

    #[test]
    // Test `KsonRep` autoderive for unit-like struct
    fn unit_struct() {
        #[derive(KsonRep, Clone)]
        struct UnitStruct;

        // to_kson
        match UnitStruct::from_kson(UnitStruct.to_kson()) {
            Some(UnitStruct) => (),
            None => panic!("Couldn't retrieve unit struct"),
        }

        // into_kson
        match UnitStruct::from_kson(UnitStruct.into_kson()) {
            Some(UnitStruct) => (),
            None => panic!("Couldn't retrieve unit struct"),
        }
    }

    #[test]
    // Test `KsonRep` autoderive for C-style struct
    fn c_struct() {
        #[derive(KsonRep, Clone)]
        struct CStruct {
            fu: u8,
        };

        let c_struct = CStruct { fu: 1 };

        // to_kson
        match CStruct::from_kson(c_struct.to_kson()) {
            Some(CStruct { fu }) => assert_eq!(fu, 1),
            None => panic!("Couldn't retrieve c-type struct"),
        }

        // into_kson
        match CStruct::from_kson(c_struct.into_kson()) {
            Some(CStruct { fu }) => assert_eq!(fu, 1),
            None => panic!("Couldn't retrieve c-type struct"),
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
            Some(Foo(num, string)) => {
                assert_eq!(num, 1);
                assert_eq!(string, "hello".to_string());
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }

        // into_kson
        match Named::from_kson(fu.into_kson()) {
            Some(Foo(num, string)) => {
                assert_eq!(num, 1);
                assert_eq!(&string, "hello");
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }
    }

    #[test]
    // Test `KsonRep` autoderive for enum of unit-like structs
    fn unit_enum() {
        #[derive(KsonRep, Clone, Debug)]
        enum UnitEnum {
            Foo,
            Bar(u8),
        }

        use UnitEnum::*;

        // to_kson
        match UnitEnum::from_kson(Foo.to_kson()) {
            Some(Foo) => (),
            _ => panic!("Failed to retrieve unit-like struct"),
        }

        // into_kson
        match UnitEnum::from_kson(Foo.into_kson()) {
            Some(Foo) => (),
            _ => panic!("Failed to retrieve unit-like struct"),
        }
    }

    #[test]
    /// Test `KsonRep` autoderive for named-tuple struct
    fn tuple() {
        #[derive(KsonRep, Clone, Debug)]
        struct Foo(u8, String);

        match Foo::from_kson(Foo(1, "hello".to_string()).to_kson()) {
            Some(Foo(num, s)) => {
                assert_eq!(num, 1);
                assert_eq!(s, "hello".to_string());
            }
            _ => panic!("No Foo"),
        }
    }

    // Test `KsonRep` autoderive for enum of C-style structs
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
            Some(Foo { num, string }) => {
                assert_eq!(num, 1);
                assert_eq!(&string, "hello");
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }

        // into_kson
        match CStyle::from_kson(fu.into_kson()) {
            Some(Foo { num, string }) => {
                assert_eq!(num, 1);
                assert_eq!(&string, "hello");
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }
    }

}
