use crate::{util::*, vecmap::*, *};
use bytes::Bytes;
use hashbrown::HashMap;
use std::{
    fmt::Debug,
    net::{Ipv4Addr, SocketAddrV4},
    vec::{IntoIter, Vec},
};

/// A value representable as `Kson`.
pub trait KsonRep: Clone + Sized {
    /// Converts value into `Kson`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::rep::*;
    ///
    /// let k_num = 1.to_kson();
    /// ```
    fn to_kson(&self) -> Kson { self.clone().into_kson() }

    /// Consumes value, converting it into kson.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::rep::*;
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
    /// use kson::rep::*;
    ///
    /// let k_num = "foo".to_string().into_kson();
    ///
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

try_from_kson!(i64, Inum);
try_from_kson!(u64, Inum);

try_from_kson!(u8, Inum, i64);
try_from_kson!(u16, Inum, i64);
try_from_kson!(u32, Inum, i64);
try_from_kson!(i8, Inum, i64);
try_from_kson!(i16, Inum, i64);
try_from_kson!(i32, Inum, i64);

macro_rules! try_from_kson_rep {
    ($t:ty) => {
        impl KsonRep for $t {
            fn into_kson(self) -> Kson { self.into() }

            fn from_kson(ks: Kson) -> Option<Self> { ks.try_into().ok() }
        }
    };
}

try_from_kson_rep!(Kson);
try_from_kson_rep!(bool);
try_from_kson_rep!(u8);
try_from_kson_rep!(u16);
try_from_kson_rep!(u32);
try_from_kson_rep!(u64);
try_from_kson_rep!(i8);
try_from_kson_rep!(i16);
try_from_kson_rep!(i32);
try_from_kson_rep!(i64);
try_from_kson_rep!(Inum);
try_from_kson_rep!(Bytes);

impl KsonRep for String {
    fn into_kson(self) -> Kson { Byt(Bytes::from(self.into_bytes())) }

    fn to_kson(&self) -> Kson { Byt(Bytes::from(self.as_bytes())) }

    fn from_kson(ks: Kson) -> Option<Self> {
        String::from_utf8(Bytes::from_kson(ks)?.to_vec()).ok()
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
        let octs = self.octets();
        Bytes::from(&[octs[0], octs[1], octs[2], octs[3]] as &[u8]).into_kson()
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let bs: Bytes = KsonRep::from_kson(ks)?;
        if bs.len() != 4 {
            None
        } else {
            Some(Ipv4Addr::new(bs[0], bs[1], bs[2], bs[3]))
        }
    }
}

impl KsonRep for SocketAddrV4 {
    fn into_kson(self) -> Kson { (*self.ip(), self.port()).into_kson() }

    fn from_kson(ks: Kson) -> Option<Self> {
        let (ip, port) = KsonRep::from_kson(ks)?;
        Some(SocketAddrV4::new(ip, port))
    }
}

pub fn struct_to_kson(entries: Vec<(&str, Kson)>) -> Kson {
    let vm: VecMap<Bytes, Kson> = entries
        .into_iter()
        .map(|(k, v)| (str_to_bs(k), v))
        .collect();
    Kson::from(vm)
}

pub fn struct_from_kson(ks: Kson, names: &[&str]) -> Option<Vec<Kson>> {
    let m = ks.into_map()?;
    let outs: Vec<Kson> = names
        .iter()
        .filter_map(|n| m.get(&str_to_bs(n)).cloned())
        .collect();
    if outs.len() == names.len() && outs.len() == m.len() {
        Some(outs)
    } else {
        None
    }
}

pub fn enum_to_kson(name: &str, mut fields: Vec<Kson>) -> Kson {
    fields.insert(0, Kson::from(str_to_bs(name)));
    Array(fields)
}

pub fn enum_from_kson<T: Debug>(
    ks: Kson,
    fns: Vec<(&str, Box<FnMut(IntoIter<Kson>) -> Option<T>>)>,
) -> Option<T> {
    let vec = ks.into_vec()?;
    let mut fields = vec.into_iter();
    let ctor: Bytes = fields.next()?.try_into().ok()?;
    for (name, mut f) in fns {
        if ctor == str_to_bs(name) {
            let out = f(fields);
            return out;
        }
    }
    None
}

/// Gets the next element from an iterator of `Kson` values as `T`.
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
