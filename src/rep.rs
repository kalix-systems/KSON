use hashbrown::HashMap;
use num_traits::*;
use rug::Integer;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::net::{Ipv4Addr, SocketAddrV4};
use std::slice::Iter;
use std::sync::Arc;
use std::vec::{IntoIter, Vec};
use void::{unreachable, Void};

use crate::util::*;
use crate::*;

pub trait KsonRep: Clone + Sized {
    fn to_kson(&self) -> Kson {
        self.clone().into_kson()
    }

    fn into_kson(self) -> Kson {
        self.to_kson()
    }

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
                Atom::try_from(ks).map_err(|_| ()).and_then(|a| a.try_into().map_err(|_| ()))
            }
        }
    };
    ($t: ty, $($is:tt)*) => {
        impl TryFrom<Kson> for $t {
            type Error = ();
            fn try_from(ks: Kson) -> Result<$t, ()> {
                chain_try_from!(Ok(ks), $($is)*)
                // chain_try_from!(Atom::try_from(ks).map_err(|_| ()), $($is)*)
                //     .try_into().map_err(|_| ())
            }
        }
    };
}

try_from_kson!(bool);
try_from_kson!(Bytes);
try_from_kson!(i64, Atom, Inum);
try_from_kson!(u64, Atom, Inum);

try_from_kson!(u8, Atom, Inum, i64);
try_from_kson!(u16, Atom, Inum, i64);
try_from_kson!(u32, Atom, Inum, i64);
try_from_kson!(i8, Atom, Inum, i64);
try_from_kson!(i16, Atom, Inum, i64);
try_from_kson!(i32, Atom, Inum, i64);

impl<T: Clone + Into<Kson> + TryFrom<Kson>> KsonRep for T {
    fn into_kson(self) -> Kson {
        self.into()
    }
    fn from_kson(ks: Kson) -> Option<Self> {
        ks.try_into().ok()
    }
}

impl<T: Into<Kson>> From<Vec<T>> for Kson {
    fn from(v: Vec<T>) -> Kson {
        let mut out = Vec::with_capacity(v.len());
        for t in v {
            out.push(t.into());
        }
        Contain(Array(out))
    }
}

impl<T: Into<Kson>> From<BTreeMap<Bytes, T>> for Kson {
    fn from(m: BTreeMap<Bytes, T>) -> Kson {
        Contain(Map(m.into_iter().map(|(k, v)| (k, v.into())).collect()))
    }
}

impl<T: KsonRep> KsonRep for Vec<T> {
    fn into_kson(self) -> Kson {
        Contain(Array(self).fmap(|t| t.into_kson()))
    }

    fn to_kson(&self) -> Kson {
        Contain(Array(self.iter().map(|t| t.to_kson()).collect()))
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        Container::try_from(ks)
            .ok()?
            .traverse_option(T::from_kson)?
            .into_vec()
    }
}

impl<T: KsonRep> KsonRep for BTreeMap<Bytes, T> {
    fn into_kson(self) -> Kson {
        Contain(Map(self).fmap(|t| t.into_kson()))
    }

    fn to_kson(&self) -> Kson {
        Contain(Map(self
            .iter()
            .map(|(k, v)| (k.clone(), v.to_kson()))
            .collect()))
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        Container::try_from(ks)
            .ok()?
            .traverse_option(T::from_kson)?
            .into_map()
    }
}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonRep for HashMap<Bytes, T, S> {
    fn into_kson(self) -> Kson {
        Contain(Map(self
            .into_iter()
            .map(|(k, v)| (k, v.into_kson()))
            .collect()))
    }

    fn to_kson(&self) -> Kson {
        Contain(Map(self
            .iter()
            .map(|(k, v)| (k.clone(), v.to_kson()))
            .collect()))
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let m: BTreeMap<Bytes, Kson> = ks.into_map()?;
        let mut h = HashMap::with_hasher(S::default());
        h.reserve(m.len());
        for (k, v) in m.into_iter() {
            let t = T::from_kson(v)?;
            h.insert(k, t);
        }
        Some(h)
    }
}

impl KsonRep for () {
    fn into_kson(self) -> Kson {
        Contain(Array(vec![]))
    }
    fn from_kson(ks: Kson) -> Option<()> {
        if ks.into_vec()?.len() == 0 {
            Some(())
        } else {
            None
        }
    }
}

impl<A: KsonRep, B: KsonRep> KsonRep for (A, B) {
    fn into_kson(self) -> Kson {
        Contain(Array(vec![self.0.into_kson(), self.1.into_kson()]))
    }

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
        Contain(Array(vec![
            self.0.into_kson(),
            self.1.into_kson(),
            self.2.into_kson(),
        ]))
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
        Contain(Array(vec![
            self.0.into_kson(),
            self.1.into_kson(),
            self.2.into_kson(),
            self.3.into_kson(),
        ]))
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
            Some(x) => Contain(Array(vec![x.into_kson()])),
            None => Atomic(Null),
        }
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        if let Some(Null) = ks.to_atom() {
            Some(None)
        } else if let Some(v) = ks.into_vec() {
            if v.len() == 1 {
                let v = v.into_iter().next().unwrap();
                Some(Some(T::from_kson(v)?))
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl KsonRep for Ipv4Addr {
    fn into_kson(self) -> Kson {
        let octs = self.octets();
        Bytes(vec![octs[0], octs[1], octs[2], octs[3]]).into_kson()
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
    fn into_kson(self) -> Kson {
        (*self.ip(), self.port()).into_kson()
    }
    fn from_kson(ks: Kson) -> Option<Self> {
        let (ip, port) = KsonRep::from_kson(ks)?;
        Some(SocketAddrV4::new(ip, port))
    }
}

pub fn struct_to_kson(entries: Vec<(&str, Kson)>) -> Kson {
    let mut m = BTreeMap::new();
    for (k, v) in entries {
        m.insert(str_to_bs(k), v);
    }
    Kson::from(m)
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
    Contain(Array(fields))
    // Kson::from(fields)
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

pub fn pop_kson<T: KsonRep>(iter: &mut IntoIter<Kson>) -> Option<T> {
    KsonRep::from_kson(iter.next()?)
}

/// Values whose KSON representation is never `KSNull`.
pub trait KsonNotNull: KsonRep {}
impl KsonNotNull for u8 {}
impl KsonNotNull for u16 {}
impl KsonNotNull for u32 {}
impl KsonNotNull for u64 {}
impl KsonNotNull for i8 {}
impl KsonNotNull for i16 {}
impl KsonNotNull for i32 {}
impl KsonNotNull for i64 {}
impl KsonNotNull for Bytes {}
impl<T: KsonRep> KsonNotNull for Vec<T> {}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonNotNull
    for HashMap<Bytes, T, S>
{
}
impl KsonNotNull for () {}
impl<A: KsonRep, B: KsonRep> KsonNotNull for (A, B) {}
impl<A: KsonRep, B: KsonRep, C: KsonRep> KsonNotNull for (A, B, C) {}
