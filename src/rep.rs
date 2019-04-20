use byte_string::*;
use hashbrown::HashMap;
use num_traits::*;
use rug::Integer;
use std::collections::BTreeMap;
use std::net::{Ipv4Addr, SocketAddrV4};
use std::slice::Iter;
use std::sync::Arc;
use std::vec::Vec;

use crate::util::*;
use crate::*;

/// Values that can be converted to and from `Kson`.
pub trait KsonRep: Clone + Sized {
    /// Converts this value to `Kson`.
    /// NOTE: this function is expected to create a new reference - incrementing an existing
    /// reference will break the default into_kson implementation
    fn to_kson(&self) -> Kson {
        self.clone().into_kson()
    }

    /// Converts this value to `Kson`, consuming it in the process.
    fn into_kson(self) -> Kson {
        self.to_kson()
    }

    /// Converts `Kson` to a value of this type.
    fn from_kson(ks: Kson) -> Option<Self> {
        Self::from_kson_arc(ks).map(unwrap_or_clone)
    }

    /// Converts `Kson` to an `Arc`d value of this type
    fn from_kson_arc(ks: Kson) -> Option<Arc<Self>> {
        Self::from_kson(ks.clone()).map(Arc::new)
    }
}

impl KsonRep for Kson {
    fn into_kson(self) -> Kson {
        self
    }

    fn from_kson(ks: Kson) -> Option<Kson> {
        Some(ks)
    }
}

impl KsonRep for bool {
    fn into_kson(self) -> Kson {
        Kson::KSBool(self)
    }
    fn from_kson(ks: Kson) -> Option<bool> {
        ks.to_bool()
    }
}

impl KsonRep for u8 {
    fn into_kson(self) -> Kson {
        Kson::KSInt(Inum::from(self as u64))
    }
    fn from_kson(ks: Kson) -> Option<u8> {
        ks.to_int()?.to_u8()
    }
}

impl KsonRep for u16 {
    fn into_kson(self) -> Kson {
        Kson::KSInt(Inum::from(self as u64))
    }
    fn from_kson(ks: Kson) -> Option<u16> {
        ks.to_i64()
            .and_then(|i| if i < 0 { None } else { Some(i as u16) })
            .or_else(|| ks.to_int()?.to_u16())
    }
}

impl KsonRep for u32 {
    fn into_kson(self) -> Kson {
        Kson::KSInt(Inum::from(self as u64))
    }
    fn from_kson(ks: Kson) -> Option<u32> {
        ks.to_int()?.to_u32()
    }
}

impl KsonRep for u64 {
    fn into_kson(self) -> Kson {
        Kson::KSInt(Inum::from(self))
    }
    fn from_kson(ks: Kson) -> Option<u64> {
        ks.to_int()?.to_u64()
    }
}

impl KsonRep for i8 {
    fn into_kson(self) -> Kson {
        Kson::KSInt(Inum::from(self as i64))
    }
    fn from_kson(ks: Kson) -> Option<i8> {
        ks.to_int()?.to_i8()
    }
}

impl KsonRep for i16 {
    fn into_kson(self) -> Kson {
        Kson::KSInt(Inum::from(self as i64))
    }
    fn from_kson(ks: Kson) -> Option<i16> {
        ks.to_int()?.to_i16()
    }
}

impl KsonRep for i32 {
    fn into_kson(self) -> Kson {
        Kson::KSInt(Inum::from(self as i64))
    }
    fn from_kson(ks: Kson) -> Option<i32> {
        ks.into_inum()?.to_i32()
    }
}

impl KsonRep for i64 {
    fn into_kson(self) -> Kson {
        Kson::from(self)
    }
    fn from_kson(ks: Kson) -> Option<i64> {
        ks.into_i64()
    }
}

impl KsonRep for ByteString {
    fn into_kson(self) -> Kson {
        Kson::KSString(Arc::new(self))
    }
    fn from_kson_arc(ks: Kson) -> Option<Arc<Self>> {
        ks.into_string()
    }
}

impl<T: KsonRep> KsonRep for Vec<T> {
    fn into_kson(self) -> Kson {
        Kson::KSArray(Arc::new(self.into_iter().map(|x| x.into_kson()).collect()))
    }
    fn to_kson(&self) -> Kson {
        Kson::KSArray(Arc::new(self.iter().map(|x| x.to_kson()).collect()))
    }
    fn from_kson(ks: Kson) -> Option<Vec<T>> {
        unwrap_or_clone(ks.into_array()?)
            .into_iter()
            .map(T::from_kson)
            .collect()
    }
}

impl<T: KsonRep> KsonRep for Arc<T> {
    fn into_kson(self) -> Kson {
        self.as_ref().to_kson()
    }
    fn to_kson(&self) -> Kson {
        self.as_ref().to_kson()
    }
    fn from_kson(ks: Kson) -> Option<Arc<T>> {
        T::from_kson_arc(ks)
    }
}

impl<T: KsonRep> KsonRep for BTreeMap<ByteString, T> {
    fn into_kson(self) -> Kson {
        Kson::KSMap(Arc::new(
            self.into_iter().map(|(k, v)| (k, v.into_kson())).collect(),
        ))
    }
    fn to_kson(&self) -> Kson {
        Kson::KSMap(Arc::new(
            self.iter().map(|(k, v)| (k.clone(), v.to_kson())).collect(),
        ))
    }
    fn from_kson(ks: Kson) -> Option<Self> {
        unwrap_or_clone(ks.into_map()?)
            .into_iter()
            .map(|(k, v)| T::from_kson(v).map(|v| (k, v)))
            .collect()
    }
}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonRep
    for HashMap<ByteString, T, S>
{
    fn into_kson(self) -> Kson {
        Kson::KSMap(Arc::new(
            self.into_iter().map(|(k, v)| (k, v.into_kson())).collect(),
        ))
    }
    fn to_kson(&self) -> Kson {
        Kson::KSMap(Arc::new(
            self.iter().map(|(k, v)| (k.clone(), v.to_kson())).collect(),
        ))
    }
    fn from_kson(ks: Kson) -> Option<Self> {
        let m = unwrap_or_clone(ks.into_map()?);
        let mut h = HashMap::with_hasher(S::default());
        h.reserve(m.len());
        for (k, v) in m.into_iter() {
            v.into_rep().map(|v| h.insert(k, v));
        }
        Some(h)
    }
}

impl KsonRep for () {
    fn into_kson(self) -> Kson {
        Kson::KSArray(Arc::new(vec![]))
    }
    fn from_kson(ks: Kson) -> Option<()> {
        if ks.to_array()?.len() == 0 {
            Some(())
        } else {
            None
        }
    }
}

impl<A: KsonRep, B: KsonRep> KsonRep for (A, B) {
    fn into_kson(self) -> Kson {
        Kson::KSArray(Arc::new(vec![self.0.into_kson(), self.1.into_kson()]))
    }
    fn to_kson(&self) -> Kson {
        Kson::KSArray(Arc::new(vec![self.0.to_kson(), self.1.to_kson()]))
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let arr = ks.into_array()?;
        let a = A::from_kson(arr[0].clone())?;
        let b = B::from_kson(arr[1].clone())?;
        Some((a, b))
    }
}

impl<A: KsonRep, B: KsonRep, C: KsonRep> KsonRep for (A, B, C) {
    fn into_kson(self) -> Kson {
        Kson::KSArray(Arc::new(vec![
            self.0.into_kson(),
            self.1.into_kson(),
            self.2.into_kson(),
        ]))
    }
    fn to_kson(&self) -> Kson {
        Kson::KSArray(Arc::new(vec![
            self.0.to_kson(),
            self.1.to_kson(),
            self.2.to_kson(),
        ]))
    }
    fn from_kson(ks: Kson) -> Option<Self> {
        let arr = ks.into_array()?;
        let a = A::from_kson(arr[0].clone())?;
        let b = B::from_kson(arr[1].clone())?;
        let c = C::from_kson(arr[2].clone())?;
        Some((a, b, c))
    }
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
impl KsonNotNull for ByteString {}
impl<T: KsonRep> KsonNotNull for Vec<T> {}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonNotNull
    for HashMap<ByteString, T, S>
{
}
impl KsonNotNull for () {}
impl<A: KsonRep, B: KsonRep> KsonNotNull for (A, B) {}
impl<A: KsonRep, B: KsonRep, C: KsonRep> KsonNotNull for (A, B, C) {}
impl<T: KsonNotNull> KsonNotNull for Arc<T> {}

impl<T: KsonRep> KsonRep for Option<T> {
    fn into_kson(self) -> Kson {
        match self {
            Some(x) => Kson::KSArray(Arc::new(vec![x.into_kson()])),
            None => Kson::KSNull,
        }
    }
    fn to_kson(&self) -> Kson {
        match self {
            Some(x) => Kson::KSArray(Arc::new(vec![x.to_kson()])),
            None => Kson::KSNull,
        }
    }
    fn from_kson(ks: Kson) -> Option<Self> {
        match ks {
            Kson::KSNull => Some(None),
            Kson::KSArray(its) => {
                if its.len() != 1 {
                    None
                } else {
                    Some(Some(KsonRep::from_kson(its[0].clone())?))
                }
            }
            _ => None,
        }
    }
}

impl KsonRep for Ipv4Addr {
    fn to_kson(&self) -> Kson {
        let octs = self.octets();
        ByteString::new(vec![octs[0], octs[1], octs[2], octs[3]]).into_kson()
    }
    fn from_kson(ks: Kson) -> Option<Self> {
        let bs: ByteString = KsonRep::from_kson(ks)?;
        if bs.len() != 4 {
            None
        } else {
            Some(Ipv4Addr::new(bs[0], bs[1], bs[2], bs[3]))
        }
    }
}

impl KsonRep for SocketAddrV4 {
    fn to_kson(&self) -> Kson {
        (*self.ip(), self.port()).to_kson()
    }
    fn from_kson(ks: Kson) -> Option<Self> {
        let (ip, port) = KsonRep::from_kson(ks)?;
        Some(SocketAddrV4::new(ip, port))
    }
}

pub fn struct_to_kson(entries: &[(&str, Kson)]) -> Kson {
    let mut m = BTreeMap::new();
    for (k, v) in entries {
        m.insert(str_to_bs(k), v.clone());
    }
    Kson::KSMap(Arc::new(m))
}

pub fn struct_from_kson(ks: Kson, names: &[&str]) -> Option<Vec<Kson>> {
    let m = ks.to_map()?;
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
    fields.insert(0, Kson::KSString(Arc::new(str_to_bs(name))));
    Kson::KSArray(Arc::new(fields))
}

pub fn enum_from_kson<T, F: FnOnce(Iter<Kson>) -> Option<T>>(
    ks: &Kson,
    name: &str,
    f: F,
) -> Option<T> {
    let vec = ks.to_array()?;
    let mut fields = vec.as_ref().iter();
    if fields.next()?.to_string()?.as_ref() == &str_to_bs(name) {
        f(fields)
    } else {
        None
    }
}

pub fn pop_kson<T: KsonRep>(iter: &mut Iter<Kson>) -> Option<T> {
    KsonRep::from_kson(iter.next()?.clone())
}
