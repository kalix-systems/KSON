#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

pub mod encoding;
pub mod inum;
pub mod rep;
pub mod util;

use byte_string::*;
use rug::Integer;
use std::collections::BTreeMap;
use std::convert::{TryFrom, TryInto};
use std::sync::Arc;
use std::vec::Vec;

use inum::*;
use rep::KsonRep;

pub const NULL: Kson = Atomic(Null);

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Kson {
    Atomic(Atom),
    Contain(Container<Kson>),
}

use Kson::*;

impl TryFrom<Kson> for Atom {
    type Error = Container<Kson>;
    fn try_from(value: Kson) -> Result<Atom, Container<Kson>> {
        match value {
            Atomic(a) => Ok(a),
            Contain(c) => Err(c),
        }
    }
}

impl<T: TryFrom<Kson>> TryFrom<Kson> for Container<T> {
    type Error = ();
    fn try_from(ks: Kson) -> Result<Container<T>, ()> {
        match ks {
            Contain(c) => c.traverse_result(|x| x.try_into().map_err(|_| ())),
            Atomic(a) => Err(()),
        }
    }
}

impl Kson {
    fn to_atom(&self) -> Option<&Atom> {
        match self {
            Atomic(a) => Some(a),
            _ => None,
        }
    }

    fn to_container(&self) -> Option<&Container<Kson>> {
        match self {
            Contain(c) => Some(c),
            _ => None,
        }
    }

    pub fn to_vec(&self) -> Option<&Vec<Kson>> {
        match self {
            Contain(Array(a)) => Some(a),
            _ => None,
        }
    }

    pub fn into_vec(self) -> Option<Vec<Kson>> {
        Container::try_from(self).ok()?.into_vec()
    }

    pub fn into_map(self) -> Option<BTreeMap<ByteString, Kson>> {
        Container::try_from(self).ok()?.into_map()
    }

    pub fn into_rep<T: KsonRep>(self) -> Option<T> {
        T::from_kson(self)
    }
}

from_fn!(Kson, Atom, |a| Atomic(a));
from_fn!(Kson, Container<Kson>, |c| Contain(c));

/// Generic containers, can be either arrays or maps
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Container<T> {
    Array(Vec<T>),
    Map(BTreeMap<ByteString, T>),
}

use Container::*;

impl<T> From<Vec<T>> for Container<T> {
    fn from(v: Vec<T>) -> Container<T> {
        Array(v)
    }
}

impl<T> From<BTreeMap<ByteString, T>> for Container<T> {
    fn from(v: BTreeMap<ByteString, T>) -> Container<T> {
        Map(v)
    }
}

impl<T> Container<T> {
    fn into_vec(self) -> Option<Vec<T>> {
        match self {
            Array(v) => Some(v),
            _ => None,
        }
    }

    fn to_vec(&self) -> Option<&Vec<T>> {
        match self {
            Array(v) => Some(v),
            _ => None,
        }
    }

    fn into_map(self) -> Option<BTreeMap<ByteString, T>> {
        match self {
            Map(m) => Some(m),
            _ => None,
        }
    }

    fn to_map(&self) -> Option<&BTreeMap<ByteString, T>> {
        match self {
            Map(m) => Some(m),
            _ => None,
        }
    }

    fn fmap<O, F: FnMut(T) -> O>(self, mut f: F) -> Container<O> {
        match self {
            Array(a) => {
                let mut out = Vec::with_capacity(a.len());
                for t in a {
                    out.push(f(t));
                }
                Array(out)
            }
            Map(m) => Map(m.into_iter().map(|(k, v)| (k.clone(), f(v))).collect()),
        }
    }

    fn fmap_borrow<O, F: FnMut(&T) -> O>(&self, mut f: F) -> Container<O> {
        match self {
            Array(a) => {
                let mut out = Vec::with_capacity(a.len());
                for t in a {
                    out.push(f(t));
                }
                Array(out)
            }
            Map(m) => Map(m.iter().map(|(k, v)| (k.clone(), f(v))).collect()),
        }
    }

    fn traverse_option<O, F: FnMut(T) -> Option<O>>(self, mut f: F) -> Option<Container<O>> {
        match self {
            Array(a) => {
                let mut out = Vec::with_capacity(a.len());
                for t in a.into_iter() {
                    out.push(f(t)?);
                }
                Some(Array(out))
            }
            Map(m) => {
                let mut out = BTreeMap::new();
                for (k, v) in m {
                    out.insert(k, f(v)?);
                }
                Some(Map(out))
            }
        }
    }

    fn traverse_result<L, R, F: FnMut(T) -> Result<L, R>>(
        self,
        mut f: F,
    ) -> Result<Container<L>, R> {
        match self {
            Array(a) => {
                let mut out = Vec::with_capacity(a.len());
                for t in a.into_iter() {
                    out.push(f(t)?);
                }
                Ok(Array(out))
            }
            Map(m) => {
                let mut out = BTreeMap::new();
                for (k, v) in m {
                    out.insert(k, f(v)?);
                }
                Ok(Map(out))
            }
        }
    }
}

/// `Atom`s are atomic values for `Kson`
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Atom {
    Null,
    Bool(bool),
    ANum(Inum),
    Str(ByteString),
}

use Atom::*;

impl TryFrom<Atom> for bool {
    type Error = Atom;
    fn try_from(a: Atom) -> Result<Self, Atom> {
        match a {
            Bool(b) => Ok(b),
            a => Err(a),
        }
    }
}

impl TryFrom<Atom> for Inum {
    type Error = Atom;
    fn try_from(a: Atom) -> Result<Self, Atom> {
        match a {
            ANum(i) => Ok(i),
            a => Err(a),
        }
    }
}

impl TryFrom<Atom> for ByteString {
    type Error = Atom;
    fn try_from(a: Atom) -> Result<Self, Atom> {
        match a {
            Str(s) => Ok(s),
            a => Err(a),
        }
    }
}

impl Atom {
    fn is_null(&self) -> bool {
        match self {
            Null => true,
            _ => false,
        }
    }

    fn to_inum(&self) -> Option<&Inum> {
        match self {
            ANum(i) => Some(i),
            _ => None,
        }
    }

    fn to_bool(&self) -> Option<bool> {
        match self {
            Bool(b) => Some(*b),
            _ => None,
        }
    }

    fn to_str(&self) -> Option<&ByteString> {
        match self {
            Str(s) => Some(s),
            _ => None,
        }
    }
}

from_fn!(Atom, bool, Bool);
from_fn!(Atom, Inum, ANum);
from_fn!(Atom, ByteString, Str);

compose_from!(Kson, Atom, Inum);
compose_from!(Kson, Atom, ByteString);
compose_from!(Kson, Atom, bool);

compose_from!(Atom, Inum, Integer);
compose_from!(Atom, Inum, i64);
compose_from!(Atom, Inum, u64);

compose_from!(Kson, Inum, Integer);
compose_from!(Kson, Inum, i64);
compose_from!(Kson, Inum, u64);

from_prims!(Atom);
from_prims!(Kson);

//     /// `k.size()` returns an upper bound on number of bytes `encode_full(k)` would require
//     pub fn size(&self) -> usize {
//         fn leb_size(i: &Integer) -> usize {
//             i.significant_digits::<u8>() * 8 / 7 + 1
//         }
//         fn str_size(bs: &ByteString) -> usize {
//             let len_str = bs.len();
//             len_str + leb_size(&Integer::from(len_str))
//         }
//         match self {
//             Kson::KSString(b) => 1 + str_size(b),
//             Kson::KSInt(i) => 1 + leb_size(&i.to_int()),
//             Kson::KSArray(v) => v
//                 .iter()
//                 .fold(1 + leb_size(&Integer::from(v.len())), |acc, v| {
//                     acc + v.size()
//                 }),
//             Kson::KSMap(m) => m
//                 .iter()
//                 .fold(1 + leb_size(&Integer::from(m.len())), |acc, (k, v)| {
//                     acc + str_size(k) + v.size()
//                 }),
//             _ => 1,
//         }
//     }
// }
