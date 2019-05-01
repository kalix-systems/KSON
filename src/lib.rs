#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(clippy::cast_ptr_alignment)]
#![allow(clippy::cast_lossless)]
#![allow(clippy::clone_on_copy)]
#![feature(is_sorted)]

#[macro_use]
extern crate kson_macro;

pub mod encoding;
pub mod inum;
pub mod python;
pub mod rep;
pub mod util;
pub mod vecmap;

use bytes::Bytes;
use hashbrown::HashMap;
use rug::Integer;

use std::{
    collections::BTreeMap,
    convert::{TryFrom, TryInto},
    slice::Iter,
    sync::Arc,
    vec::Vec,
};

use inum::*;
use rep::KsonRep;
use vecmap::*;

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

    pub fn into_vec(self) -> Option<Vec<Kson>> { Container::try_from(self).ok()?.into_vec() }

    pub fn into_vecmap(self) -> Option<VecMap<Bytes, Kson>> {
        Container::try_from(self).ok()?.into_vecmap()
    }

    pub fn into_map(self) -> Option<HashMap<Bytes, Kson>> {
        Some(self.into_vecmap()?.into_hashmap())
    }

    pub fn into_rep<T: KsonRep>(self) -> Option<T> { T::from_kson(self) }
}

from_fn!(Kson, Atom, |a| Atomic(a));
from_fn!(Kson, Container<Kson>, |c| Contain(c));

/// Generic containers, can be either arrays or maps
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Container<T> {
    Array(Vec<T>),
    Map(VecMap<Bytes, T>),
}

use Container::*;

impl<T> From<Vec<T>> for Container<T> {
    fn from(v: Vec<T>) -> Container<T> { Array(v) }
}

impl<T> From<VecMap<Bytes, T>> for Container<T> {
    fn from(v: VecMap<Bytes, T>) -> Container<T> { Map(v) }
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

    fn into_vecmap(self) -> Option<VecMap<Bytes, T>> {
        match self {
            Map(m) => Some(m),
            _ => None,
        }
    }

    fn into_map(self) -> Option<HashMap<Bytes, T>> { Some(self.into_vecmap()?.into_hashmap()) }

    fn to_map(&self) -> Option<&VecMap<Bytes, T>> {
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
                let mut out = Vec::with_capacity(m.len());
                for (k, v) in m {
                    out.push((k, f(v)?));
                }
                Some(Map(VecMap::from_sorted(out)))
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
                let mut out = Vec::with_capacity(m.len());
                for (k, v) in m {
                    out.push((k, f(v)?));
                }
                Ok(Map(VecMap::from_sorted(out)))
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
    Str(Bytes),
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

impl TryFrom<Atom> for Bytes {
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

    fn to_str(&self) -> Option<&Bytes> {
        match self {
            Str(s) => Some(s),
            _ => None,
        }
    }
}

from_fn!(Atom, bool, Bool);
from_fn!(Atom, Inum, ANum);
from_fn!(Atom, Bytes, Str);
compose_from!(Atom, Bytes, Vec<u8>);

compose_from!(Kson, Atom, Inum);
compose_from!(Kson, Atom, Bytes);
compose_from!(Kson, Atom, bool);

compose_from!(Atom, Inum, Integer);
compose_from!(Atom, Inum, i64);
compose_from!(Atom, Inum, u64);

compose_from!(Kson, Inum, Integer);
compose_from!(Kson, Inum, i64);
compose_from!(Kson, Inum, u64);

compose_from!(Kson, Container, VecMap<Bytes, Kson>);
compose_from!(Kson, Container, Vec<Kson>);

from_prims!(Atom);
from_prims!(Kson);
