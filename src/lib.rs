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
use inum::*;
use rep::KsonRep;
use rug::Integer;
use std::{
    convert::{TryFrom, TryInto},
    slice::Iter,
    sync::Arc,
    vec::Vec,
};
use vecmap::*;

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Kson {
    Null,
    Bool(bool),
    Kint(Inum),
    Str(Bytes),
    Array(Vec<Kson>),
    Map(VecMap<Bytes, Kson>),
}

use Kson::*;

impl Kson {
    pub fn to_vec(&self) -> Option<&Vec<Kson>> {
        match self {
            Array(a) => Some(a),
            _ => None,
        }
    }

    pub fn into_vec(self) -> Option<Vec<Kson>> { self.try_into().ok() }

    pub fn into_vecmap(self) -> Option<VecMap<Bytes, Kson>> { self.try_into().ok() }

    pub fn into_map(self) -> Option<HashMap<Bytes, Kson>> {
        Some(self.into_vecmap()?.into_hashmap())
    }

    pub fn into_rep<T: KsonRep>(self) -> Option<T> { T::from_kson(self) }

    /// Indicates whether a value is `Null`.
    fn is_null(&self) -> bool {
        match self {
            Null => true,
            _ => false,
        }
    }

    fn to_inum(&self) -> Option<&Inum> {
        match self {
            Kint(i) => Some(i),
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

impl<T: Into<Kson>> From<Vec<T>> for Kson {
    fn from(v: Vec<T>) -> Kson { Array(v.into_iter().map(T::into).collect()) }
}

impl<T: Into<Kson>> From<VecMap<Bytes, T>> for Kson {
    fn from(v: VecMap<Bytes, T>) -> Kson {
        Map(v.into_iter().map(|(k, v)| (k, v.into())).collect())
    }
}

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

from_fn!(Kson, bool, Bool);
try_from_ctor!(Kson, bool, Bool);
from_fn!(Kson, Inum, Kint);
try_from_ctor!(Kson, Inum, Kint);
from_fn!(Kson, Bytes, Str);
try_from_ctor!(Kson, Bytes, Str);

try_from_ctor!(Kson, Vec<Kson>, Array);
try_from_ctor!(Kson, VecMap<Bytes, Kson>, Map);

compose_from!(Kson, Inum, Integer);
compose_from!(Kson, Inum, i64);
compose_from!(Kson, Inum, u64);

from_prims!(Kson);
