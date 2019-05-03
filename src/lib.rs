//#![allow(dead_code)]
//#![allow(unused_variables)]
//#![allow(unused_imports)]
#![allow(clippy::cast_lossless)]
// TODO figure out if dereferencing is still slower than cloning
#![allow(clippy::clone_on_copy)]
#![feature(is_sorted)]
#![feature(result_map_or_else)]

pub extern crate kson_macro;

pub mod encoding;
pub mod inum;
pub mod python;
pub mod rep;
pub mod util;
pub mod vecmap;

use bytes::Bytes;
use hashbrown::HashMap;
use inum::*;
use num_bigint::BigInt;
use rep::KsonRep;
use std::convert::{TryFrom, TryInto};
use vecmap::*;

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Kson {
    Null,
    Bool(bool),
    Kint(Inum),
    Byt(Bytes),
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

    /// Tries to cast value as an `Inum`, returns `None` if it fails.
    fn to_inum(&self) -> Option<&Inum> {
        match self {
            Kint(i) => Some(i),
            _ => None,
        }
    }

    /// Tries to cast value as a `bool`, returns `None` if it fails.
    fn to_bool(&self) -> Option<bool> {
        match self {
            Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Tries to cast value as `Bytes`, returns `None` if it fails.
    fn to_bytes(&self) -> Option<&Bytes> {
        match self {
            Byt(s) => Some(s),
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
from_fn!(Kson, Bytes, Byt);
try_from_ctor!(Kson, Bytes, Byt);

try_from_ctor!(Kson, Vec<Kson>, Array);
try_from_ctor!(Kson, VecMap<Bytes, Kson>, Map);

compose_from!(Kson, Inum, BigInt);
compose_from!(Kson, Inum, i64);
compose_from!(Kson, Inum, u64);

from_prims!(Kson);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivial_tests() {
        assert!(Null.is_null());

        assert!(5.to_kson().to_inum().is_some());

        assert!(true.to_kson().to_bool().unwrap());

        assert_eq!(
            Bytes::from("word").to_kson().to_bytes().unwrap(),
            &Bytes::from("word")
        );
    }

    #[test]
    fn from_vec() {
        let v = vec![0, 1, 2, 3, 4];
        let k_val = Kson::from(v.clone());
        assert_eq!(k_val.into_rep(), Some(v));
    }
}
