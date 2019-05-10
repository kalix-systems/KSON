//! # KSON
//!
//! KSON (Kalix Serializable Object Notation) is a serialization format designed to be
//! efficient, complete, concise, and easy to implement.
//!
//! # Usage
//!
//! The trait `KsonRep` is used to specify how data is converted into `Kson`.
//!
//! This trait can usually be autoderived, and then it's ready for serialization.
//!
//! For example:
//!
//! ```
//! use kson::prelude::*;
//!
//! #[derive(Clone, Debug, KsonRep)]
//! /// A silly enum, we shall make an example of it.
//! enum SillyEnum {
//!     Foo,
//!     Bar(u8, String),
//!     Baz { x: i32, y: f32 },
//! }
//!
//! let silly_example = SillyEnum::Bar(1, "hello".to_string()).to_kson();
//!
//! // encode
//! let encoded = encode_full(&silly_example);
//! ```
//!
//! If the auto-derive fails or you would like to represent the data in a particular way,
//! see [Implementing the KsonRep trait](#implementing-the-ksonrep-trait).
//!
//! # An overview of KSON types
//!
//! This section contains a brief overview of the core KSON datatypes. For details
//! about how they are encoded, see [Specification].
//!
//! ## Integers
//!
//! KSON includes signed 64-bit integers (`I64`) and BigInts (`Int`) up to $2^64$ bytes in
//! length. All other integer types will be converted to one of these integer types.
//!
//! KSON can also encode and decode `usize` and `isize` values, but this can of course
//! lead to issues if the data is being sent between machines with different word sizes.
//!
//! ```
//! use kson::prelude::*;
//!
//! // a small number
//! let small = 23u8.into_kson();
//!
//! // an (absolutely) large number
//! let large = (-99999999999999999999i128).into_kson();
//!
//! // a very large number, from a base 36
//! let very_big = BigInt::from_str_radix("zzzzzzzzzzzzzzzzzzzzzzzzzzzz", 36)
//!     .unwrap()
//!     .into_kson();
//!
//! let len = (1 as usize).into_kson();
//! ```
//!
//! See [`Inum`] for more details.
//!
//! ## Floats
//!
//! The KSON specification includes half, single, and double precision floating point
//! numbers.
//!
//! ```
//! ```
//!
//! Arbitrary precision floating point is not a core part of the format, but we intend to
//! add support for `Mpfr` through a separate crate in the near future.
//!
//! See `Float` for more details.
//!
//! ## Bytestrings
//!
//!
//! ## Arrays
//!
//! ## Maps
//!
//! # Implementing the `KsonRep` trait
//!
//!
//! # Benchmarks
//!
//! # Specification
//!
//!
//! ## Constants
//!
//! The KSON specification include

#![warn(
    missing_docs,
    deprecated_in_future,
    unsafe_code,
    unused_labels,
    keyword_idents,
    missing_doc_code_examples,
    missing_copy_implementations,
    missing_debug_implementations,
    macro_use_extern_crate,
    unreachable_pub,
    trivial_casts,
    trivial_numeric_casts,
    unused_extern_crates,
    unused_import_braces
)]
#![allow(clippy::cast_lossless)]

/// Procedural macros.
pub extern crate kson_macro;

/// KSON binary encoder and decoder.
pub mod encoding;
/// Floating-point numbers
pub mod float;
/// Integer variants.
pub mod inum;
/// Things you probably want in scope when working with `Kson`.
///
/// ```
/// use kson::prelude::*;
/// ```
pub mod prelude;
// /// Python support.
// pub mod python;
/// Types representable as `Kson`.
pub mod rep;
/// Helper functions.
mod util;
/// A wrapper around a sorted vector of pairs.
pub mod vecmap;

use bytes::{buf::FromBuf, Bytes, IntoBuf};
use float::*;
use half::f16;
use hashbrown::HashMap;
use inum::*;
use num_bigint::BigInt;
use rep::KsonRep;
use std::convert::{TryFrom, TryInto};
use vecmap::*;

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
/// KSON variants.
///
/// # Example
///
/// ```
/// use kson::prelude::*;
///
/// let b = Kson::Bool(true);
///
/// let val = match b {
///     Kson::Bool(b) => true,
///     _ => panic!(),
/// };
///
/// assert!(val);
/// ```
pub enum Kson {
    /// Null. Corresponds to `None`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let k_null = Kson::Null;
    /// ```
    Null,
    /// Boolean.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::{Kson::Bool, *};
    ///
    /// let k_bool = Bool(true);
    /// ```
    Bool(bool),
    /// Integer.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::{Kson::Kint, *};
    ///
    /// // small integer
    /// let num = Inum::I64(1);
    ///
    /// // as `Kson`
    /// let k_num = Kint(num);
    /// ```
    Kint(Inum),
    /// Bytestring type.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::{Kson::Byt, *};
    ///
    /// let bytes = Bytes::from_static(b"hello world");
    ///
    /// let k_bytes = Byt(bytes);
    /// ```
    Byt(Bytes),
    /// Array type.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::{Kson::Array, *};
    ///
    /// let k_array = Array(
    ///     vec![1, 2, 3, 4]
    ///         .into_iter()
    ///         .map(|n| n.into_kson())
    ///         .collect(),
    /// );
    /// ```
    Array(Vec<Kson>),
    /// Map type.
    ///
    /// ```
    /// use kson::prelude::{Kson::Map, *};
    ///
    /// let vmap = VecMap::from(vec![(Bytes::from_static(b"hello world"), 1.into_kson())]);
    ///
    /// let kmap = Map(vmap);
    /// ```
    Map(VecMap<Bytes, Kson>),
    /// Floating point number type.
    /// ```
    /// use kson::prelude::{Kson::Kfloat, *};
    ///
    /// let f = Float::Single(1f32.to_bits());
    ///
    /// let k_float = Kfloat(f);
    /// ```
    Kfloat(Float),
}

use Kson::*;

impl Kson {
    /// Converts a `Kson` value to a vector of `Kson`.
    /// This will return `None` if the value is not a `Kson` array.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// // a vector of numbers
    /// let numbers = vec![1, 2, 3];
    ///
    /// // convert into `Kson`
    /// let ks = numbers.into_kson();
    ///
    /// // get a vec of `Kson` values
    /// let k_numbers = ks.to_vec().unwrap();
    /// ```
    pub fn to_vec(&self) -> Option<&Vec<Kson>> {
        match self {
            Array(a) => Some(a),
            _ => None,
        }
    }

    /// Consumes a `Kson` value, converting it into a vector of `Kson`.
    /// This will return `None` if the value is not a `Kson` array.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// // a vector of numbers
    /// let numbers = vec![1, 2, 3];
    ///
    /// // convert into `Kson`
    /// let ks = numbers.into_kson();
    ///
    /// // get a vec of `Kson` values
    /// let k_numbers = ks.into_vec().unwrap();
    /// ```
    pub fn into_vec(self) -> Option<Vec<Kson>> { self.try_into().ok() }

    /// Converts a `Kson` value to a `VecMap`.
    /// This will return `None` if the value is a not a `Kson` map.
    ///
    /// # Example
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use kson::prelude::*;
    ///
    /// // intialize `HashMap` and insert one key-value pair
    /// let mut simple_map = HashMap::new();
    /// simple_map.insert(Bytes::from("foo"), 1);
    ///
    /// // convert map into `Kson`
    /// let k_map = simple_map.into_kson();
    ///
    /// // convert `Kson` to `VecMap`
    /// let vmap = k_map.to_vecmap();
    /// ```
    pub fn to_vecmap(&self) -> Option<&VecMap<Bytes, Kson>> {
        match self {
            Map(vmap) => Some(vmap),
            _ => None,
        }
    }

    /// Consumes a `Kson` value, converting it into a `HashMap`.
    /// This will return `None` if the value is a not a `Kson` map.
    ///
    /// # Example
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use kson::prelude::*;
    ///
    /// // initialize `HashMap` and insert one key-value pair
    /// let mut simple_map = HashMap::new();
    /// simple_map.insert(Bytes::from("foo"), 1);
    ///
    /// // convert map into `Kson`
    /// let k_map = simple_map.into_kson();
    ///
    /// // convert `Kson` into `VecMap`.
    /// let vmap = k_map.into_vecmap();
    /// ```
    pub fn into_vecmap(self) -> Option<VecMap<Bytes, Kson>> { self.try_into().ok() }

    /// Consumes a `Kson` value, converting it into a `HashMap`.
    /// This will return `None` if the value is a not a `Kson` map.
    ///
    /// # Example
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use kson::prelude::*;
    ///
    /// // intialize `HashMap` and insert one key-value pair
    /// let mut simple_map = HashMap::new();
    /// simple_map.insert(Bytes::from("foo"), 1);
    ///
    /// // convert map into `Kson`
    /// let k_map = simple_map.into_kson();
    ///
    /// // convert `Kson` into `HashMap`
    /// let vmap = k_map.into_map();
    /// ```
    pub fn into_map(self) -> Option<HashMap<Bytes, Kson>> {
        Some(self.into_vecmap()?.into_hashmap())
    }

    /// Consumes a `Kson` value, converting it to a value of type `T`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// // number as `Kson`
    /// let ks_num = 1.to_kson();
    ///
    /// // convert `Kson` into u8
    /// let num: u8 = ks_num.into_rep().unwrap();
    ///
    /// // should be equal
    /// assert_eq!(num, 1);
    /// ```
    pub fn into_rep<T: KsonRep>(self) -> Option<T> { T::from_kson(self) }

    /// Converts a bytestring literal to `Kson`.
    ///
    /// # Example
    /// ```
    /// use kson::prelude::*;
    ///
    /// // bytesting literal
    /// let foo = b"this is an example";
    ///
    /// // convert to `Kson`
    /// let ks_foo = Kson::from_static(foo);
    /// ```
    pub fn from_static(bytes: &'static [u8]) -> Kson { Byt(Bytes::from_static(bytes)) }

    /// Indicates whether a value is `Null`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::Kson::Null;
    ///
    /// let foo = Null;
    ///
    /// assert!(foo.is_null());
    /// ```
    pub fn is_null(&self) -> bool {
        match self {
            Null => true,
            _ => false,
        }
    }

    /// Tries to convert value to an `Inum`.
    /// This will return `None` if the value is not an `Inum`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let ks_num = 1.into_kson();
    ///
    /// let n = u64::try_from(ks_num.to_inum().unwrap().clone()).unwrap();
    ///
    /// assert_eq!(n, 1);
    /// ```
    pub fn to_inum(&self) -> Option<&Inum> {
        match self {
            Kint(i) => Some(i),
            _ => None,
        }
    }

    /// Consumes the value, converting it to an `Inum`.
    /// This will return `None` if the value is not an `Inum`.
    pub fn into_inum(self) -> Option<Inum> {
        match self {
            Kint(i) => Some(i),
            _ => None,
        }
    }

    /// Tries to convert value to a `bool`.
    /// This will return `None` if the value is not a `Kson` bool.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let b = true.into_kson();
    ///
    /// // should be `true`
    /// assert!(b.to_bool().unwrap());
    /// ```
    pub fn to_bool(&self) -> Option<bool> {
        match self {
            Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Tries to convert value to `Bytes`.
    /// This will return `None` if the value is not a `Kson` bytestring.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::Kson;
    ///
    /// let foo = Kson::from_static(b"This is an example");
    ///
    /// let foo_bytes = foo.to_bytes().unwrap();
    /// ```
    pub fn to_bytes(&self) -> Option<&Bytes> {
        match self {
            Byt(s) => Some(s),
            _ => None,
        }
    }
}

impl FromBuf for Kson {
    fn from_buf<T>(buf: T) -> Self
    where
        T: IntoBuf,
    {
        Byt(Bytes::from_buf(buf.into_buf()))
    }
}

impl From<String> for Kson {
    fn from(s: String) -> Kson { s.into_kson() }
}

impl From<char> for Kson {
    fn from(c: char) -> Kson { c.into_kson() }
}

impl<T: Into<Kson>> From<Vec<T>> for Kson {
    fn from(v: Vec<T>) -> Kson { Array(v.into_iter().map(T::into).collect()) }
}

impl<T: Into<Kson>> From<VecMap<Bytes, T>> for Kson {
    fn from(v: VecMap<Bytes, T>) -> Kson {
        Map(v.into_iter().map(|(k, v)| (k, v.into())).collect())
    }
}

// bool -> Kson, From
from_fn!(Kson, bool, Bool);
// bool -> Kson, TryFrom
try_from_ctor!(Kson, bool, Bool);

// Inum -> Kson, From
from_fn!(Kson, Inum, Kint);
// Inum -> Kson, TryFrom
try_from_ctor!(Kson, Inum, Kint);

// Bytes -> Kson, From
from_fn!(Kson, Bytes, Byt);
// Bytes -> Kson, TryFrom
try_from_ctor!(Kson, Bytes, Byt);

// Float -> Kson, From
from_fn!(Kson, Float, Kfloat);
// Float -> Kson, TryFrom
try_from_ctor!(Kson, Float, Kfloat);

// Bytes -> Kson, TryFrom
try_from_ctor!(Kson, Vec<Kson>, Array);
try_from_ctor!(Kson, VecMap<Bytes, Kson>, Map);

// Integers
compose_from!(Kson, Inum, BigInt);
compose_from!(Kson, Inum, isize);
compose_from!(Kson, Inum, usize);
compose_from!(Kson, Inum, i64);
compose_from!(Kson, Inum, u64);
compose_from!(Kson, Inum, i128);
compose_from!(Kson, Inum, u128);
from_prims!(Kson);

// Floats
compose_from!(Kson, Float, f32);
compose_from!(Kson, Float, f64);
compose_from!(Kson, Float, f16);

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
