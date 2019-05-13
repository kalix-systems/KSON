// TODO update docstrings to reflect better error handling

//! # KSON
//!
//! KSON (Kalix Serializable Object Notation) is a serialization format designed to be
//! efficient, complete, concise, and easy to implement.
//!
//! # Usage
//!
//! The trait [`KsonRep`] is used to specify how data is converted into [`Kson`].
//!
//! This trait can usually be autoderived, and then it's ready for serialization.
//!
//! For example:
//!
//! ```
//! use kson::prelude::*;
//!
//! #[derive(Clone, Debug, KsonRep, PartialEq)]
//! /// A silly enum, we shall make an example of it.
//! enum SillyEnum {
//!     Foo,
//!     Bar(u8, String),
//!     Baz { x: i32, y: f32 },
//! }
//!
//! let silly_example = SillyEnum::Bar(1, "hello".to_string());
//!
//! // encode
//! let encoded = &mut encode_full(&silly_example.to_kson()).into_buf();
//!
//! // and then immediately decode, because this is a silly exaple
//! let decoded = SillyEnum::from_kson(decode(encoded).unwrap()).unwrap();
//!
//! assert_eq!(silly_example, decoded);
//! ```
//!
//! If the auto-derive fails or you would like to represent the data in a particular way,
//! see [Implementing the KsonRep trait](#implementing-the-ksonrep-trait).
//!
//! # An overview of KSON types
//!
//! This section contains a brief overview of the core KSON datatypes. For details
//! about how they are encoded, see [Specification](#specification).
//!
//! ## Integers
//!
//! KSON includes signed 64-bit integers ([`Inum::I64`]) and BigInts ([`Inum::Int`]) up to
//! `2^64` bytes in length. All other integer types will be converted to one of these
//! integer types.
//!
//! KSON can also encode and decode [`usize`] and [`isize`] values, but this can of course
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
//! See also: [`Inum`] and [the integer specification](#integers-1).
//!
//! ## Floats
//!
//! The KSON specification includes half, single, and double precision floating point
//! numbers.
//!
//! ```
//! use kson::prelude::*;
//!
//! let half = f16::from_f32(1.0).into_kson();
//!
//! let single = 1f32.into_kson();
//!
//! let double = 1f64.into_kson();
//! ```
//!
//! Arbitrary precision floating point is not a core part of the format, but we intend to
//! add support for [MPFR](https://en.wikipedia.org/wiki/GNU_MPFR) arbitrary precision floating
//! points through a separate crate in the near future.
//!
//! See also [`Float`] and the [float specification](#float-1).
//!
//! ## Bytestrings
//!
//! ```
//! use kson::prelude::*;
//!
//! let a_str = Kson::from("hello world");
//!
//! let literal = Kson::from_static(b"this is a bytestring literal");
//!
//! let a_string = "This is a string".to_string().into_kson();
//! ```
//!
//! See also: [`Bytes`] and the [bytestring specification](#bytestrings-1).
//!
//! ## Arrays
//!
//! Arrays are sequences of KSON objects.
//!
//! ```
//! use kson::prelude::*;
//!
//! let some_numbers = vec![1, 2, 3, 4, 5].into_kson();
//! ```
//!
//! See also: the [array specification](#arrays-1).
//!
//! ## Maps
//!
//! Maps are mappings from keys to values, serialized based on their [`VecMap`]
//! representation.
//!
//! ```
//! use hashbrown::HashMap;
//! use kson::prelude::*;
//!
//! let mut a_map = HashMap::new();
//!
//! a_map.insert(Bytes::from_static(b"key"), 250);
//!
//! let k_map = a_map.into_kson();
//! ```
//!
//! See also: [`VecMap`] and the [map specification](#maps-1).
//!
//! # Implementing the `KsonRep` trait
//!
//! While autoderiving [`KsonRep`] is [usually a better idea](#usage), it is fairly
//! straightforward, if not a bit tedious, to implement by hand. An example:
//!
//! ```
//! use kson::prelude::*;
//! use hashbrown::HashMap;
//!
//! #[derive(Clone)]
//! /// This is, again, a silly enum.
//! enum SillyEnum {
//!     Foo,
//!     Bar(u8, String),
//!     Baz { x: i32, y: f32 },
//! }
//!
//! impl KsonRep for SillyEnum {
//!     fn into_kson(self) -> Kson {
//!         match self {
//!             SillyEnum::Foo => vec![Kson::from("Foo")].into_kson(), // just the name for unit-like structs
//!             SillyEnum::Bar(n, s) => {
//!                 vec![
//!                     Kson::from("Bar"), // name
//!                     n.into_kson(),     // first field
//!                     s.into_kson(),     // second field
//!                 ]
//!                 .into_kson() // convert the vector into a `Kson` array
//!             }
//!             SillyEnum::Baz { x, y } => {
//!                 vec![
//!                     Kson::from("Baz"), // name
//!                     VecMap::from_sorted(
//!                         // construct map
//!                         vec![
//!                             (Bytes::from("x"), x.into_kson()), // first field
//!                             (Bytes::from("y"), y.into_kson()), // second field
//!                         ],
//!                     )
//!                     .into_kson(), // into a KSON map
//!                 ]
//!                 .into_kson() // convert the vector into `Kson`
//!             }
//!         }
//!     }
//!
//!     fn from_kson(ks: Kson) -> Result<SillyEnum, KsonConversionError> {
//!         let ks_iter = &mut ks.into_vec()?.into_iter();
//!         
//!         let name: String = pop_kson(ks_iter)?;
//!
//!         match name.as_str() {
//!             "Foo" => {
//!                 // it shouldn't have any fields
//!                 if ks_iter.len() == 0 {
//!                     Ok(SillyEnum::Foo)
//!                 } else {
//!                     // if it *does*, presumably something went wrong
//!                     Err(KsonConversionError::new("Unit-like variants shouldn't have fields!"))
//!                 }
//!             }
//!             "Bar" => {
//!                 // get the fields
//!                 let n = pop_kson(ks_iter)?;
//!                 let s = pop_kson(ks_iter)?;
//!
//!                 if ks_iter.len() == 0 {
//!                     Ok(SillyEnum::Bar(n, s))
//!                 } else {
//!                     Err(KsonConversionError::new("Found too many fields!"))
//!                 }
//!             }
//!             "Baz" => {
//!                 let mut fields: HashMap<Bytes, Kson> = pop_kson(ks_iter)?;
//!                 
//!                 // there should be exactly two fields
//!                 if fields.len() != 2 {
//!                     return Err(KsonConversionError::new("Found the wrong number of fields!"))
//!                 }
//!                 
//!                 // and ks_iter should be exhausted
//!                 if ks_iter.len() > 0 {
//!                     return Err(KsonConversionError::new("Found too many fields!"))
//!                 }
//!
//!                 // get the fields
//!                 let x = i32::from_kson(fields.remove(&Bytes::from("x")).ok_or(KsonConversionError::new("Field not found"))?)?;
//!                 let y =
//!                 f32::from_kson(fields.remove(&Bytes::from("y")).ok_or(KsonConversionError::new("Field not found"))?)?;
//!
//!                 Ok(SillyEnum::Baz { x, y})                 
//!             }
//!             _ => Err(KsonConversionError::new("This isn't a variant")) // catch-all
//!         }
//!     }
//! }
//! ```
//!
//! If this example makes you sad (it has that effect on us), see [Usage](#usage).
//!
//! # Benchmarks
//!
//! # Specification
//!
//! This section describes the KSON binary format.
//!
//! ## Tags
//!
//! The first byte of every Kson object is called the *tag*. The first 3 bits of the tag
//! are called the *type*, with the remaining 5 bits being *metadata*.
//!
//! ## Constants
//!
//! Constants are values that fit into a tag byte. Their type is `000`. While KSON can
//! support up to `2^6-1 = 63` constants, we currently use only three. These are
//! summarized in the table below.
//!
//! | Metadata | Semantics |
//! | ---      | ---       |
//! | `00000`  | `null`    |
//! | `00001`  | `true`    |
//! | `00010`  | `false`   |
//!
//! ## Integers
//!
//! Integers are whole numbers with length in bytes up to `2^64`.
//! Their tag byte is constructed as follows:
//!
//! | 001  | x                      | x        | xxx             |
//! | ---  | --                     | ---      | --              |
//! | Type | Small (0) or large (1) | Sign bit | Length in bytes |
//!
//! For small integers, the length bits encode the length of the integer itself, starting
//! at 1. For large integers, the length bits encode the length of the length of the
//! integer, starting at 9.
//!
//! The digits of the integer are encoded in little endian order as a sequence
//! of bytes. When the sign bit is negative, the digits are encoded as `-(n + 1)`, where
//! the magnitude is `n`.
//!
//! ## Bytestrings
//!
//! Bytestrings are sequences of bytes with length up to `2^128`.
//! Their tag byte is constructed as follows:
//!
//! | 010  | x              | xxxx            |
//! | ---  | --             | --              |
//! | Type | Small or large | Length in bytes |
//!
//! For small strings, the length bits correspond to the length in bytes of the string
//! itself, starting at 0. For large strings, the length bits correspond to the length in
//! bytes of the length of the string in bytes, starting at 16.
//!
//! ## Arrays
//!
//! Arrays are sequences of KSON items with length up to `2^128`.
//! Their tag byte is constructed as follows:
//!
//! | 011  | x              | xxxx            |
//! | ---  | --             | --              |
//! | Type | Small or large | Length in items |
//!
//! For small arrays, the length bits correspond to the length in items of the array
//! itself, starting at 0. For large arrays, the length bits correspond to the length in
//! bytes of the length of the array in items, starting at 16.
//!
//! ## Maps
//!
//! Maps are sequences of `(key, value)` pairs where keys are tagged bytestrings and
//! values are KSON items with length up to `2^128`. Their tag byte is constructed as
//! follows:
//!
//! | 100  | x              | xxxx            |
//! | ---  | --             | --              |
//! | Type | Small or large | Length in pairs |
//!
//! For small maps, the length bits correspond to the length in pairs of the map itself,
//! starting at 0. For large maps, the length bits correspond to the length in bytes of
//! the length of the map in pairs, starting at 16.
//!
//! ## Floats
//!
//! Floats are encoded according to [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754).
//!
//! Their tag byte is constructed as follows:
//!
//! | 101  | xx                                  | xxx              |
//! | ---  | ---                                 | ---              |
//! | Type | Half (00), Single (01), Double (10) | Currently Unused |

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

/// Procedural macros for autoderiving `KsonRep`.
pub extern crate kson_macro;

/// KSON binary encoder and decoder.
pub mod encoding;
/// Floating-point numbers
pub mod float;
/// Integer variants.
pub mod inum;
/// Things you probably want in scope when working with `Kson`.
pub mod prelude;
// /// Python support.
// pub mod python;
pub mod errors;
/// Types representable as `Kson`.
pub mod rep;
/// Helper functions.
mod util;
/// A wrapper around a sorted vector of pairs.
pub mod vecmap;

use bytes::{buf::FromBuf, Bytes, IntoBuf};
use errors::KsonConversionError;
use float::*;
use half::f16;
use hashbrown::HashMap;
use inum::*;
use num_bigint::BigInt;
use rep::KsonRep;
use std::convert::{TryFrom, TryInto};
use vecmap::*;

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
/// `Kson` and its variants.
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
    pub fn to_vec(&self) -> Result<&Vec<Kson>, KsonConversionError> {
        match self {
            Array(a) => Ok(a),
            _ => Err(KsonConversionError::new("This value is not an `Array`")),
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
    pub fn into_vec(self) -> Result<Vec<Kson>, KsonConversionError> {
        // TODO return a sane error message
        self.try_into()
            .map_err(|_| KsonConversionError::new("This value is not an `Array`"))
    }

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
    pub fn to_vecmap(&self) -> Result<&VecMap<Bytes, Kson>, KsonConversionError> {
        match self {
            Map(vmap) => Ok(vmap),
            _ => Err(KsonConversionError::new("This value is not a `Map`")),
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
    pub fn into_vecmap(self) -> Result<VecMap<Bytes, Kson>, KsonConversionError> {
        // TODO error message
        self.try_into()
            .map_err(|_| errors::KsonConversionError::new("This value is not a `Map`"))
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
    pub fn into_map(self) -> Result<HashMap<Bytes, Kson>, errors::KsonConversionError> {
        Ok(self.into_vecmap()?.into_hashmap())
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
    pub fn into_rep<T: KsonRep>(self) -> Result<T, KsonConversionError> { T::from_kson(self) }

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
    pub fn to_inum(&self) -> Result<&Inum, KsonConversionError> {
        match self {
            Kint(i) => Ok(i),
            _ => {
                Err(KsonConversionError::new(
                    "Value is not `Kint`, cannot convert to `Inum`",
                ))
            }
        }
    }

    /// Consumes the value, converting it to an `Inum`.
    /// This will return `None` if the value is not an `Inum`.
    pub fn into_inum(self) -> Result<Inum, KsonConversionError> {
        match self {
            Kint(i) => Ok(i),
            _ => {
                Err(KsonConversionError::new(
                    "Value is not `Kint`, cannot convert to `Inum`",
                ))
            }
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
    pub fn to_bool(&self) -> Result<bool, KsonConversionError> {
        match self {
            Bool(b) => Ok(*b),
            _ => Err(KsonConversionError::new("Value is not `Bool`")),
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
    pub fn to_bytes(&self) -> Result<&Bytes, KsonConversionError> {
        match self {
            Byt(s) => Ok(s),
            _ => Err(KsonConversionError::new("Value is not a bytestring")),
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

impl From<&str> for Kson {
    fn from(s: &str) -> Kson { s.to_string().into_kson() }
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

        assert!(5.to_kson().to_inum().is_ok());

        assert!(true.to_kson().to_bool().unwrap());

        assert_eq!(
            Bytes::from("word").to_kson().to_bytes().unwrap(),
            &Bytes::from("word")
        );
    }

    #[test]
    fn from_vec() {
        let v: Vec<u8> = vec![0, 1, 2, 3, 4];
        let val: Vec<u8> = Kson::from(v.clone()).into_rep().unwrap();
        assert_eq!(val, v);
    }
}
