//! # KSON
//!
//! KSON (Kalix Serializable Object Notation) is a serialization format designed to be
//! efficient, complete, concise, and easy to implement.
//!
//! # Usage
//!
//! The trait [`KsonRep`] is used to specify how data is converted into [`Kson`].
//!
//! This trait can usually be auto-derived, and then it's ready for serialization.
//!
//! For example:
//!
//! ```
//! use kson::prelude::*;
//!
//! #[derive(Clone, Debug, KSerDe, PartialEq)]
//! /// A silly enum, we shall make an example of it.
//! enum SillyEnum {
//!     Foo,
//!     Bar(u8, String),
//!     Baz { x: i32, y: f32 },
//! }
//!
//! let silly_example = SillyEnum::Bar(1, "hello".to_string());
//!
//! // encode TODO implement KSerDe for references
//! let encoded = &mut encode_full(silly_example.clone()).into_buf();
//!
//! // and then immediately decode, because this is a silly example
//! let decoded: SillyEnum = decode(encoded).unwrap();
//!
//! assert_eq!(silly_example, decoded);
//! ```
//!
//! If the auto-derive fails or you would like to represent the data in a particular way,
//! see [Implementing the KsonRep trait](#implementing-the-ksonrep-trait).
//!
//! # An overview of KSON types
//!
//! This section contains a brief overview of the core KSON data types. For details
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
//! The KSON specification includes half, single, and double precision floating-point
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
//! Arbitrary precision floating-point is not a core part of the format, but we intend to
//! add support for [MPFR](https://en.wikipedia.org/wiki/GNU_MPFR) arbitrary precision floats
//! through a separate crate in the near future.
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
//! use std::collections::HashMap;
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
//! While auto-deriving [`KsonRep`] is [usually a better idea](#usage), it is fairly
//! straight-forward, if not a bit tedious, to implement it by hand. An example:
//!
//! ```
//! use kson::prelude::*;
//! use std::collections::HashMap;
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
//!     fn to_kson(&self) -> Kson {
//!         match self {
//!             SillyEnum::Foo => vec![Kson::from("Foo")].into_kson(), // just the name for unit-like structs
//!             SillyEnum::Bar(n, s) => {
//!                 vec![
//!                     Kson::from("Bar"), // name
//!                     n.to_kson(),     // first field
//!                     s.to_kson(),     // second field
//!                 ]
//!                 .into_kson() // convert the vector into a `Kson` array
//!             }
//!             SillyEnum::Baz { x, y } => {
//!                 vec![
//!                     Kson::from("Baz"), // name
//!                     VecMap::from_sorted(
//!                         // construct map
//!                         vec![
//!                             (Bytes::from("x"), x.to_kson()), // first field
//!                             (Bytes::from("y"), y.to_kson()), // second field
//!                         ],
//!                     )
//!                     .into_kson(), // into a KSON map
//!                 ]
//!                 .into_kson() // convert the vector into `Kson`
//!             }
//!         }
//!     }
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
//!     fn from_kson(ks: Kson) -> Result<SillyEnum, Error> {
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
//!                     bail!("Unit-like variants shouldn't have fields!")
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
//!                     bail!("Found too many fields!")
//!                 }
//!             }
//!             "Baz" => {
//!                 let mut fields: HashMap<Bytes, Kson> = pop_kson(ks_iter)?;
//!                 
//!                 // there should be exactly two fields
//!                 if fields.len() != 2 {
//!                     bail!("Found the wrong number of fields!")
//!                 }
//!                 
//!                 // and ks_iter should be exhausted
//!                 if ks_iter.len() > 0 {
//!                     bail!("Found too many fields!")
//!                 }
//!
//!                 // get the fields
//!                 let x = i32::from_kson(fields.remove(&Bytes::from("x")).ok_or(format_err!("Field not found"))?)?;
//!                 let y =
//!                 f32::from_kson(fields.remove(&Bytes::from("y")).ok_or(format_err!("Field not found"))?)?;
//!
//!                 Ok(SillyEnum::Baz { x, y})                 
//!             }
//!             _ => bail!("This isn't a variant") // catch-all
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

#![allow(warnings)]
// #![warn(
// //    missing_docs,
//     deprecated_in_future,
//     unsafe_code,
//     unused_labels,
//     keyword_idents,
//     missing_doc_code_examples,
//     missing_copy_implementations,
//     missing_debug_implementations,
//     macro_use_extern_crate,
//     unreachable_pub,
//     trivial_casts,
//     trivial_numeric_casts,
//     unused_extern_crates,
//     unused_import_braces
// )]
#![allow(clippy::cast_lossless)]
#![allow(clippy::expect_fun_call)]

pub mod encoding;
pub mod float;
pub mod inum;
pub mod prelude;
mod util;

use bytes::{buf::FromBuf, Bytes, IntoBuf};
use failure::*;
use float::*;
use half::f16;
use inum::*;
use num_bigint::BigInt;
use std::{
    collections::HashMap,
    convert::{TryFrom, TryInto},
};
pub(crate) use womp::womp;
