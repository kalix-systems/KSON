//! # KSON
//!
//! KSON (Kalix Serializable Object Notation) is a serialization format designed to be
//! efficient, complete, concise, and easy to implement.
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

// #![allow(warnings)]
#![warn(
//    missing_docs,
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
#![allow(clippy::expect_fun_call)]

pub mod encoding;
pub mod float;
pub mod inum;
pub mod prelude;
mod util;
