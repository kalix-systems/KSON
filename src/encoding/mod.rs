//! # KSON binary encoder and decoder
//!
//! Encode and decode functions for KSON.
//!
//! # Example
//!
//! ```
//! use kson::prelude::*;
//!
//! // a struct that will store some data
//! #[derive(KsonRep, PartialEq, Debug, Clone)]
//! struct SomeData {
//!     x: usize,
//!     y: i32,
//! }
//!
//! // here it is storing some data
//! let some_data = SomeData { x: 1, y: 2 };
//!
//! // and we've encoded it
//! let enc_full = encode_full(&some_data.to_kson());
//!
//! // let's encode it a different way too
//!
//! // create a buffer
//! let out = &mut Vec::new();
//!
//! // and we've encoded it a different way
//! encode(&some_data.to_kson(), out);
//!
//! // but they are equivalent
//! assert_eq!(*out, enc_full);
//!
//! // Note: decoding returns a `Result`
//! let dec_ks: Kson = decode_full(&enc_full).unwrap(); // did the decoding succeed?
//! let dec_full: SomeData = dec_ks.into_rep().unwrap(); // did the conversion succeed?
//!
//! // success!
//! assert_eq!(dec_full, some_data);
//! ```

#![allow(clippy::inconsistent_digit_grouping)]
use crate::{
    util::*,
    vecmap::VecMap,
    Float::*,
    Inum::{self, *},
    Kson::{self, *},
};
use bytes::{Buf, Bytes, IntoBuf};
use failure::Error;

pub mod ser;
pub use ser::*;
pub mod de;
pub use de::*;
mod constants;
use constants::*;

// TODO: replace len vecs w/ heapless vec of size at most 8
/// Encode [`Kson`] into its binary representation, storing output in `out`.
///
/// # Arguments
///
/// * `ks: &Kson` - A reference to the [`Kson`] value to be encoded.
/// * `out: &mut Vec<u8>` - A mutable reference to [`Bytes`] where the encoder output will
///   be stored.
///
/// # Example
///
/// ```
/// use kson::prelude::*;
///
/// // output buffer
/// let out = &mut Vec::new();
/// // value to encode
/// let ks = Kson::Null;
///
/// // encode value
/// encode(&ks, out);
/// ```
pub fn encode<T: Ser>(t: T, out: &mut Vec<u8>) { t.ser(out) }

/// Tries to decode a buffer into [`Kson`].
///
/// # Arguments
///
/// * `data` - A buffer containing binary encoded KSON.
///
/// # Example
///
/// ```
/// use kson::prelude::*;
///
/// // encoded value
/// let k_null = &mut encode_full(&Kson::Null).into_buf();
///
/// // Did the decoding succeed?
/// let dec: Kson = match decode_full(k_null) {
///     Ok(value) => value,
///     Err(_e) => panic!("Oh no. Whatever will I do?"),
/// };
///
/// // should be equal
/// assert_eq!(dec, Kson::Null);
/// ```
pub fn decode<D: Deserializer, T: De>(data: &mut D) -> Result<T, Error> { T::de(data) }

/// Encodes a [`Kson`] object into a vector of bytes.
///
/// # Arguments
///
/// * `ks` - A reference to the [`Kson`] value to be encoded.
///
/// # Example
///
/// ```
/// use kson::prelude::*;
///
/// // value to encode
/// let ks = Kson::Null;
///
/// // encoded value
/// let enc: Vec<u8> = encode_full(&ks);
/// ```
pub fn encode_full<T: Ser>(t: T) -> Vec<u8> {
    let mut out = Vec::new();
    t.ser(&mut out);
    out
}

/// Decodes a bytestring into [`Kson`], returns an error if decoding fails.
///
/// # Arguments
///
/// * `bs` - A buffer containing the bytestring to be decoded.
///
/// # Example
///
/// ```
/// use kson::{prelude::*, Kson::Null};
///
/// // encoded value
/// let bs = encode_full(&Null);
///
/// // decode value
/// let dec: Result<Kson, failure::Error> = decode_full(&bs);
/// ```
pub fn decode_full<B: IntoBuf, T: De>(bs: B) -> Result<T, Error> { decode(&mut bs.into_buf()) }

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use std::ops::Neg;

    #[test]
    fn inum_meta_no_sign() {
        let n = Kson::from(0);
        let out = encode_full(&n);

        // tag
        assert_eq!(out[0], 0b001_0_1_000);
        // digit, should be 0
        assert_eq!(out[1], 0);
    }

    #[test]
    fn inum_meta_small_pos_one_byte() {
        let small_pos = Kson::from(1);
        let out = encode_full(&small_pos);

        // tag
        assert_eq!(out[0], 0b001_0_1_000);
        // digit, should be 1
        assert_eq!(out[1], 1);
    }

    #[test]
    fn inum_meta_small_pos_two_bytes() {
        let small_pos = Kson::from(257);
        let out = encode_full(&small_pos);

        // tag
        assert_eq!(out[0], 0b001_0_1_001);
        // LSD, should be 1
        assert_eq!(out[1], 1);
        // MSD, should be 1
        assert_eq!(out[2], 1);
    }

    #[test]
    fn inum_meta_small_pos_eight_bytes() {
        let small_pos = Kson::from(i64::max_value());
        let out = encode_full(&small_pos);

        assert_eq!(out[0], 0b001_0_1_111);
        assert_eq!(out[1..], [255, 255, 255, 255, 255, 255, 255, 127]);
    }

    #[test]
    fn inum_meta_small_neg_one_byte() {
        let small_neg = Kson::from(-2);
        let out = encode_full(&small_neg);

        // tag
        assert_eq!(out[0], 0b0010_0_000);
        // should be 0
        assert_eq!(out[1], 1);
    }

    #[test]
    fn inum_meta_small_neg_two_byte() {
        let small_neg = Kson::from(-257);
        let out = encode_full(&small_neg);

        // tag
        assert_eq!(out[0], 0b001_0_0_001);
        // LSD, should be 0
        assert_eq!(out[1], 0);
        // MSD, should be 1
        assert_eq!(out[2], 1);
    }

    #[test]
    fn inum_meta_small_neg_eight_bytes() {
        let small_neg = Kson::from(i64::min_value());
        let out = encode_full(&small_neg);

        // tag
        assert_eq!(out[0], 0b001_0_0_111);
        assert_eq!(out[1..], [255, 255, 255, 255, 255, 255, 255, 127]);
    }

    #[test]
    fn inum_meta_big_pos() {
        let big_pos = Kson::from(BigInt::from(u64::max_value()) + 1);
        let out = encode_full(&big_pos);

        // tag
        assert_eq!(out[0], 0b001_1_1_000,);
        // length in bytes
        assert_eq!(out[1], 0);
        // digits
        assert_eq!(out[2..], [0, 0, 0, 0, 0, 0, 0, 0, 1]);
    }

    #[test]
    fn inum_meta_big_neg() {
        let big_neg = Kson::from(BigInt::from(u64::max_value()).neg() - 2);
        let out = encode_full(&big_neg);

        // tag
        assert_eq!(out[0], 0b0011_0000);
        // length in bytes
        assert_eq!(out[1], 0);
        // digits
        assert_eq!(out[2..], [0, 0, 0, 0, 0, 0, 0, 0, 1]);
    }
    #[test]
    fn constants() {
        let out = encode_full(&Null);

        assert_eq!(out[0], CON_NULL);
        assert_eq!(out.len(), 1);

        let out = encode_full(&Kson::from(true));

        assert_eq!(out[0], CON_TRUE);
        assert_eq!(out.len(), 1);

        let out = encode_full(&Kson::from(false));

        assert_eq!(out[0], CON_FALSE);
        assert_eq!(out.len(), 1);
    }

    #[test]
    fn small_string() {
        let small_bs = Kson::from_static(b"w");

        let out = encode_full(&small_bs);

        // tag
        assert_eq!(out[0], 0b010_0_0001);
        // characters
        assert_eq!(out[1], 119);
    }

    #[test]
    fn large_string() {
        let large_bs = Kson::from_static(&[b'w'; 140]);

        let out = encode_full(&large_bs);

        // tag
        assert_eq!(out[0], 0b010_1_0000);
        // length
        assert_eq!(out[1], 140 - BIG_BIT);
        // bytes
        assert_eq!(out[2..].to_vec(), vec![b'w'; 140]);
    }

    #[test]
    fn small_array() {
        let small_array = Kson::from(vec![0]);

        let out = encode_full(&small_array);

        // tag
        assert_eq!(out[0], 0b011_0_0001);
        // element tag
        assert_eq!(out[1], 0b001_0_1_000);
        // check that the value is right
        assert_eq!(out[2], 0);
    }

    #[test]
    fn large_array() {
        let large_array = Kson::from(vec![0; 140]);

        let out = encode_full(&large_array);

        // tag
        assert_eq!(out[0], 0b011_1_0000);
        // length
        assert_eq!(out[1], 140 - BIG_BIT);

        // element tags
        let out_tags: Vec<&u8> = out[2..].iter().step_by(2).collect();
        assert_eq!(out_tags, vec![&0b001_0_1_000; 140]);

        let out_vals: Vec<&u8> = out[3..].iter().step_by(2).collect();
        assert_eq!(out_vals, vec![&0; 140]);
    }

    #[test]
    fn small_map() {
        let small_map = Kson::from(VecMap::from_sorted(vec![(
            Bytes::from_static(b"a"),
            Bytes::from_static(b"b"),
        )]));

        let out = encode_full(&small_map);

        // tag
        assert_eq!(out[0], 0b100_0_0001);
        // element tags
        assert_eq!(vec![out[1], out[3]], vec![0b010_0_0001, 0b010_0_0001]);
        // check that the values are right
        assert_eq!(vec![out[2], out[4]], vec![b'a', b'b']);
    }

    #[test]
    fn large_map() {
        let large_map = Kson::from(VecMap::from_sorted(
            (0..140)
                .map(|x| (Bytes::from(vec![x as u8]), Bytes::from(vec![x as u8])))
                .collect(),
        ));

        let out = encode_full(&large_map);

        // tag
        assert_eq!(out[0], 0b100_1_0000);
        // length
        assert_eq!(out[1], 140 - BIG_BIT);

        // key tags
        out[2..]
            .iter()
            .step_by(4)
            .for_each(|x| assert_eq!(*x, 0b010_0_0001));

        // val tags
        out[4..]
            .iter()
            .step_by(4)
            .for_each(|x| assert_eq!(*x, 0b010_0_0001));

        // keys
        out[3..]
            .iter()
            .step_by(4)
            .enumerate()
            .for_each(|(i, x)| assert_eq!(*x as usize, i));

        // values
        out[5..]
            .iter()
            .step_by(4)
            .enumerate()
            .for_each(|(i, x)| assert_eq!(*x as usize, i));
    }

    #[test]
    fn half_float() {
        let f = half::f16::from_f32(1.0);
        let kf = Kson::from(f);

        let out = encode_full(&kf);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b00_1111_00]);

        let f = half::f16::from_f32(-1.0);
        let kf = Kson::from(f);

        let out = encode_full(&kf);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b10_1111_00]);

        let f = half::f16::from_f32(-0.0);
        let kf = Kson::from(f);

        let out = encode_full(&kf);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b1_000_0000]);

        let f = half::f16::from_f32(65504.0);
        let kf = Kson::from(f);

        let out = encode_full(&kf);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0b1111_1111, 0b0111_1011]);
    }

    #[test]
    fn single_floats() {
        let f = 1f32;
        let kf = Kson::from(f);

        let out = encode_full(&kf);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0b1000_0000, 0b0011_1111]);

        let f = -1f32;
        let kf = Kson::from(f);

        let out = encode_full(&kf);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0b1000_0000, 0b1011_1111]);

        let f = -0f32;
        let kf = Kson::from(f);

        let out = encode_full(&kf);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0, 0b1_000_0000]);
    }

    #[test]
    fn double_floats() {
        let f = 1f64;
        let kf = Kson::from(f);

        let out = encode_full(&kf);

        // tag
        assert_eq!(out[0], DOUBLE);

        // bytes
        assert_eq!(out[1..9], [0, 0, 0, 0, 0, 0, 0b1111_0000, 0b0011_1111]);
    }

    #[test]
    // for completeness
    fn trivial() {
        assert!((&mut Vec::new().into_buf()).read_many(3).is_err());

        assert!((&mut Vec::new().into_buf()).read_uint(3).is_err());

        // assert!(decode(&mut vec![0b0000_0011].into_buf()).is_err());
    }
}
