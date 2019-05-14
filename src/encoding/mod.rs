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
//! let dec_full: SomeData = decode(&mut enc_full.into_buf())
//!     .unwrap() // did the decoding succeed?
//!     .into_rep() // convert into `SomeData`
//!     .unwrap(); // did the conversion succeed?
//!
//! // success!
//! assert_eq!(dec_full, some_data);
//! ```

#![allow(clippy::inconsistent_digit_grouping)]
use crate::{
    errors::DecodingError,
    util::*,
    vecmap::VecMap,
    Float::*,
    Inum::{self, *},
    Kson::{self, *},
};
use bytes::{Buf, Bytes, IntoBuf};
use num_bigint::{BigInt, Sign::*};
use std::convert::TryInto;

pub mod ser;
pub use ser::*;
mod constants;
pub(crate) use constants::*;

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
pub fn encode(ks: &Kson, out: &mut Vec<u8>) { ks.ser(out) }

/// Read a specific number of bytes from a buffer.
///
/// # Arguments
///
/// * `data: &mut B` - A mutable reference to the buffer that will be read from.
/// * `num_bytes` - The number of bytes to read from the buffer.
fn read_bytes<B: Buf>(data: &mut B, num_bytes: usize) -> Result<Vec<u8>, DecodingError> {
    if data.remaining() >= num_bytes {
        let mut bts = vec![0; num_bytes];
        data.copy_to_slice(&mut bts);
        Ok(bts)
    } else {
        Err(DecodingError::new(&format!(
            "Requested {} bytes, but only {} bytes were left",
            num_bytes,
            data.remaining()
        )))
    }
}

#[derive(Copy, Clone, Debug)]
/// KSON tags.
enum KTag {
    KCon(u8),
    KInt(bool, bool, u8),
    KByt(bool, u8),
    KArr(bool, u8),
    KMap(bool, u8),
    KFloat(u8),
}

use KTag::*;

macro_rules! big_and_len {
    ($ctor:expr, $mask:expr, $len_fn:expr, $byte:ident) => {{
        let big = $byte & BIG_BIT == BIG_BIT;
        let len = $byte & $mask;
        Ok($ctor(big, $len_fn(len)))
    }};
    ($ctor:expr, $byte:ident) => {
        big_and_len!($ctor, MASK_LEN_BITS, |x| x, $byte)
    };
}

/// Try to read tag byte from buffer.
///
/// # Arguments
///
/// * `input: &mut Buf` - A mutable reference to the buffer to be read from.
fn read_tag(input: &mut Buf) -> Result<KTag, DecodingError> {
    if input.has_remaining() {
        let byte = input.get_u8();

        match byte & MASK_TYPE {
            TYPE_CON => Ok(KCon(byte & MASK_META)),
            TYPE_INT => {
                let big = byte & BIG_BIT == BIG_BIT;
                let pos = byte & INT_POSITIVE == INT_POSITIVE;
                let len = byte & MASK_INT_LEN_BITS;
                debug_assert!(len <= MASK_INT_LEN_BITS);
                Ok(KInt(big, pos, len + 1))
            }
            TYPE_BYT => big_and_len!(KByt, byte),
            TYPE_ARR => big_and_len!(KArr, byte),
            TYPE_MAP => big_and_len!(KMap, byte),
            TYPE_FLOAT => Ok(KFloat(byte)),
            unknown => {
                Err(DecodingError::new(&format!(
                    "Found unknown tag: {:b}",
                    unknown
                )))
            }
        }
    } else {
        Err(DecodingError::new(
            "Buffer was empty, couldn't get tag byte",
        ))
    }
}

/// Try to read [`u64`] from buffer.
fn read_u64<B: Buf>(data: &mut B, len: u8) -> Result<u64, DecodingError> {
    debug_assert!(len <= 8);
    if data.remaining() >= len as usize {
        Ok(data.get_uint_le(len as usize))
    } else {
        Err(DecodingError::new(&format!(
            "Requested 8 bytes to read `u64`, but only {} bytes were left",
            data.remaining()
        )))
    }
}

/// Try to read [`Inum`] from buffer.
fn read_int<B: Buf>(data: &mut B, big: bool, pos: bool, len: u8) -> Result<Inum, DecodingError> {
    debug_assert!(len - 1 <= MASK_INT_LEN_BITS);
    let u = read_u64(data, len).map_err(|e| {
        DecodingError::new(&format!(
            "While attempting to read an `Inum`, this error was encountered: {}",
            e.0
        ))
    })?;
    let mut i = {
        if big {
            Int(BigInt::from_bytes_le(
                Plus,
                &read_bytes(data, u as usize + BIGINT_MIN_LEN as usize)?,
            ))
        } else {
            Inum::from(u)
        }
    };
    if !pos {
        i = -i - I64(1);
    }
    Ok(i)
}

/// Try to read length from buffer.
fn read_len<B: Buf>(data: &mut B, big: bool, len: u8) -> Result<usize, DecodingError> {
    if big {
        Ok(read_u64(data, len + 1).map_err(|e| {
            DecodingError::new(&format!(
                "While attempting to read a length, this error was encountered: {}",
                e.0
            ))
        })? as usize
            + BIGCOL_MIN_LEN as usize)
    } else {
        Ok(len as usize)
    }
}

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
/// let dec = match decode(k_null) {
///     Ok(value) => value,
///     Err(_e) => panic!("Oh no. Whatever will I do?"),
/// };
///
/// // should be equal
/// assert_eq!(dec, Kson::Null);
/// ```
pub fn decode<B: Buf>(data: &mut B) -> Result<Kson, DecodingError> {
    let tag = read_tag(data)?;
    match tag {
        KCon(u) => {
            match u {
                0 => Ok(Null),
                1 => Ok(Bool(true)),
                2 => Ok(Bool(false)),
                unknown => {
                    Err(DecodingError::new(&format!(
                        "Encountered unknown constant `{:b}` while reading tag",
                        unknown
                    )))
                }
            }
        }
        KInt(big, pos, len) => read_int(data, big, pos, len).map(Kint),
        KByt(big, len) => {
            let len = read_len(data, big, len)?;
            Ok(Byt(Bytes::from(read_bytes(data, len)?)))
        }
        KArr(big, len) => {
            let len = read_len(data, big, len)?;
            let mut out = Vec::with_capacity(len);
            for _ in 0..len {
                out.push(decode(data)?)
            }
            Ok(Array(out))
        }
        KMap(big, len) => {
            let len = read_len(data, big, len)?;
            let mut out = Vec::with_capacity(len);
            for _ in 0..len {
                let key: Bytes = decode(data)?.try_into().map_err(|_| {
                    DecodingError::new("Expected bytestring, found some other [`Kson`] value")
                })?;
                let val = decode(data)?;
                out.push((key, val));
            }
            Ok(Map(VecMap::from(out)))
        }
        KFloat(b) => {
            match b {
                HALF => {
                    let f = if data.remaining() >= 2 {
                        Ok(data.get_u16_le())
                    } else {
                        Err(DecodingError::new(&format!(
                            "Requested 2 bytes to read `f16`, but only {} bytes were left",
                            data.remaining()
                        )))
                    };

                    Ok(Kfloat(Half(f?)))
                }
                SINGLE => {
                    let f = if data.remaining() >= 4 {
                        Ok(data.get_u32_le())
                    } else {
                        Err(DecodingError::new(&format!(
                            "Requested 4 bytes to read `f32`, but only {} bytes were left",
                            data.remaining()
                        )))
                    };

                    Ok(Kfloat(Single(f?)))
                }
                DOUBLE => {
                    let f = if data.remaining() >= 8 {
                        Ok(data.get_u64_le())
                    } else {
                        Err(DecodingError::new(&format!(
                            "Requested 8 bytes to read `f64`, but only {} bytes were left",
                            data.remaining()
                        )))
                    };

                    Ok(Kfloat(Double(f?)))
                }
                unknown => {
                    Err(DecodingError::new(&format!(
                        "Expected a float tag, found {:b}",
                        unknown
                    )))
                }
            }
        }
    }
}

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
pub fn encode_full(ks: &Kson) -> Vec<u8> {
    let mut out = Vec::new();
    ks.ser(&mut out);
    // encode(ks, &mut out);
    out
}

/// Decodes a bytestring into [`Kson`], returns a [`DecodingError`] if decoding fails.
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
/// let dec = decode_full(bs);
/// ```
pub fn decode_full<B: IntoBuf>(bs: B) -> Result<Kson, DecodingError> { decode(&mut bs.into_buf()) }

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::*;
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
        assert!(read_bytes(&mut Vec::new().into_buf(), 3).is_err());

        assert!(read_u64(&mut Vec::new().into_buf(), 3).is_err());

        assert!(decode(&mut vec![0b0000_0011].into_buf()).is_err());
    }
}
