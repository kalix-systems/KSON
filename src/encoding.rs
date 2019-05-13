#![allow(clippy::inconsistent_digit_grouping)]
use crate::{
    errors::DecodingError,
    util::*,
    vecmap::VecMap,
    Float::{self, *},
    Inum::{self, *},
    Kson::{self, *},
};
use bytes::{Buf, Bytes, IntoBuf};
use num_bigint::{BigInt, Sign::*};
use num_traits::*;
use std::convert::TryInto;

// TODO: replace len vecs w/heapless vec of size at most 8

/// 0xe0
const MASK_TYPE: u8 = 0b1110_0000;
/// 0x1f
const MASK_META: u8 = 0b0001_1111;
/// 0x00
const TYPE_CON: u8 = 0b0000_0000;
/// Integer type bits, 0x20
const TYPE_INT: u8 = 0b0010_0000;
/// String type bits, 0x40
const TYPE_BYT: u8 = 0b0100_0000;
/// Array type bits, 0x60
const TYPE_ARR: u8 = 0b0110_0000;
/// Map type bits, 0x80
const TYPE_MAP: u8 = 0b1000_0000;
/// Large integer indicator bit, 0x10
const BIG_BIT: u8 = 0b0001_0000;
/// Integer sign bit, 0x0f
const INT_POSITIVE: u8 = 0b0000_1000;

/// Float type bits
const TYPE_FLOAT: u8 = 0b101_00_000;
/// Half-precision tag
const HALF: u8 = TYPE_FLOAT;
/// Single-precision tag
const SINGLE: u8 = TYPE_FLOAT | 0b000_01_000;
/// Double-precision tag
const DOUBLE: u8 = TYPE_FLOAT | 0b000_10_000;

/// `Null` constant.
const CON_NULL: u8 = 0b0000_0000;
/// `True` constant.
const CON_TRUE: u8 = 0b0000_0001;
/// `False` constant.
const CON_FALSE: u8 = 0b0000_0010;

const MASK_LEN_BITS: u8 = 0b0000_1111;
const MASK_INT_LEN_BITS: u8 = 0b0000_0111;

const BIGINT_MIN_LEN: u64 = MASK_INT_LEN_BITS as u64 + 2;
const BIGCON_MIN_LEN: u64 = MASK_LEN_BITS as u64 + 1;

#[derive(Clone, Debug)]
/// The second element in a tagged KSON integer, bytestring, array, or map.
/// It is either a length (in the case of large versions)
/// or digits (in the case of small versions).
enum LenOrDigs {
    /// Length variant
    Len(u8),
    /// Digits variant
    Digs(Vec<u8>),
}

use LenOrDigs::*;

#[derive(Clone, Debug)]
/// `Kson` with encoding metadata.
enum KMeta<'a> {
    /// Constants
    KMCon(u8),
    /// Tagged integer
    KMInt(bool, LenOrDigs, Vec<u8>),
    /// Tagged bytestring
    KMByt(LenOrDigs, &'a Bytes),
    /// Tagged array
    KMArr(LenOrDigs, &'a Vec<Kson>),
    /// Tagged map
    KMMap(LenOrDigs, &'a VecMap<Bytes, Kson>),
    /// Tagged float
    KMFloat(&'a Float),
}

use KMeta::*;

/// Converts `Inum` to tagged `Kson`.
///
/// # Arguments
///
/// * `i` - An `Inum` that holds the integer.
fn inum_to_meta<'a, 'b>(i: &'a Inum) -> KMeta<'b> {
    match i {
        I64(i) => {
            let pos = !i.is_negative();
            let j = if pos { *i } else { -(*i + 1) };
            let digs = u64_to_digits(j as u64);
            debug_assert!(digs.len() <= 8);
            KMInt(pos, Len(digs.len() as u8), digs)
        }
        Int(i) => {
            // TODO: do the arithmetic on bytes directly so we don't have to allocate a new bigint
            let (sign, mut digs) = i.to_bytes_le();
            debug_assert!(digs.len() >= 8);
            if sign == Minus {
                // subtract 1 directly on the digits
                for dig in digs.iter_mut() {
                    *dig = dig.wrapping_sub(1);
                    if *dig != 255 {
                        break;
                    }
                }
                let last = digs.pop().unwrap();
                if last != 0 {
                    digs.push(last)
                }
            };
            if digs.len() <= 8 {
                KMInt(sign != Minus, Len(digs.len() as u8), digs)
            } else {
                match sign {
                    Plus => {
                        KMInt(
                            true,
                            Digs(u64_to_digits(digs.len() as u64 - BIGINT_MIN_LEN)),
                            digs,
                        )
                    }
                    Minus => {
                        KMInt(
                            false,
                            Digs(u64_to_digits(digs.len() as u64 - BIGINT_MIN_LEN)),
                            digs,
                        )
                    }
                    NoSign => unreachable!("0 should not be encoded as BigInt"),
                }
            }
        }
    }
}

macro_rules! len_or_digs {
    ($id:ident) => {
        if $id.len() <= MASK_LEN_BITS as usize {
            Len($id.len() as u8)
        } else {
            Digs(u64_to_digits($id.len() as u64 - BIGCON_MIN_LEN))
        }
    };
}

/// Converts `Kson` to tagged `Kson`.
///
/// # Arguments
///
/// * `ks: &Kson` - A reference to the value to be converted.
fn kson_to_meta(ks: &Kson) -> KMeta {
    match ks {
        Null => KMCon(CON_NULL),
        Bool(t) => KMCon(if *t { CON_TRUE } else { CON_FALSE }),
        Kint(i) => inum_to_meta(i),
        Byt(bs) => KMByt(len_or_digs!(bs), bs),
        Array(a) => KMArr(len_or_digs!(a), a),
        Map(m) => KMMap(len_or_digs!(m), m),
        Kfloat(f) => KMFloat(f),
    }
}

macro_rules! len_or_tag {
    ($tag:ident, $len_digs:ident, $id:ident, $f:expr) => {
        match $id {
            Len(l) => {
                $tag |= $f(l);
                $len_digs = vec![];
            }
            Digs(l_d) => {
                let len_len = l_d.len() as u8 - 1;
                $tag |= BIG_BIT;
                $tag |= len_len;
                $len_digs = l_d;
            }
        }
    };
    ($tag:ident, $len_digs:ident, $id:ident) => {
        len_or_tag!($tag, $len_digs, $id, |x| x)
    };
}

macro_rules! tag_and_len {
    ($type:expr, $len_or_digs:ident, $out:ident) => {
        let mut tag = $type;
        let len_digs;
        len_or_tag!(tag, len_digs, $len_or_digs);
        $out.extend_from_slice(&[tag]);
        $out.extend_from_slice(&len_digs);
    };
}

/// Encode tagged `Kson`.
fn encode_meta<'a>(km: KMeta<'a>, out: &mut Vec<u8>) {
    match km {
        KMCon(con) => out.extend_from_slice(&[TYPE_CON | con]),
        KMInt(pos, len_or_digs, digs) => {
            let mut tag = TYPE_INT;
            let len_digs;
            len_or_tag!(tag, len_digs, len_or_digs, |x| x - 1);
            if pos {
                tag |= INT_POSITIVE;
            }
            out.extend_from_slice(&[tag]);
            out.extend_from_slice(&len_digs);
            out.extend_from_slice(&digs);
        }
        KMByt(len_or_digs, st) => {
            tag_and_len!(TYPE_BYT, len_or_digs, out);
            out.extend_from_slice(st);
        }
        KMArr(len_or_digs, vs) => {
            tag_and_len!(TYPE_ARR, len_or_digs, out);
            for v in vs {
                encode(v, out);
            }
        }
        KMMap(len_or_digs, m) => {
            tag_and_len!(TYPE_MAP, len_or_digs, out);
            for (k, v) in m.iter() {
                encode(&Byt(k.clone()), out);
                encode(v, out);
            }
        }
        KMFloat(f) => {
            match f {
                Half(n) => {
                    out.extend_from_slice(&[HALF]);
                    out.extend_from_slice(&u16::to_le_bytes(*n));
                }
                Single(n) => {
                    out.extend_from_slice(&[SINGLE]);
                    out.extend_from_slice(&u32::to_le_bytes(*n));
                }
                Double(n) => {
                    out.extend_from_slice(&[DOUBLE]);
                    out.extend_from_slice(&u64::to_le_bytes(*n));
                }
            }
        }
    }
}

/// Encode `Kson` into its binary representation, storing output in `out`.
///
/// # Arguments
///
/// * `ks` - A reference to the `Kson` value to be encoded.
/// * `out` - A mutable reference to `Bytes` where the encoder output will be stored.
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
pub fn encode(ks: &Kson, out: &mut Vec<u8>) { encode_meta(kson_to_meta(ks), out) }

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

/// Try to read `u64` from buffer.
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

/// Try to read `Inum` from buffer.
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

/// Try to read length from from buffer.
fn read_len<B: Buf>(data: &mut B, big: bool, len: u8) -> Result<usize, DecodingError> {
    if big {
        Ok(read_u64(data, len + 1).map_err(|e| {
            DecodingError::new(&format!(
                "While attempting to read a length, this error was encountered: {}",
                e.0
            ))
        })? as usize
            + BIGCON_MIN_LEN as usize)
    } else {
        Ok(len as usize)
    }
}

/// Tries to decode a buffer into `Kson`.
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
/// // should be equal
/// assert_eq!(decode(k_null).unwrap(), Kson::Null);
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
                    DecodingError::new(&format!(
                        "Expected bytestring, found some other `Kson` value",
                    ))
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
                        "Expected a floating-point tag, found {:b}",
                        unknown
                    )))
                }
            }
        }
    }
}

/// Encodes a `Kson` object into a vector of bytes.
///
/// # Arguments
///
/// * `ks` - A reference to the `Kson` value to be encoded.
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
    encode(ks, &mut out);
    out
}

/// Decodes a bytestring into `Kson`, returns `None` if decoding fails.
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
    use std::ops::Neg;

    #[test]
    fn inum_meta_no_sign() {
        let n = Inum::from(0);
        let meta = inum_to_meta(&n);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], 0b001_0_1_000);
        // digit, should be 0
        assert_eq!(out[1], 0);

        let n = Inum::from(-0);
        let meta = inum_to_meta(&n);

        let out = &mut Vec::new();
        encode_meta(meta, out);
    }

    #[test]
    fn inum_meta_small_pos_one_byte() {
        let small_pos = I64(1);
        let meta = inum_to_meta(&small_pos);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], 0b001_0_1_000);
        // digit, should be 1
        assert_eq!(out[1], 1);
    }

    #[test]
    fn inum_meta_small_pos_two_bytes() {
        let small_pos = I64(257);
        let meta = inum_to_meta(&small_pos);
        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], 0b001_0_1_001);
        // LSD, should be 1
        assert_eq!(out[1], 1);
        // MSD, should be 1
        assert_eq!(out[2], 1);
    }

    #[test]
    fn inum_meta_small_pos_eight_bytes() {
        let small_pos = I64(i64::max_value());
        let meta = inum_to_meta(&small_pos);
        let out = &mut Vec::new();
        encode_meta(meta, out);

        assert_eq!(out[0], 0b001_0_1_111);
        assert_eq!(out[1..], [255, 255, 255, 255, 255, 255, 255, 127]);
    }

    #[test]
    fn inum_meta_small_neg_one_byte() {
        let small_neg = I64(-2);
        let meta = inum_to_meta(&small_neg);
        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], 0b0010_0_000);
        // should be 0
        assert_eq!(out[1], 1);
    }

    #[test]
    fn inum_meta_small_neg_two_byte() {
        let small_neg = I64(-257);
        let meta = inum_to_meta(&small_neg);
        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], 0b001_0_0_001);
        // LSD, should be 0
        assert_eq!(out[1], 0);
        // MSD, should be 1
        assert_eq!(out[2], 1);
    }

    #[test]
    fn inum_meta_small_neg_eight_bytes() {
        let small_neg = I64(i64::min_value());
        let meta = inum_to_meta(&small_neg);
        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], 0b001_0_0_111);
        assert_eq!(out[1..], [255, 255, 255, 255, 255, 255, 255, 127]);
    }

    #[test]
    fn inum_meta_big_pos() {
        let big_pos = Inum::from(BigInt::from(u64::max_value()) + 1);
        let meta = inum_to_meta(&big_pos);
        let out = &mut Vec::new();

        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], 0b001_1_1_000);
        // length in bytes
        assert_eq!(out[1], 0);
        // digits
        assert_eq!(out[2..], [0, 0, 0, 0, 0, 0, 0, 0, 1]);
    }

    #[test]
    fn inum_meta_big_neg() {
        let big_neg = Inum::from(BigInt::from(u64::max_value()) + 2).neg();
        let meta = inum_to_meta(&big_neg);
        let out = &mut Vec::new();

        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], 0b0011_0000);
        // length in bytes
        assert_eq!(out[1], 0);
        // digits
        assert_eq!(out[2..], [0, 0, 0, 0, 0, 0, 0, 0, 1]);
    }
    #[test]
    fn constants() {
        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&Null), out);

        assert_eq!(out[0], CON_NULL);

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&Bool(true)), out);

        assert_eq!(out[0], CON_TRUE);

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&Bool(false)), out);

        assert_eq!(out[0], CON_FALSE);
    }

    #[test]
    fn small_string() {
        let small_bs = Kson::from_static(b"w");

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&small_bs), out);

        // tag
        assert_eq!(out[0], 0b010_0_0001);
        // characters
        assert_eq!(out[1], 119);
    }

    #[test]
    fn large_string() {
        let large_bs = Kson::from_static(&[b'w'; 140]);

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&large_bs), out);

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

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&small_array), out);

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

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&large_array), out);

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

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&small_map), out);

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

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&large_map), out);

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
        let kf = Kfloat(Float::from(f));
        let meta = kson_to_meta(&kf);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b00_1111_00]);

        let f = half::f16::from_f32(-1.0);
        let kf = Kfloat(Float::from(f));
        let meta = kson_to_meta(&kf);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b10_1111_00]);

        let f = half::f16::from_f32(-0.0);
        let kf = Kfloat(Float::from(f));
        let meta = kson_to_meta(&kf);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b1_000_0000]);

        let f = half::f16::from_f32(65504.0);
        let kf = Kfloat(Float::from(f));
        let meta = kson_to_meta(&kf);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0b1111_1111, 0b0111_1011]);
    }

    #[test]
    fn single_floats() {
        let f = 1f32;
        let kf = Kfloat(Float::from(f));
        let meta = kson_to_meta(&kf);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0b1000_0000, 0b0011_1111]);

        let f = -1f32;
        let kf = Kfloat(Float::from(f));
        let meta = kson_to_meta(&kf);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0b1000_0000, 0b1011_1111]);

        let f = -0f32;
        let kf = Kfloat(Float::from(f));
        let meta = kson_to_meta(&kf);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0, 0b1_000_0000]);
    }

    #[test]
    fn double_floats() {
        let f = 1f64;
        let kf = Kfloat(Float::from(f));
        let meta = kson_to_meta(&kf);

        let out = &mut Vec::new();
        encode_meta(meta, out);

        // tag
        assert_eq!(out[0], DOUBLE);

        // bytes
        assert_eq!(out[1..9], [0, 0, 0, 0, 0, 0, 0b1111_0000, 0b00111111]);
    }

    #[test]
    // for completeness
    fn trivial() {
        assert!(read_bytes(&mut Vec::new().into_buf(), 3).is_err());

        assert!(read_u64(&mut Vec::new().into_buf(), 3).is_err());

        assert!(decode(&mut vec![0b0000_0011].into_buf()).is_err());
    }
}
