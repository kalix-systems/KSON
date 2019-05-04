use bytes::{buf::IntoBuf, Buf, Bytes};
use num_bigint::{BigInt, Sign::*};
use num_traits::*;
use std::convert::TryInto;

use crate::{
    util::*,
    vecmap::VecMap,
    Inum::{self, *},
    Kson::{self, *},
};
// TODO: replace len vecs w/heapless vec of size at most 8

/// 0xe0
pub const MASK_TYPE: u8 = 0b1110_0000;
/// 0x1f
pub const MASK_META: u8 = 0b0001_1111;
/// 0x00
pub const TYPE_CON: u8 = 0b0000_0000;
/// Integer type bits, 0x20
pub const TYPE_INT: u8 = 0b0010_0000;
/// String type bits, 0x40
pub const TYPE_BYT: u8 = 0b0100_0000;
/// Array type bits, 0x60
pub const TYPE_ARR: u8 = 0b0110_0000;
/// Map type bits, 0x80
pub const TYPE_MAP: u8 = 0b1000_0000;
/// Large integer indicator bit, 0x10
pub const BIG_BIT: u8 = 0b0001_0000;
/// Integer sign bit, 0x0f
pub const INT_POSITIVE: u8 = 0b0000_1000;

/// `Null` constant.
pub const CON_NULL: u8 = 0b0000_0000;
/// `True` constant.
pub const CON_TRUE: u8 = 0b0000_0001;
/// `False` constant.
pub const CON_FALSE: u8 = 0b0000_0010;

pub const MASK_LEN_BITS: u8 = 0b0000_1111;
pub const MASK_INT_LEN_BITS: u8 = 0b0000_0111;

pub const BIGINT_MIN_LEN: u64 = MASK_INT_LEN_BITS as u64 + 2;
pub const BIGCON_MIN_LEN: u64 = MASK_LEN_BITS as u64 + 1;

#[derive(Clone, Debug)]
pub enum LenOrDigs {
    Len(u8),
    Digs(Vec<u8>),
}

use LenOrDigs::*;

#[derive(Clone, Debug)]
/// Tagged KSON.
pub enum KMeta<'a> {
    KMCon(u8),
    KMInt(bool, LenOrDigs, Vec<u8>),
    KMByt(LenOrDigs, &'a Bytes),
    KMArr(LenOrDigs, &'a Vec<Kson>),
    KMMap(LenOrDigs, &'a VecMap<Bytes, Kson>),
}

use KMeta::*;

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
                    NoSign => unreachable!("0 had long digits"),
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

fn kson_to_meta(ks: &Kson) -> KMeta {
    match ks {
        Null => KMCon(0),
        Bool(t) => KMCon(if *t { 1 } else { 2 }),
        Kint(i) => inum_to_meta(i),
        Byt(bs) => KMByt(len_or_digs!(bs), bs),
        Array(a) => KMArr(len_or_digs!(a), a),
        Map(m) => KMMap(len_or_digs!(m), m),
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
        $out.push(tag);
        $out.extend_from_slice(&len_digs);
    };
}

fn encode_meta<'a>(km: KMeta<'a>, out: &mut Vec<u8>) {
    match km {
        KMCon(con) => out.push(TYPE_CON | con),
        KMInt(pos, len_or_digs, digs) => {
            let mut tag = TYPE_INT;
            let len_digs;
            len_or_tag!(tag, len_digs, len_or_digs, |x| x - 1);
            if pos {
                tag |= INT_POSITIVE;
            }
            out.push(tag);
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
    }
}

pub fn encode(ks: &Kson, out: &mut Vec<u8>) { encode_meta(kson_to_meta(ks), out) }

fn read_bytes<B: Buf>(dat: &mut B, num_bytes: usize) -> Option<Vec<u8>> {
    if dat.remaining() >= num_bytes {
        let mut bts = vec![0; num_bytes];
        dat.copy_to_slice(&mut bts);
        Some(bts)
    } else {
        None
    }
}

#[derive(Clone, Debug)]
/// KSON tags.
pub enum KTag {
    KCon(u8),
    KInt(bool, bool, u8),
    KByt(bool, u8),
    KArr(bool, u8),
    KMap(bool, u8),
}

use KTag::*;

macro_rules! big_and_len {
    ($ctor:expr, $mask:expr, $len_fn:expr, $byte:ident) => {{
        let big = $byte & BIG_BIT == BIG_BIT;
        let len = $byte & $mask;
        Some($ctor(big, $len_fn(len)))
    }};
    ($ctor:expr, $byte:ident) => {
        big_and_len!($ctor, MASK_LEN_BITS, |x| x, $byte)
    };
}

pub fn read_tag(input: &mut Buf) -> Option<KTag> {
    if input.has_remaining() {
        let byte = input.get_u8();
        match byte & MASK_TYPE {
            TYPE_CON => Some(KCon(byte & MASK_META)),
            TYPE_INT => {
                let big = byte & BIG_BIT == BIG_BIT;
                let pos = byte & INT_POSITIVE == INT_POSITIVE;
                let len = byte & MASK_INT_LEN_BITS;
                debug_assert!(len <= MASK_INT_LEN_BITS);
                Some(KInt(big, pos, len + 1))
            }
            TYPE_BYT => big_and_len!(KByt, byte),
            TYPE_ARR => big_and_len!(KArr, byte),
            TYPE_MAP => big_and_len!(KMap, byte),
            _ => None,
        }
    } else {
        None
    }
}

fn read_u64<B: Buf>(dat: &mut B, len: u8) -> Option<u64> {
    debug_assert!(len <= 8);
    if dat.remaining() >= len as usize {
        Some(dat.get_uint_le(len as usize))
    } else {
        None
    }
}

fn read_int<B: Buf>(dat: &mut B, big: bool, pos: bool, len: u8) -> Option<Inum> {
    debug_assert!(len - 1 <= MASK_INT_LEN_BITS);
    let u = read_u64(dat, len)?;
    let mut i = {
        if big {
            Int(BigInt::from_bytes_le(
                Plus,
                &read_bytes(dat, u as usize + BIGINT_MIN_LEN as usize)?,
            ))
        } else {
            Inum::from(u)
        }
    };
    if !pos {
        i = -i - I64(1);
    }
    Some(i)
}

fn read_len<B: Buf>(dat: &mut B, big: bool, len: u8) -> Option<usize> {
    if big {
        Some(read_u64(dat, len + 1)? as usize + BIGCON_MIN_LEN as usize)
    } else {
        Some(len as usize)
    }
}

pub fn decode<B: Buf>(dat: &mut B) -> Option<Kson> {
    let tag = read_tag(dat)?;
    match tag {
        KCon(u) => {
            match u {
                0 => Some(Null),
                1 => Some(Bool(true)),
                2 => Some(Bool(false)),
                _ => None,
            }
        }
        KInt(big, pos, len) => read_int(dat, big, pos, len).map(Kint),
        KByt(big, len) => {
            let len = read_len(dat, big, len)?;
            Some(Byt(Bytes::from(read_bytes(dat, len)?)))
        }
        KArr(big, len) => {
            let len = read_len(dat, big, len)?;
            let mut out = Vec::with_capacity(len);
            for _ in 0..len {
                out.push(decode(dat)?)
            }
            Some(Array(out))
        }
        KMap(big, len) => {
            let len = read_len(dat, big, len)?;
            let mut out = Vec::with_capacity(len);
            for _ in 0..len {
                let key: Bytes = decode(dat)?.try_into().ok()?;
                let val = decode(dat)?;
                out.push((key, val));
            }
            Some(Map(VecMap::from(out)))
        }
    }
}

/// Encodes a `Kson` object into a `Vec<u8>`
pub fn encode_full(ks: &Kson) -> Vec<u8> {
    let mut out = vec![];
    encode(ks, &mut out);
    out
}

/// Decodes an `IntoBuf` into `Kson`, returns `None` if decoding fails.
pub fn decode_full<B: IntoBuf>(bs: B) -> Option<Kson> { decode(&mut bs.into_buf()) }

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
        let small_bs = Byt(Bytes::from("w"));

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&small_bs), out);

        // tag
        assert_eq!(out[0], 0b010_0_0001);
        // characters
        assert_eq!(out[1], 119);
    }

    #[test]
    fn large_string() {
        let large_bs = Byt(Bytes::from_static(&[b'w'; 140]));

        let out = &mut Vec::new();
        encode_meta(kson_to_meta(&large_bs), out);

        // tag
        assert_eq!(out[0], 0b010_1_0000);
        // length
        assert_eq!(out[1], 140 - BIG_BIT);
        // bytes
        assert_eq!(out[2..].to_vec(), vec![b'w' as u8; 140]);
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
        assert_eq!(vec![out[2], out[4]], vec![b'a' as u8, b'b' as u8]);
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
    fn trivial() {
        assert!(read_bytes(&mut Vec::new().into_buf(), 3).is_none());

        assert!(read_u64(&mut Vec::new().into_buf(), 3).is_none());

        assert!(decode(&mut vec![0b0000_0011].into_buf()).is_none());
    }
}
