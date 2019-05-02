use bytes::{buf::IntoBuf, Buf, Bytes};
use rug::{integer::Order, Integer};
use std::{collections::BTreeMap, ops::AddAssign, vec::Vec};

use crate::{util::*, *};

use Atom::*;
use Container::*;
use Inum::*;
use Kson::*;
// TODO: replace len vecs w/heapless vec of size at most 8

// 0xe0
pub const MASK_TYPE: u8 = 0b1110_0000;
// 0x1f
pub const MASK_META: u8 = 0b0001_1111;
// 0x00
pub const TYPE_CON: u8 = 0b0000_0000;
// 0x20
pub const TYPE_INT: u8 = 0b0010_0000;
// 0x40
pub const TYPE_STR: u8 = 0b0100_0000;
// 0x60
pub const TYPE_ARR: u8 = 0b0110_0000;
// 0x80
pub const TYPE_MAP: u8 = 0b1000_0000;
// 0x10
pub const BIG_BIT: u8 = 0b0001_0000;
// 0x0f
pub const INT_POSITIVE: u8 = 0b0000_1000;

pub const CON_NULL: u8 = 0b0000_0000;
pub const CON_TRUE: u8 = 0b0000_0001;
pub const CON_FALSE: u8 = 0b0000_0010;

pub const MASK_LEN_BITS: u8 = 0b0000_1111;
pub const MASK_INT_LEN_BITS: u8 = 0b0000_0111;

#[derive(Clone, Debug)]
pub enum LenOrDigs {
    Len(u8),
    Digs(Vec<u8>),
}

use LenOrDigs::*;

#[derive(Clone, Debug)]
/// Metadata tags for KSON.
pub enum KMeta<'a> {
    KMC(u8),
    KMInt(bool, LenOrDigs, Vec<u8>),
    KMStr(LenOrDigs, &'a Bytes),
    KMArr(LenOrDigs, &'a Vec<Kson>),
    KMMap(LenOrDigs, &'a VecMap<Bytes, Kson>),
}

use KMeta::*;

fn inum_to_meta<'a, 'b>(i: &'a Inum) -> KMeta<'b> {
    let pos = *i >= 0;
    match i {
        I64(i) => {
            let j = if pos { *i } else { -*i - 1 };
            let digs = u64_to_digits(j as u64);
            assert!(digs.len() <= 8);
            KMInt(pos, Len(digs.len() as u8), digs)
        }
        Int(i) => {
            if pos {
                let digs = Integer::to_digits(i, Order::Lsf);
                assert!(digs.len() >= 8);
                let len_digs_digs = u64_to_digits(digs.len() as u64);
                KMInt(pos, Digs(len_digs_digs), digs)
            } else {
                let digs = Integer::to_digits(&(i.clone() + 1), Order::Lsf);
                assert!(digs.len() >= 8);
                let len_digs_digs = u64_to_digits(digs.len() as u64);
                KMInt(pos, Digs(len_digs_digs), digs)
            }
        }
    }
}

macro_rules! len_or_digs {
    ($id:ident) => {
        if $id.len() <= MASK_LEN_BITS as usize {
            Len($id.len() as u8)
        } else {
            Digs(u64_to_digits($id.len() as u64))
        }
    };
}

fn atom_to_meta(a: &Atom) -> KMeta {
    match a {
        Null => KMC(0),
        Bool(t) => KMC(if *t { 1 } else { 2 }),
        ANum(i) => inum_to_meta(i),
        Str(bs) => KMStr(len_or_digs!(bs), bs),
    }
}

fn container_to_meta(c: &Container<Kson>) -> KMeta {
    match c {
        Array(a) => KMArr(len_or_digs!(a), a),
        Map(m) => KMMap(len_or_digs!(m), m),
    }
}

fn kson_to_meta(ks: &Kson) -> KMeta {
    match ks {
        Atomic(a) => atom_to_meta(a),
        Contain(c) => container_to_meta(c),
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
                let len_len = l_d.len() as u8;
                $tag |= BIG_BIT;
                $tag |= len_len - 1;
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
        KMC(con) => out.push(TYPE_CON | con),
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
        KMStr(len_or_digs, st) => {
            tag_and_len!(TYPE_STR, len_or_digs, out);
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
                encode(&Atomic(Str(k.clone())), out);
                encode(v, out);
            }
        }
    }
}

pub fn encode(ks: &Kson, out: &mut Vec<u8>) { encode_meta(kson_to_meta(ks), out) }

fn read_byte(dat: &Bytes, ix: &mut usize) -> Option<u8> {
    if *ix >= dat.len() {
        return None;
    }
    let v = dat[*ix];
    *ix += 1;
    Some(v)
}

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
    KC(u8),
    KInt(bool, bool, u8),
    KStr(bool, u8),
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
            TYPE_CON => Some(KC(byte & MASK_META)),
            TYPE_INT => {
                let big = byte & BIG_BIT == BIG_BIT;
                let pos = byte & INT_POSITIVE == INT_POSITIVE;
                let len = byte & MASK_INT_LEN_BITS;
                Some(KInt(big, pos, len + 1))
            }
            TYPE_STR => big_and_len!(KStr, byte),
            TYPE_ARR => big_and_len!(KArr, byte),
            TYPE_MAP => big_and_len!(KMap, byte),
            _ => None,
        }
    } else {
        None
    }
}

fn read_u64<B: Buf>(dat: &mut B, len: u8) -> Option<u64> {
    assert!(len <= 8);
    if dat.remaining() >= len as usize {
        Some(dat.get_uint_le(len as usize))
    } else {
        None
    }
}

fn read_int<B: Buf>(dat: &mut B, big: bool, pos: bool, len: u8) -> Option<Inum> {
    assert!(len - 1 <= MASK_INT_LEN_BITS);
    let u = read_u64(dat, len)?;
    let mut i = {
        if big {
            Int(Integer::from_digits(
                &read_bytes(dat, u as usize)?,
                Order::Lsf,
            ))
        } else {
            assert!(u < i64::max_value() as u64);
            I64(u as i64)
        }
    };
    if !pos {
        i *= -1;
        i += -1;
    }
    Some(i)
}

fn read_len<B: Buf>(dat: &mut B, big: bool, len: u8) -> Option<usize> {
    if big {
        Some(read_u64(dat, len + 1)? as usize)
    } else {
        Some(len as usize)
    }
}

pub fn decode<B: Buf>(dat: &mut B) -> Option<Kson> {
    let tag = read_tag(dat)?;
    match tag {
        KC(u) => {
            match u {
                0 => Some(Atomic(Null)),
                1 => Some(Atomic(Bool(true))),
                2 => Some(Atomic(Bool(false))),
                _ => None,
            }
        }
        KInt(big, pos, len) => read_int(dat, big, pos, len).map(|i| Atomic(ANum(i))),
        KStr(big, len) => {
            let len = read_len(dat, big, len)?;
            Some(Atomic(Str(Bytes::from(read_bytes(dat, len)?))))
        }
        KArr(big, len) => {
            let len = read_len(dat, big, len)?;
            let mut out = Vec::with_capacity(len);
            for _ in 0..len {
                out.push(decode(dat)?)
            }
            Some(Contain(Array(out)))
        }
        KMap(big, len) => {
            let len = read_len(dat, big, len)?;
            let mut out = Vec::with_capacity(len);
            for _ in 0..len {
                let key: Bytes = decode(dat)?.try_into().ok()?;
                let val = decode(dat)?;
                out.push((key, val));
            }
            Some(Contain(Map(VecMap::from(out))))
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
