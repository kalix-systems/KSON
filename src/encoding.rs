use rug::{integer::Order, Integer};
use std::{collections::BTreeMap, ops::AddAssign, vec::Vec};

use crate::{bytes::*, util::*, *};

use Atom::*;
use Container::*;
use Inum::*;
use Kson::*;
// TODO: replace len vecs w/heapless vec of size at most 8

pub const MASK_TYPE: u8 = 0b1110_0000;
pub const MASK_META: u8 = 0b0001_1111;
pub const TYPE_CON: u8 = 0b0000_0000;
pub const TYPE_INT: u8 = 0b0010_0000;
pub const TYPE_STR: u8 = 0b0100_0000;
pub const TYPE_ARR: u8 = 0b0110_0000;
pub const TYPE_MAP: u8 = 0b1000_0000;
pub const BIG_BIT: u8 = 0b0001_0000;
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
pub enum KMeta {
    KMC(u8),
    KMInt(bool, LenOrDigs, Vec<u8>),
    KMStr(LenOrDigs, Bytes),
    KMArr(LenOrDigs, Vec<Kson>),
    KMMap(LenOrDigs, BTreeMap<Bytes, Kson>),
}

use KMeta::*;

fn inum_to_meta(mut i: Inum) -> KMeta {
    let pos = i >= 0;
    if !pos {
        i *= -1;
        i += -1;
    }
    match i {
        I64(i) => {
            let digs = u64_to_digits(i as u64);
            assert!(digs.len() <= 8);
            KMInt(pos, Len(digs.len() as u8), digs)
        }
        Int(i) => {
            let digs = Integer::to_digits(&i, Order::Lsf);
            assert!(digs.len() >= 8);
            let len_digs_digs = u64_to_digits(digs.len() as u64);
            KMInt(pos, Digs(len_digs_digs), digs)
        }
    }
}

macro_rules! len_or_digs {
    ($id: ident) => {
        if $id.len() <= MASK_LEN_BITS as usize {
            Len($id.len() as u8)
        } else {
            Digs(u64_to_digits($id.len() as u64))
        }
    };
}

fn atom_to_meta(a: Atom) -> KMeta {
    match a {
        Null => KMC(0),
        Bool(t) => KMC(if t { 1 } else { 2 }),
        ANum(i) => inum_to_meta(i),
        Str(bs) => KMStr(len_or_digs!(bs), bs),
    }
}

fn container_to_meta(c: Container<Kson>) -> KMeta {
    match c {
        Array(a) => KMArr(len_or_digs!(a), a),
        Map(m) => KMMap(len_or_digs!(m), m),
    }
}

fn kson_to_meta(ks: Kson) -> KMeta {
    match ks {
        Atomic(a) => atom_to_meta(a),
        Contain(c) => container_to_meta(c),
    }
}

macro_rules! len_or_tag {
    ($tag: ident, $len_digs: ident, $id: ident, $f: expr) => {
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
    ($tag: ident, $len_digs: ident, $id: ident) => {
        len_or_tag!($tag, $len_digs, $id, |x| x)
    };
}

macro_rules! tag_and_len {
    ($type: expr, $len_or_digs: ident, $out: ident) => {
        let mut tag = $type;
        let mut len_digs;
        len_or_tag!(tag, len_digs, $len_or_digs);
        $out.push(tag);
        $out.append(&mut len_digs);
    };
}

fn encode_meta(km: KMeta, out: &mut Bytes) {
    match km {
        KMC(con) => out.push(TYPE_CON | con),
        KMInt(pos, len_or_digs, mut digs) => {
            let mut tag = TYPE_INT;
            let mut len_digs;
            len_or_tag!(tag, len_digs, len_or_digs, |x| x - 1);
            if pos {
                tag |= INT_POSITIVE;
            }
            out.push(tag);
            out.append(&mut len_digs);
            out.append(&mut digs)
        }
        KMStr(len_or_digs, mut st) => {
            tag_and_len!(TYPE_STR, len_or_digs, out);
            out.append(st.as_mut());
        }
        KMArr(len_or_digs, vs) => {
            tag_and_len!(TYPE_ARR, len_or_digs, out);
            for v in vs {
                encode(v, out);
            }
        }
        KMMap(len_or_digs, m) => {
            tag_and_len!(TYPE_MAP, len_or_digs, out);
            for (k, v) in m {
                encode(Atomic(Str(k)), out);
                encode(v, out);
            }
        }
    }
}

pub fn encode(ks: Kson, out: &mut Bytes) {
    encode_meta(kson_to_meta(ks), out)
}

fn read_byte(dat: &Bytes, ix: &mut usize) -> Option<u8> {
    if *ix >= dat.len() {
        return None;
    }
    let v = dat[*ix];
    *ix += 1;
    Some(v)
}

fn read_bytes<'a, 'b>(dat: &'a Bytes, ix: &'b mut usize, num_bytes: usize) -> Option<&'a [u8]> {
    let out = dat.get(*ix..*ix + num_bytes)?;
    *ix += num_bytes;
    Some(out)
}

#[derive(Clone, Debug)]
pub enum KTag {
    KC(u8),
    KInt(bool, bool, u8),
    KStr(bool, u8),
    KArr(bool, u8),
    KMap(bool, u8),
}

use KTag::*;

macro_rules! big_and_len {
    ($ctor: expr, $mask: expr, $len_fn: expr, $byte: ident) => {{
        let big = $byte & BIG_BIT == BIG_BIT;
        let len = $byte & $mask;
        Some($ctor(big, $len_fn(len)))
    }};
    ($ctor: expr, $byte: ident) => {
        big_and_len!($ctor, MASK_LEN_BITS, |x| x, $byte)
    };
}

pub fn read_tag(input: &Bytes, ix: &mut usize) -> Option<KTag> {
    let byte = read_byte(input, ix)?;
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
}

fn read_u64(dat: &Bytes, ix: &mut usize, len: u8) -> Option<u64> {
    assert!(len <= 8);
    let bytes = read_bytes(dat, ix, len as usize)?;
    let mask = u64::max_value() >> (64 - 8 * bytes.len());
    let p = bytes.as_ptr() as *const u64;
    Some(u64::from_le(unsafe { *p }) & mask)
}

fn read_int(dat: &Bytes, ix: &mut usize, big: bool, pos: bool, len: u8) -> Option<Inum> {
    assert!(len - 1 <= MASK_INT_LEN_BITS);
    let u = read_u64(dat, ix, len)?;
    let mut i;
    if big {
        let digs = read_bytes(dat, ix, u as usize)?;
        i = Int(Integer::from_digits(digs, Order::Lsf));
    } else {
        assert!(u < i64::max_value() as u64);
        i = I64(u as i64);
    }
    if !pos {
        i *= -1;
        i += -1;
    }
    Some(i)
}

fn read_len(dat: &Bytes, ix: &mut usize, big: bool, len: u8) -> Option<usize> {
    if big {
        Some(read_u64(dat, ix, len + 1)? as usize)
    } else {
        Some(len as usize)
    }
}

fn decode(dat: &Bytes, ix: &mut usize) -> Option<Kson> {
    let tag = read_tag(dat, ix)?;
    match tag {
        KC(u) => match u {
            0 => Some(Atomic(Null)),
            1 => Some(Atomic(Bool(true))),
            2 => Some(Atomic(Bool(false))),
            _ => None,
        },
        KInt(big, pos, len) => read_int(dat, ix, big, pos, len).map(|i| Atomic(ANum(i))),
        KStr(big, len) => {
            let len = read_len(dat, ix, big, len)?;
            let bytes = read_bytes(dat, ix, len)?.to_vec();
            Some(Atomic(Str(Bytes(bytes))))
        }
        KArr(big, len) => {
            let len = read_len(dat, ix, big, len)?;
            let mut out = Vec::with_capacity(len);
            for _ in 0..len {
                out.push(decode(dat, ix)?)
            }
            Some(Contain(Array(out)))
        }
        KMap(big, len) => {
            let len = read_len(dat, ix, big, len)?;
            let mut out = BTreeMap::new();
            for _ in 0..len {
                let key: Bytes = decode(dat, ix)?.try_into().ok()?;
                let val = decode(dat, ix)?;
                out.insert(key, val);
            }
            Some(Contain(Map(out)))
        }
    }
}

pub fn encode_full(ks: Kson) -> Bytes {
    let mut out = Bytes(vec![]);
    encode(ks, &mut out);
    out
}

pub fn decode_full(bs: &Bytes) -> Option<Kson> {
    decode(bs, &mut 0)
}
