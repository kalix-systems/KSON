use byte_string::*;
use rug::integer::Order;
use rug::Integer;
use std::collections::BTreeMap;
use std::ops::AddAssign;
use std::sync::Arc;
use std::vec::Vec;

use crate::util::*;
use crate::*;

use Kson::*;
// TODO: replace len vecs w/heapless vec of size at most 8

#[derive(Clone, Debug)]
pub enum KTag {
    KC(u8),
    KInt(bool, bool, u8),
    KStr(bool, u8),
    KArr(bool, u8),
    KMap(bool, u8),
}

use KTag::*;

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

pub fn encode_i64(mut val: i64, out: &mut ByteString) {
    let (mag, sign);
    if val >= 0 {
        mag = val as u64;
        sign = INT_POSITIVE;
    } else {
        val *= -1;
        val -= 1;
        mag = val as u64;
        sign = 0;
    }
    let mut digs = u64_to_digits(mag);
    assert!(0 < digs.len() && digs.len() <= 8);
    let len = (digs.len() - 1) as u8;
    let tag = TYPE_INT | sign | len;
    out.push(tag);
    out.append(&mut digs);
}

pub fn encode_int(mut val: Integer, out: &mut ByteString) {
    let sign;
    if val >= 0 {
        sign = INT_POSITIVE;
    } else {
        val *= -1;
        val -= 1;
        sign = 0;
    }
    let mut digs: Vec<u8> = val.to_digits(Order::Lsf);
    let mut len_digs = u64_to_digits((digs.len() - 1) as u64);
    let len_len = len_digs.len() as u8;
    assert!(0 < len_len && len_len <= 8);
    let mut tag = TYPE_INT;
    tag |= BIG_BIT;
    tag |= sign;
    tag |= len_len - 1;
    out.push(tag);
    out.append(&mut len_digs);
    out.append(&mut digs);
}

fn encode_inum(val: Inum, out: &mut ByteString) {
    match val {
        Inum::I64(i) => encode_i64(i, out),
        Inum::Int(i) => encode_int(unwrap_or_clone(i), out),
    }
}

fn encode_str(bs: ByteString, out: &mut ByteString) {
    let tag;
    let mut len;
    if bs.len() <= MASK_LEN_BITS as usize {
        // small case
        let len_small = bs.len() as u8;
        len = vec![];
        tag = TYPE_STR | len_small;
    } else {
        // big case
        len = u64_to_digits(bs.len() as u64);
        assert!(len.len() <= 8);
        let len_len = len.len() as u8;
        tag = TYPE_STR | BIG_BIT | len_len;
    }
    out.push(tag);
    out.append(&mut len);
    out.append(&mut bs.to_vec());
}

fn encode_array(v: Vec<Kson>, out: &mut ByteString) {
    let tag;
    let mut len;
    if v.len() <= MASK_LEN_BITS as usize {
        // small case
        let len_small = v.len() as u8;
        len = vec![];
        tag = TYPE_ARR | len_small;
    } else {
        // big case
        len = u64_to_digits(v.len() as u64);
        assert!(len.len() <= 8);
        let len_len = len.len() as u8;
        tag = TYPE_ARR | BIG_BIT | len_len;
    }
    out.push(tag);
    out.append(&mut len);
    for k in v {
        encode(k, out);
    }
}

fn encode_map(m: BTreeMap<ByteString, Kson>, out: &mut ByteString) {
    let tag;
    let mut len;
    if m.len() <= MASK_LEN_BITS as usize {
        // small case
        let len_small = m.len() as u8;
        len = vec![];
        tag = TYPE_MAP | len_small;
    } else {
        // big case
        len = u64_to_digits(m.len() as u64);
        assert!(len.len() <= 8);
        let len_len = len.len() as u8;
        tag = TYPE_MAP | BIG_BIT | len_len;
    }
    out.push(tag);
    out.append(&mut len);
    for (k, v) in m {
        encode_str(k, out);
        encode(v, out);
    }
}

pub fn encode(obj: Kson, out: &mut ByteString) {
    match obj {
        Kson::KSNull => out.push(CON_NULL),
        Kson::KSBool(b) => out.push(if b { CON_TRUE } else { CON_FALSE }),
        Kson::KSInt(i) => encode_inum(i, out),
        Kson::KSString(s) => encode_str(unwrap_or_clone(s), out),
        Kson::KSArray(v) => encode_array(unwrap_or_clone(v), out),
        Kson::KSMap(m) => encode_map(unwrap_or_clone(m), out),
    }
}

fn read_byte(dat: &ByteString, ix: &mut usize) -> Option<u8> {
    if *ix >= dat.len() {
        return None;
    }
    let v = dat[*ix];
    *ix += 1;
    Some(v)
}

fn read_bytes<'a, 'b>(
    dat: &'a ByteString,
    ix: &'b mut usize,
    num_bytes: usize,
) -> Option<&'a [u8]> {
    let out = dat.get(*ix..*ix + num_bytes)?;
    *ix += num_bytes;
    Some(out)
}

fn read_u64(dat: &ByteString, ix: &mut usize, len: u8) -> Option<u64> {
    assert!(len <= 8);
    let bytes = read_bytes(dat, ix, len as usize)?;
    let mask = u64::max_value() >> (64 - 8 * bytes.len());
    let p = bytes.as_ptr() as *const u64;
    Some(u64::from_le(unsafe { *p }) & mask)
}

fn read_bigint(dat: &ByteString, ix: &mut usize, positive: bool, len: usize) -> Option<Integer> {
    let digs = read_bytes(dat, ix, len)?;
    let mut i = Integer::from_digits(digs, Order::Lsf);
    if !positive {
        i *= -1;
        i -= 1;
    }
    Some(i)
}

pub fn read_int(
    dat: &ByteString,
    ix: &mut usize,
    big: bool,
    positive: bool,
    len: u8,
) -> Option<Inum> {
    assert!(0 < len && len <= 8);
    if big {
        let newlen = 1 + read_u64(dat, ix, len)? as usize;
        assert!(8 <= newlen);
        let mag = read_bigint(dat, ix, positive, newlen)?;
        Some(Inum::from(mag))
    } else {
        let mag = read_u64(dat, ix, len)?;
        let i = mag as i64;
        if positive {
            if i >= 0 {
                Some(Inum::I64(i))
            } else {
                Some(Inum::Int(Arc::new(Integer::from(mag))))
            }
        } else {
            if i >= 0 {
                Some(Inum::I64(-1 * i - 1))
            } else {
                Some(Inum::Int(Arc::new(-1 * Integer::from(mag) - 1)))
            }
        }
    }
}

pub fn read_tag(input: &ByteString, ix: &mut usize) -> Option<KTag> {
    let byte = read_byte(input, ix)?;
    match byte & MASK_TYPE {
        TYPE_CON => Some(KC(byte & MASK_META)),
        TYPE_INT => {
            let big = byte & BIG_BIT == BIG_BIT;
            let pos = byte & INT_POSITIVE == INT_POSITIVE;
            let len = byte & MASK_INT_LEN_BITS;
            Some(KInt(big, pos, len + 1))
        }
        TYPE_STR => {
            let big = byte & BIG_BIT == BIG_BIT;
            Some(KStr(big, byte & MASK_LEN_BITS))
        }
        TYPE_ARR => {
            let big = byte & BIG_BIT == BIG_BIT;
            Some(KArr(big, byte & MASK_LEN_BITS))
        }
        TYPE_MAP => {
            let big = byte & BIG_BIT == BIG_BIT;
            Some(KMap(big, byte & MASK_LEN_BITS))
        }
        _ => None,
    }
}

fn read_array(dat: &ByteString, ix: &mut usize, len: usize) -> Option<Vec<Kson>> {
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        out.push(decode(dat, ix)?);
    }
    Some(out)
}

fn read_map(dat: &ByteString, ix: &mut usize, len: usize) -> Option<BTreeMap<ByteString, Kson>> {
    let mut out = BTreeMap::new();
    for _ in 0..len {
        if let Some(KSString(bs)) = decode(dat, ix) {
            out.insert(unwrap_or_clone(bs), decode(dat, ix)?);
        } else {
            return None;
        }
    }
    Some(out)
}

pub fn decode(dat: &ByteString, ix: &mut usize) -> Option<Kson> {
    let tag = read_tag(dat, ix)?;
    match tag {
        KC(con) => match con {
            0 => Some(KSNull),
            1 => Some(KSBool(true)),
            2 => Some(KSBool(false)),
            _ => None,
        },
        KInt(big, pos, len) => read_int(dat, ix, big, pos, len).map(KSInt),
        KStr(big, len) => {
            let bytes;
            if big {
                let longlen = read_u64(dat, ix, len)?;
                bytes = read_bytes(dat, ix, longlen as usize)?;
            } else {
                bytes = read_bytes(dat, ix, len as usize)?;
            }
            Some(KSString(Arc::new(ByteString(bytes.to_vec()))))
        }
        KArr(big, len) => {
            let elems;
            if big {
                let longlen = read_u64(dat, ix, len)?;
                elems = read_array(dat, ix, longlen as usize)?;
            } else {
                elems = read_array(dat, ix, len as usize)?;
            }
            Some(KSArray(Arc::new(elems)))
        }
        KMap(big, len) => {
            let map;
            if big {
                let longlen = read_u64(dat, ix, len)?;
                map = read_map(dat, ix, longlen as usize)?;
            } else {
                map = read_map(dat, ix, len as usize)?;
            }
            Some(KSMap(Arc::new(map)))
        }
    }
}

pub fn encode_full(ks: Kson) -> ByteString {
    let mut bs = ByteString(vec![]);
    encode(ks, &mut bs);
    bs
}

pub fn decode_full(bs: &ByteString) -> Option<Kson> {
    decode(bs, &mut 0)
}
