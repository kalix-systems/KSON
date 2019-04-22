use byte_string::*;
use rug::integer::Order;
use rug::Integer;
use std::collections::BTreeMap;
use std::ops::AddAssign;
use std::sync::Arc;
use std::vec::Vec;

use crate::util::*;
use crate::*;

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
    KMStr(LenOrDigs, ByteString),
    KMArr(LenOrDigs, Vec<Kson>),
    KMMap(LenOrDigs, BTreeMap<ByteString, Kson>),
}

use KMeta::*;

fn inum_to_meta(i: Inum) -> KMeta {
    match i {
        I64(mut i) => {
            let pos = i >= 0;
            if !pos {
                i *= -1;
                i -= 1;
            }
            let digs = u64_to_digits(i as u64);
            assert!(digs.len() <= 8);
            KMInt(i >= 0, Len(digs.len() as u8), digs)
        }
        Int(mut i) => {
            let pos = i >= 0;
            if !pos {
                i *= -1;
                i -= 1;
            }
            let digs = Integer::to_digits(&i, Order::Lsf);
            assert!(digs.len() > 8);
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

fn encode_meta(km: KMeta, out: &mut ByteString) {
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

fn encode(ks: Kson, out: &mut ByteString) {
    encode_meta(kson_to_meta(ks), out)
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

#[derive(Clone, Debug)]
pub enum KTag {
    KC(u8),
    KInt(bool, bool, u8),
    KStr(bool, u8),
    KArr(bool, u8),
    KMap(bool, u8),
}

use KTag::*;

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

// fn read_u64(dat: &ByteString, ix: &mut usize, len: u8) -> Option<u64> {
//     assert!(len <= 8);
//     let bytes = read_bytes(dat, ix, len as usize)?;
//     let mask = u64::max_value() >> (64 - 8 * bytes.len());
//     let p = bytes.as_ptr() as *const u64;
//     Some(u64::from_le(unsafe { *p }) & mask)
// }

// fn read_bigint(dat: &ByteString, ix: &mut usize, positive: bool, len: usize) -> Option<Integer> {
//     let digs = read_bytes(dat, ix, len)?;
//     let mut i = Integer::from_digits(digs, Order::Lsf);
//     if !positive {
//         i *= -1;
//         i -= 1;
//     }
//     Some(i)
// }

// pub fn read_int(
//     dat: &ByteString,
//     ix: &mut usize,
//     big: bool,
//     positive: bool,
//     len: u8,
// ) -> Option<Inum> {
//     assert!(0 < len && len <= 8);
//     if big {
//         let newlen = 1 + read_u64(dat, ix, len)? as usize;
//         assert!(8 <= newlen);
//         let mag = read_bigint(dat, ix, positive, newlen)?;
//         Some(Inum::from(mag))
//     } else {
//         let mag = read_u64(dat, ix, len)?;
//         let i = mag as i64;
//         if positive {
//             if i >= 0 {
//                 Some(Inum::I64(i))
//             } else {
//                 Some(Inum::Int(Arc::new(Integer::from(mag))))
//             }
//         } else {
//             if i >= 0 {
//                 Some(Inum::I64(-1 * i - 1))
//             } else {
//                 Some(Inum::Int(Arc::new(-1 * Integer::from(mag) - 1)))
//             }
//         }
//     }
// }

// fn read_array(dat: &ByteString, ix: &mut usize, len: usize) -> Option<Vec<Kson>> {
//     let mut out = Vec::with_capacity(len);
//     for _ in 0..len {
//         out.push(decode(dat, ix)?);
//     }
//     Some(out)
// }

// fn read_map(dat: &ByteString, ix: &mut usize, len: usize) -> Option<BTreeMap<ByteString, Kson>> {
//     let mut out = BTreeMap::new();
//     for _ in 0..len {
//         if let Some(KSString(bs)) = decode(dat, ix) {
//             out.insert(unwrap_or_clone(bs), decode(dat, ix)?);
//         } else {
//             return None;
//         }
//     }
//     Some(out)
// }

// pub fn decode(dat: &ByteString, ix: &mut usize) -> Option<Kson> {
//     let tag = read_tag(dat, ix)?;
//     match tag {
//         KC(con) => match con {
//             0 => Some(KSNull),
//             1 => Some(KSBool(true)),
//             2 => Some(KSBool(false)),
//             _ => None,
//         },
//         KInt(big, pos, len) => read_int(dat, ix, big, pos, len).map(KSInt),
//         KStr(big, len) => {
//             let bytes;
//             if big {
//                 let longlen = read_u64(dat, ix, len)?;
//                 bytes = read_bytes(dat, ix, longlen as usize)?;
//             } else {
//                 bytes = read_bytes(dat, ix, len as usize)?;
//             }
//             Some(KSString(Arc::new(ByteString(bytes.to_vec()))))
//         }
//         KArr(big, len) => {
//             let elems;
//             if big {
//                 let longlen = read_u64(dat, ix, len)?;
//                 elems = read_array(dat, ix, longlen as usize)?;
//             } else {
//                 elems = read_array(dat, ix, len as usize)?;
//             }
//             Some(KSArray(Arc::new(elems)))
//         }
//         KMap(big, len) => {
//             let map;
//             if big {
//                 let longlen = read_u64(dat, ix, len)?;
//                 map = read_map(dat, ix, longlen as usize)?;
//             } else {
//                 map = read_map(dat, ix, len as usize)?;
//             }
//             Some(KSMap(Arc::new(map)))
//         }
//     }
// }

// pub fn encode_full(ks: Kson) -> ByteString {
//     let mut bs = ByteString(vec![]);
//     encode(ks, &mut bs);
//     bs
// }

// pub fn decode_full(bs: &ByteString) -> Option<Kson> {
//     decode(bs, &mut 0)
// }
