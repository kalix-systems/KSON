use super::*;
use half::f16;
use num_bigint::{BigInt, Sign};
// use std::io::Error;

pub trait Serializer {
    type Out;
    fn put_byte(&mut self, u: u8);
    fn put_slice(&mut self, slice: &[u8]);
    fn finalize(self) -> Self::Out;
}

pub trait SerializerExt: Serializer {
    fn put_i8(&mut self, i: i8) { self.put_i16(i as i16) }
    fn put_i16(&mut self, i: i16) { self.put_i32(i as i32) }
    fn put_i32(&mut self, i: i32) { self.put_i64(i as i64) }
    fn put_i64(&mut self, i: i64) { self.put_bigint(&BigInt::from(i)) }
    fn put_bigint(&mut self, i: &BigInt);

    fn put_bytes(&mut self, b: &Bytes);

    fn put_f16(&mut self, f: f16);
    fn put_f32(&mut self, f: f32);
    fn put_f64(&mut self, f: f64);

    fn put_bool(&mut self, b: bool);
    fn put_null(&mut self);

    fn put_arr<S: Ser>(&mut self, v: &Vec<S>);
    fn put_map<S: Ser>(&mut self, m: &VecMap<Bytes, S>);
}

#[inline]
fn compute_int_tag(big: bool, pos: bool, len: u8) -> u8 {
    TYPE_INT | ((big as u8) << 4) | ((pos as u8) << 3) | (len - 1)
}

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

impl Serializer for Vec<u8> {
    type Out = Vec<u8>;

    fn put_byte(&mut self, u: u8) { self.push(u) }

    fn put_slice(&mut self, slice: &[u8]) { self.extend_from_slice(slice) }

    fn finalize(self) -> Vec<u8> { self }
}

macro_rules! len_or_digs {
    ($id:ident) => {
        if $id.len() <= MASK_LEN_BITS as usize {
            Len($id.len() as u8)
        } else {
            Digs(u64_to_digits($id.len() as u64 - BIGCOL_MIN_LEN))
        }
    };
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
        $out.put_slice(&[tag]);
        $out.put_slice(&len_digs);
    };
}

impl<S: Serializer> SerializerExt for S {
    fn put_i64(&mut self, mut i: i64) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let digs = u64_to_digits(i as u64);
        debug_assert!(digs.len() <= 8);

        self.put_byte(compute_int_tag(false, pos, digs.len() as u8));
        self.put_slice(&digs);
    }

    fn put_i32(&mut self, mut i: i32) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let digs = u32_to_digits(i as u32);
        debug_assert!(digs.len() <= 4);

        self.put_byte(compute_int_tag(false, pos, digs.len() as u8));
        self.put_slice(&digs);
    }

    fn put_i16(&mut self, mut i: i16) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let digs = u16_to_digits(i as u16);
        debug_assert!(digs.len() <= 2);

        self.put_byte(compute_int_tag(false, pos, digs.len() as u8));
        self.put_slice(&digs);
    }

    fn put_i8(&mut self, mut i: i8) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let mut tag = TYPE_INT;
        tag |= (pos as u8) << 3;

        self.put_byte(tag);
        self.put_byte(i as u8);
    }

    fn put_bigint(&mut self, i: &BigInt) {
        let (sign, mut digs) = i.to_bytes_le();
        let pos = sign != Sign::Minus;
        debug_assert!(digs.len() >= 8);
        if !pos {
            decr_digs(&mut digs)
        };
        if digs.len() == 8 {
            push_digs(pos, &digs, self);
        } else {
            let len = digs.len() - BIGINT_MIN_LEN as usize;
            if len <= u16::max_value() as usize {
                let len_digs = u16_to_digits(len as u16);
                let tag = compute_int_tag(true, pos, len_digs.len() as u8);
                self.put_byte(tag);
                self.put_slice(&len_digs);
                self.put_slice(&digs);
            } else {
                u64_digs(pos, len as u64, digs, self)
            }
        }
    }

    fn put_f16(&mut self, f: f16) {
        self.put_byte(HALF);
        self.put_slice(&u16::to_le_bytes(f.to_bits()));
    }

    fn put_f32(&mut self, f: f32) {
        self.put_byte(SINGLE);
        self.put_slice(&u32::to_le_bytes(f.to_bits()));
    }

    fn put_f64(&mut self, f: f64) {
        self.put_byte(DOUBLE);
        self.put_slice(&u64::to_le_bytes(f.to_bits()));
    }

    fn put_bytes(&mut self, b: &Bytes) {
        let len_or_digs = len_or_digs!(b);
        tag_and_len!(TYPE_BYT, len_or_digs, self);
        self.put_slice(b);
    }

    fn put_bool(&mut self, b: bool) {
        if b {
            self.put_byte(CON_TRUE)
        } else {
            self.put_byte(CON_FALSE)
        }
    }

    fn put_null(&mut self) { self.put_byte(CON_NULL) }

    fn put_arr<T: Ser>(&mut self, v: &Vec<T>) {
        let len_or_digs = len_or_digs!(v);
        tag_and_len!(TYPE_ARR, len_or_digs, self);
        for t in v {
            t.ser(self);
        }
    }

    fn put_map<T: Ser>(&mut self, m: &VecMap<Bytes, T>) {
        let len_or_digs = len_or_digs!(m);
        tag_and_len!(TYPE_MAP, len_or_digs, self);
        for (k, v) in m.iter() {
            self.put_bytes(k);
            v.ser(self);
        }
    }
}

#[cold]
#[inline]
fn decr_digs(digs: &mut Vec<u8>) {
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
}

#[cold]
#[inline]
fn push_digs<S: Serializer>(pos: bool, digs: &[u8], out: &mut S) {
    out.put_byte(compute_int_tag(false, pos, digs.len() as u8));
    out.put_slice(digs);
}

#[cold]
#[inline]
fn u64_digs<S: Serializer>(pos: bool, u: u64, digs: Vec<u8>, out: &mut S) {
    let len_digs = u64_to_digits(u);
    out.put_byte(compute_int_tag(true, pos, len_digs.len() as u8));
    out.put_slice(&len_digs);
    out.put_slice(&digs);
}

pub trait Ser {
    fn ser<S: Serializer>(&self, s: &mut S);
}

impl Ser for Kson {
    fn ser<S: Serializer>(&self, s: &mut S) {
        match self {
            Null => s.put_null(),
            Bool(b) => s.put_bool(*b),
            Kint(Int(i)) => s.put_bigint(i),
            Kint(I64(i)) => s.put_i64(*i),
            Kfloat(Half(n)) => s.put_f16(f16::from_bits(*n)),
            Kfloat(Single(n)) => s.put_f32(f32::from_bits(*n)),
            Kfloat(Double(n)) => s.put_f64(f64::from_bits(*n)),
            Byt(bs) => s.put_bytes(bs),
            Array(a) => s.put_arr(a),
            Map(m) => s.put_map(m),
        }
    }
}
