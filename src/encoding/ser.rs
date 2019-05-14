use super::*;
use crate::util::*;
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

    fn put_f16(&mut self, f: f16);
    fn put_f32(&mut self, f: f32);
    fn put_f64(&mut self, f: f64);

    fn put_bool(&mut self, b: bool);
    fn put_null(&mut self);
}

pub trait Serialize {
    fn ser<S: Serializer>(self, s: S) -> S::Out;
}

fn compute_int_tag(big: bool, pos: bool, len: u8) -> u8 {
    TYPE_INT | ((big as u8) << 4) | ((pos as u8) << 3) | (len - 1)
}

impl Serializer for Vec<u8> {
    type Out = Vec<u8>;

    fn put_byte(&mut self, u: u8) { self.push(u) }

    fn put_slice(&mut self, slice: &[u8]) { self.extend_from_slice(slice) }

    fn finalize(self) -> Vec<u8> { self }
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
        if digs.len() <= 8 {
            push_digs(pos, &digs, self)
        } else {
            let len = digs.len() - BIGCON_MIN_LEN as usize;
            if len <= u16::max_value() as usize {
                let len_digs = u16_to_digits(len as u16);
                self.put_byte(TYPE_INT | BIG_BIT | ((pos as u8) << 3) | (len_digs.len() as u8 - 1));
                self.put_slice(&len_digs);
                self.put_slice(&digs);
            } else {
                u64_digs(pos, len as u64, digs, self)
            }
        }
    }

    fn put_f16(&mut self, f: f16) { unimplemented!() }

    fn put_f32(&mut self, f: f32) { unimplemented!() }

    fn put_f64(&mut self, f: f64) { unimplemented!() }

    fn put_bool(&mut self, b: bool) {
        if b {
            self.put_byte(CON_TRUE)
        } else {
            self.put_byte(CON_FALSE)
        }
    }

    fn put_null(&mut self) { self.put_byte(CON_NULL) }
}

#[cold]
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
fn push_digs<S: Serializer>(pos: bool, digs: &[u8], out: &mut S) {
    out.put_byte(compute_int_tag(false, pos, digs.len() as u8));
    out.put_slice(digs);
}

#[cold]
fn u64_digs<S: Serializer>(pos: bool, u: u64, digs: Vec<u8>, out: &mut S) {
    let len_digs = u64_to_digits(u);
    out.put_byte(compute_int_tag(true, pos, len_digs.len() as u8));
    out.put_slice(&len_digs);
    out.put_slice(&digs);
}
