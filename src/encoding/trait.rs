use super::*;
use crate::util::*;
use half::f16;
use num_bigint::{BigInt, Sign};

pub trait Serializer {
    type Out;

    fn put_byte(&mut self, u: u8);
    fn put_u64(&mut self, u: u64);
    fn put_slice(&mut self, slice: &[u8]);
    fn finalize(self) -> Self::Out;
}

pub trait SerializerExt {
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

    fn put_array<D: Serialize>(&mut self, ve
}

pub trait Serialize {
    fn ser<S: Serializer>(self, s: S) -> S::Out;
}

fn compute_int_tag(big: bool, pos: bool, len: u8) -> u8 {
    TYPE_INT | ((big as u8) << 4) | ((pos as u8) << 3) | (len - 1)
}

impl Serializer for Vec<u8> {
    type Out = Vec<u8>;

    fn put_u8(&mut self, u: u8) { self.push(u) }

    fn put_u64(&mut self, u: u64) { self.extend_from_slice(u64_to_digits(u)) }

    fn put_slice(&mut self, slice: &[u8]) { self.extend_from_slice(slice) }

    fn finalize(self) -> Vec<u8> { self }
}

impl SerializerExt for Vec<u8> {
    fn put_i64(&mut self, mut i: i64) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let digs = u64_to_digits(i as u64);
        debug_assert!(digs.len() <= 8);

        self.push(compute_int_tag(false, pos, digs.len() as u8));
        self.extend_from_slice(&digs);
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

        self.push(compute_int_tag(false, pos, digs.len() as u8));
        self.extend_from_slice(&digs);
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

        self.push(compute_int_tag(false, pos, digs.len() as u8));
        self.extend_from_slice(&digs);
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

        self.push(tag);
        self.push(i as u8);
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
                self.push(TYPE_INT | BIG_BIT | ((pos as u8) << 3) | (len_digs.len() as u8 - 1));
                self.extend_from_slice(&len_digs);
                self.extend_from_slice(&digs);
            } else {
                u64_digs(pos, len as u64, digs, self)
            }
        }
    }

    fn put_f16(&mut self, f: f16) {
        self.push(HALF);
        self.put_slice(&u16::to_bytes_le(f as u16))
    }

    fn put_f32(&mut self, f: f32) {
        self.push(SINGLE);
        self.put_slice(&u32::to_bytes_le(f as u32))
    }

    fn put_f64(&mut self, f: f64) {
        self.push(DOUBLE);
        self.put_slice(&u64::to_bytes_le(f as u64))
    }

    fn put_bool(&mut self, b: bool) {
        if b {
            self.push(CON_TRUE)
        } else {
            self.push(CON_FALSE)
        }
    }

    fn put_null(&mut self) { self.push(CON_NULL) }
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
fn push_digs(pos: bool, digs: &[u8], out: &mut Vec<u8>) {
    out.push(compute_int_tag(false, pos, digs.len() as u8));
    out.extend_from_slice(digs);
}

#[cold]
fn u64_digs(pos: bool, u: u64, digs: Vec<u8>, out: &mut Vec<u8>) {
    let len_digs = u64_to_digits(u);
    out.push(compute_int_tag(true, pos, len_digs.len() as u8));
    out.extend_from_slice(&len_digs);
    out.extend_from_slice(&digs);
}
