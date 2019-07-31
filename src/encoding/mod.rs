//! # KSON binary encoder and decoder
//!
//! Encode and decode functions for KSON.

#![allow(clippy::inconsistent_digit_grouping)]
use crate::{
    inum::Inum::{self, *},
    util::*,
};
use bytes::{Buf, Bytes, IntoBuf};
use failure::Error;

pub mod ser;
pub use ser::*;
pub mod de;
pub use de::*;
mod constants;
use constants::*;

#[derive(PartialEq, Copy, Clone, Debug)]
#[repr(u8)]
pub enum Size {
    Big = BIG_BIT,
    Small = 0,
}

#[derive(PartialEq, Copy, Clone, Debug)]
#[repr(u8)]
pub enum KSign {
    Pos = INT_POSITIVE,
    Neg = 0,
}

// TODO: replace len vecs w/ heapless vec of size at most 8
pub fn encode<T: Ser>(t: T, out: &mut Vec<u8>) { t.ser(out) }

pub fn decode<D: Deserializer, T: De>(data: &mut D) -> Result<T, Error> { T::de(data) }

pub fn encode_full<T: Ser>(t: T) -> Vec<u8> {
    let mut v = Vec::new();
    t.ser(&mut v);
    v
}

pub fn decode_full<B: IntoBuf, T: De>(bs: B) -> Result<T, Error> { decode(&mut bs.into_buf()) }

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use std::ops::Neg;

    #[test]
    fn inum_meta_no_sign() {
        let n = 0i32;
        let out = encode_full(n);

        // tag
        assert_eq!(out[0], TYPE_INT | INT_POSITIVE);
        // digit, should be 0
        assert_eq!(out[1], 0);
    }

    #[test]
    fn inum_meta_small_pos_one_byte() {
        let small_pos = 1;
        let out = encode_full(small_pos);

        // tag
        assert_eq!(out[0], TYPE_INT | INT_POSITIVE);
        // digit, should be 1
        assert_eq!(out[1], 1);
    }

    #[test]
    fn inum_meta_small_pos_two_bytes() {
        let small_pos = 257;
        let out = encode_full(small_pos);

        // tag
        assert_eq!(out[0], TYPE_INT | INT_POSITIVE | (2 - 1));
        // LSD, should be 1
        assert_eq!(out[1], 1);
        // MSD, should be 1
        assert_eq!(out[2], 1);
    }

    #[test]
    fn inum_meta_small_pos_eight_bytes() {
        let small_pos = i64::max_value();
        let out = encode_full(small_pos);

        assert_eq!(out[0], TYPE_INT | INT_POSITIVE | (8 - 1));
        assert_eq!(out[1..], [255, 255, 255, 255, 255, 255, 255, 127]);
    }

    #[test]
    fn inum_meta_small_neg_one_byte() {
        let small_neg = -2;
        let out = encode_full(small_neg);

        // tag
        assert_eq!(out[0], TYPE_INT);
        // should be 0
        assert_eq!(out[1], 1);
    }

    #[test]
    fn inum_meta_small_neg_two_byte() {
        let small_neg = -257;
        let out = encode_full(small_neg);

        // tag
        assert_eq!(out[0], TYPE_INT | (2 - 1));
        // LSD, should be 0
        assert_eq!(out[1], 0);
        // MSD, should be 1
        assert_eq!(out[2], 1);
    }

    #[test]
    fn inum_meta_small_neg_eight_bytes() {
        let small_neg = i64::min_value();
        let out = encode_full(small_neg);

        // tag
        assert_eq!(out[0], TYPE_INT | (8 - 1));
        assert_eq!(out[1..], [255, 255, 255, 255, 255, 255, 255, 127]);
    }

    #[test]
    fn inum_meta_big_pos() {
        let big_pos = BigInt::from(u64::max_value()) + 1;
        let out = encode_full(big_pos);

        // tag
        assert_eq!(out[0], TYPE_INT | BIG_BIT | INT_POSITIVE);
        // length in bytes
        assert_eq!(out[1], 0);
        // digits
        assert_eq!(out[2..], [0, 0, 0, 0, 0, 0, 0, 0, 1]);
    }

    #[test]
    fn inum_meta_big_neg() {
        let big_neg = BigInt::from(u64::max_value()).neg() - 2;
        let out = encode_full(big_neg);

        // tag
        assert_eq!(out[0], TYPE_INT | BIG_BIT);
        // length in bytes
        assert_eq!(out[1], 0);
        // digits
        assert_eq!(out[2..], [0, 0, 0, 0, 0, 0, 0, 0, 1]);
    }
    #[test]
    fn constants() {
        let out = encode_full(());

        assert_eq!(out[0], CON_NULL);
        assert_eq!(out.len(), 1);

        let out = encode_full(true);

        assert_eq!(out[0], CON_TRUE);
        assert_eq!(out.len(), 1);

        let out = encode_full(false);

        assert_eq!(out[0], CON_FALSE);
        assert_eq!(out.len(), 1);
    }

    #[test]
    fn small_string() {
        let small = "w";

        let out = encode_full(small);

        // tag
        assert_eq!(out[0], TYPE_BYT | 1);
        // characters
        assert_eq!(out[1], 119);
    }
    #[test]
    fn large_string() -> Result<(), Error> {
        let large = String::from_utf8(vec![b'w'; 140])?;

        let out = encode_full(large);

        // tag
        assert_eq!(out[0], TYPE_BYT | BIG_BIT);
        // length
        assert_eq!(out[1], 140 - BIG_BIT);
        // bytes
        assert_eq!(out[2..].to_vec(), vec![b'w'; 140]);

        Ok(())
    }

    #[test]
    fn small_vec() {
        let small_vec = vec![0];

        let out = encode_full(small_vec);

        // tag
        assert_eq!(out[0], TYPE_ARR | 1);
        // element tag
        assert_eq!(out[1], TYPE_INT | INT_POSITIVE);
        // check that the value is right
        assert_eq!(out[2], 0);
    }

    #[test]
    fn large_vec() {
        let large_vec = vec![0; 140];

        let out = encode_full(large_vec);

        // tag
        assert_eq!(out[0], TYPE_ARR | BIG_BIT);
        // length
        assert_eq!(out[1], 140 - BIG_BIT);

        // element tags
        let out_tags: Vec<&u8> = out[2..].iter().step_by(2).collect();
        assert_eq!(out_tags, vec![&(TYPE_INT | INT_POSITIVE); 140]);

        let out_vals: Vec<&u8> = out[3..].iter().step_by(2).collect();
        assert_eq!(out_vals, vec![&0; 140]);
    }

    #[test]
    fn small_map() {
        use std::collections::HashMap;
        let mut small_map: HashMap<String, u8> = HashMap::new();
        small_map.insert("a".into(), 10);

        let out = encode_full(small_map);

        // tag
        assert_eq!(out[0], TYPE_MAP | 1);
        // element tags
        assert_eq!(
            vec![out[1], out[3]],
            vec![TYPE_BYT | 1, TYPE_INT | INT_POSITIVE]
        );
        // check that the values are right
        assert_eq!((out[2], out[4]), (b'a', 10));
    }

    #[test]
    fn large_map() {
        use std::collections::HashMap;

        let large_map: HashMap<Bytes, Bytes> = (0..140)
            .map(|x| (Bytes::from(vec![x as u8]), Bytes::from(vec![x as u8])))
            .collect();

        let out = encode_full(&large_map);

        // tag
        assert_eq!(out[0], TYPE_MAP | BIG_BIT);
        // length
        assert_eq!(out[1], 140 - BIG_BIT);

        // key tags
        out[2..]
            .iter()
            .step_by(4)
            .for_each(|x| assert_eq!(*x, TYPE_BYT | 1));

        // val tags
        out[4..]
            .iter()
            .step_by(4)
            .for_each(|x| assert_eq!(*x, TYPE_BYT | 1));

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

        let out = encode_full(f);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b00_1111_00]);

        let f = half::f16::from_f32(-1.0);

        let out = encode_full(f);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b10_1111_00]);

        let f = half::f16::from_f32(-0.0);

        let out = encode_full(f);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0, 0b1_000_0000]);

        let f = half::f16::from_f32(65504.0);

        let out = encode_full(f);

        // tag
        assert_eq!(out[0], HALF);

        // bytes
        assert_eq!(out[1..3], [0b1111_1111, 0b0111_1011]);
    }

    #[test]
    fn single_floats() {
        let f = 1f32;

        let out = encode_full(f);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0b1000_0000, 0b0011_1111]);

        let f = -1f32;

        let out = encode_full(f);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0b1000_0000, 0b1011_1111]);

        let f = -0f32;

        let out = encode_full(f);

        // tag
        assert_eq!(out[0], SINGLE);

        // bytes
        assert_eq!(out[1..5], [0, 0, 0, 0b1_000_0000]);
    }

    #[test]
    fn double_floats() {
        let f = 1f64;

        let out = encode_full(f);

        // tag
        assert_eq!(out[0], DOUBLE);

        // bytes
        assert_eq!(out[1..9], [0, 0, 0, 0, 0, 0, 0b1111_0000, 0b0011_1111]);
    }

    #[test]
    // for completeness
    fn trivial() {
        assert!((&mut Vec::new().into_buf()).read_many(3).is_err());

        assert!((&mut Vec::new().into_buf()).read_uint(3).is_err());

        // assert!(decode(&mut vec![0b0000_0011].into_buf()).is_err());
    }
}
