extern crate criterion;
extern crate kson;

use criterion::black_box;
use kson::bytes::Bytes;
use rug::Integer;
use std::collections::BTreeMap;

use kson::encoding::{decode_full, encode_full};
use kson::vecmap::*;
use kson::*;
use util::*;

const N_ARR: usize = 100;
const N_MAP: usize = 100;

fn big_k() -> Kson {
    let v0: Vec<Kson> = (0..N_ARR).map(|i| Kson::from(i as u64)).collect();
    let m: VecMap<Bytes, Kson> = (0..N_MAP)
        .map(|i| (u64_to_bytes_le(i as u64), Kson::from(v0.clone())))
        .collect();
    let v: Vec<Kson> = std::iter::repeat(m)
        .map(|m| Kson::from(m))
        .take(N_ARR)
        .collect();
    Kson::from(v)
}

const N_REPS: u8 = 100;

fn main() {
    let big_k = big_k();
    let enc = encode_full(big_k.clone());
    for _ in 0..N_REPS {
        let dec = black_box(decode_full(black_box(&enc))).unwrap();
        if &dec != &big_k {
            panic!("this shouldn't happen!")
        }
    }
}
