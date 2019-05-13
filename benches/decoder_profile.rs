extern crate criterion;
extern crate kson;

use bytes::Bytes;
use criterion::black_box;
use kson::prelude::*;

const N_ARR: usize = 10;
const N_MAP: usize = 100;

fn big_k() -> Kson {
    let v0: Vec<Kson> = (0..N_ARR).map(|i| Kson::from(i as u64)).collect();
    let m: VecMap<Bytes, Kson> = (0..N_MAP)
        .map(|i| {
            (
                Bytes::from(u64::to_le_bytes(i as u64).to_vec()),
                Kson::from(v0.clone()),
            )
        })
        .collect();
    let v: Vec<Kson> = std::iter::repeat(m).map(Kson::from).take(N_ARR).collect();
    Kson::from(v)
}

const N_REPS: u8 = 100;

fn main() {
    let big_k = big_k();
    let enc = Bytes::from(encode_full(&big_k));
    for _ in 0..N_REPS {
        let dec = black_box(decode_full(black_box(&enc))).unwrap();
        if dec != big_k {
            panic!("this shouldn't happen!")
        }
    }
}
