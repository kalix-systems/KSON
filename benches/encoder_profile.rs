extern crate criterion;
extern crate kalix;

use byte_string::ByteString;
use criterion::black_box;
use rug::Integer;
use std::collections::BTreeMap;
use std::sync::Arc;

use kalix::kson::encoding::{decode_full, encode_full};
use kalix::kson::*;
use kalix::util::*;

const N_ARR: usize = 100;
const N_MAP: usize = 100;

fn big_k() -> Kson {
    let v0: Vec<Kson> = (0..N_ARR).map(|i| Kson::from(i as i64)).collect();
    let m: BTreeMap<ByteString, Kson> = (0..N_MAP)
        .map(|i| {
            (
                u64_to_bytes_le(i as u64),
                Kson::KSArray(Arc::new(v0.clone())),
            )
        })
        .collect();
    let v: Vec<Kson> = std::iter::repeat(m)
        .map(|m| Kson::KSMap(Arc::new(m)))
        .take(N_ARR)
        .collect();
    Kson::KSArray(Arc::new(v))
}

const N_REPS: u8 = 100;

fn main() {
    let big_k = black_box(big_k());
    // let size = black_box(&big_k).size();
    let enc_outer = encode_full(black_box(big_k.clone()));
    for _ in 0..N_REPS {
        let enc = encode_full(black_box(big_k.clone()));
        if enc != enc_outer {
            panic!("this hsouldn't happen!");
        }
    }
}
