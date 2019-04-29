#[macro_use]
extern crate criterion;

extern crate common_utils;
extern crate kson;

use criterion::black_box;
use criterion::Criterion;
use kson::bytes::Bytes;

use kson::encoding::{decode_full, encode_full};
use kson::*;

const N_BIG_ARR: usize = 100;
const N_CHARS: usize = 100_000;

fn big_str() -> Bytes {
    Bytes([0; N_CHARS].to_vec())
}

fn big_arr() -> Kson {
    let v: Vec<Kson> = (0..N_BIG_ARR).map(|_| Kson::from(big_str())).collect();
    Kson::from(v)
}

fn bench_enc(c: &mut Criterion) {
    let big_arr = big_arr();
    c.bench_function(
        &format!(
            "Encoding a Kson array of {} {}-character strings",
            N_BIG_ARR, N_CHARS
        ),
        move |b| b.iter(|| encode_full(black_box(big_arr.clone()))),
    );
}

fn bench_dec(c: &mut Criterion) {
    let big_arr = big_arr();
    let enc = encode_full(big_arr);
    c.bench_function(
        &format!(
            "Decoding a Kson array of {} {}-character strings",
            N_BIG_ARR, N_CHARS
        ),
        move |b| b.iter(|| decode_full(black_box(&enc.clone()))),
    );
}

criterion_group!(benches, bench_enc, bench_dec);
criterion_main!(benches);
