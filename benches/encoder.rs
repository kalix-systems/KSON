#[macro_use]
extern crate criterion;

extern crate common_utils;
extern crate kson;

use bytes::Bytes;
use criterion::{black_box, Criterion};

use kson::prelude::*;

pub fn u64_to_bytes_le(x: u64) -> Bytes { Bytes::from(u64::to_le_bytes(x).to_vec()) }

const N_BIG_ARR: usize = 2000;

fn big_arr() -> Kson {
    let v: Vec<Kson> = (0..N_BIG_ARR).map(|i| Kson::from(i as i64)).collect();
    Kson::from(v)
}

const N_ARR: usize = 10;
const N_MAP: usize = 10;

fn big_k() -> Kson {
    let v0: Vec<Kson> = (0..N_ARR).map(|i| Kson::from(i as i64)).collect();
    let m: VecMap<Bytes, Kson> = (0..N_MAP)
        .map(|i| (u64_to_bytes_le(i as u64), Kson::from(v0.clone())))
        .collect();
    let v: Vec<Kson> = std::iter::repeat(m).map(Kson::from).take(N_ARR).collect();
    Kson::from(v)
}

fn bench_construction(c: &mut Criterion) {
    c.bench_function(
        &format!(
            "Creating a Kson object of size {}",
            encode_full(&big_k()).len()
        ),
        |b| b.iter(|| black_box(big_k())),
    );
}

// fn bench_size(c: &mut Criterion) {
//     let big_k = big_k();
//     c.bench_function(
//         &format!(
//             "Calculating size for a Kson object of size {}",
//             big_k.size()
//         ),
//         move |b| b.iter(|| black_box(big_k.clone()).size()),
//     );
// }

fn bench_enc(c: &mut Criterion) {
    let big_k = big_k();
    let enc_len = encode_full(&big_k).len();
    c.bench_function(
        &format!("Encoding a Kson object, output size of {} bytes", enc_len),
        move |b| b.iter(|| encode_full(black_box(&big_k))),
    );
}

fn bench_enc_single_alloc(c: &mut Criterion) {
    let big_k = big_k();
    let enc_len = encode_full(&big_k).len();
    c.bench_function(
        &format!(
            "Encoding a Kson object, output size of {} bytes, buffer preallocated",
            enc_len
        ),
        move |b| {
            b.iter(|| {
                let out = Vec::with_capacity(enc_len * 2);
                encode(black_box(&big_k), out)
            })
        },
    );
}

fn bench_dec(c: &mut Criterion) {
    let big_k = big_k();
    let enc = encode_full(&big_k);
    c.bench_function(
        &format!("Decoding a Kson object, input size of {} bytes", enc.len()),
        move |b| b.iter(|| decode_full(black_box(&enc)).map(|x: Kson| x).unwrap()),
    );
}

fn bench_enc_flat(c: &mut Criterion) {
    let big_arr = big_arr();
    let enc_len = encode_full(&big_arr).len();
    c.bench_function(
        &format!("Encoding a Kson vector, output size of {} bytes", enc_len),
        move |b| b.iter(|| encode_full(black_box(&big_arr))),
    );
}

fn bench_dec_flat(c: &mut Criterion) {
    let big_arr = big_arr();
    let enc = encode_full(&big_arr);
    c.bench_function(
        &format!("Decoding a Kson vector of length {}", enc.len()),
        move |b| b.iter(|| decode_full(black_box(&enc)).map(|x: Kson| x).unwrap()),
    );
}
criterion_group!(
    benches,
    bench_construction,
    bench_enc,
    bench_enc_single_alloc,
    bench_dec,
    bench_enc_flat,
    bench_dec_flat
);
criterion_main!(benches);
