#[macro_use]
extern crate criterion;

use criterion::{black_box, Criterion};
use kson::{encoding::ser::SerializerExt, prelude::*};
use serde_json;

pub fn u64_to_bytes_le(x: u64) -> Bytes { Bytes::from(u64::to_le_bytes(x).to_vec()) }

fn kson_i64_encode(c: &mut Criterion) {
    c.bench_function("KSON i64 encode", |b| {
        let k = 1_000_000i64.into_kson();
        b.iter(|| encode_full(black_box(&k)))
    });
}

fn kson_i64_ser(c: &mut Criterion) {
    c.bench_function("KSON i64 ser", |b| {
        b.iter(|| {
            let mut out = Vec::with_capacity(128);
            out.put_i64(black_box(1_000_000));
        })
    });
}
fn json_i64_encode(c: &mut Criterion) {
    c.bench_function("JSON i64 encode", |b| {
        b.iter(|| serde_json::to_string(&black_box(1_000_000i64)))
    });
}

fn kson_i64_decode(c: &mut Criterion) {
    c.bench_function("KSON i64 decode", |b| {
        let buf = encode_full(&1_000_000i64.into_kson()).into_buf();
        b.iter(|| decode_full(black_box(buf.clone())))
    });
}

fn json_i64_decode(c: &mut Criterion) {
    c.bench_function("JSON i64 decode", |b| {
        b.iter(|| serde_json::to_string(&black_box(1_000_000i64)))
    });
}

fn kson_str_encode(c: &mut Criterion) {
    c.bench_function("KSON string encode", |b| {
        let s: Vec<u8> = (0..10_000).map(|x| x as u8).collect();
        let k = Bytes::from(s).into_kson();
        b.iter(|| encode_full(black_box(&k)))
    });
}

fn json_str_encode(c: &mut Criterion) {
    c.bench_function("JSON string encode", |b| {
        let s: Vec<u8> = (0..10_000).map(|x| x as u8).collect();
        b.iter(|| serde_json::to_string(&black_box(&s)))
    });
}

criterion_group!(
    benches,
    kson_i64_encode,
    kson_i64_ser,
    json_i64_encode,
    // kson_i64_decode,
    // json_i64_decode,
    kson_str_encode,
    json_str_encode,
);

criterion_main!(benches);
