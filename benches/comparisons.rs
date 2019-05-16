#[macro_use]
extern crate criterion;

use criterion::{black_box, Criterion};
use kson::{encoding::ser::Serializer, prelude::*};
use serde_json;

pub fn u64_to_bytes_le(x: u64) -> Bytes { Bytes::from(u64::to_le_bytes(x).to_vec()) }

const BENCH_INT: i64 = i64::max_value();

fn kson_i64_encode(c: &mut Criterion) {
    c.bench_function("KSON i64 encode", |b| {
        let k = BENCH_INT.into_kson();
        b.iter(|| encode_full(&k))
    });
}

fn kson_i64_ser(c: &mut Criterion) {
    c.bench_function("KSON i64 ser", |b| {
        b.iter(|| {
            let mut out = Vec::with_capacity(128);
            out.put_i64(black_box(BENCH_INT));
        })
    });
}
fn json_i64_encode(c: &mut Criterion) {
    c.bench_function("JSON i64 encode", |b| {
        b.iter(|| serde_json::to_string(&black_box(BENCH_INT)).unwrap())
    });
}

fn kson_i64_decode(c: &mut Criterion) {
    c.bench_function("KSON i64 decode", |b| {
        let buf = encode_full(&BENCH_INT.into_kson());
        b.iter(|| i64::from_kson(decode_full(black_box(&buf)).unwrap()).unwrap())
    });
}

fn kson_i64_deser(c: &mut Criterion) {
    c.bench_function("KSON i64 deser", |b| {
        let buf = encode_full(&BENCH_INT.into_kson());
        b.iter(|| decode_full(black_box(&buf)).map(|i: i64| i).unwrap())
    });
}

fn json_i64_decode(c: &mut Criterion) {
    c.bench_function("JSON i64 decode", |b| {
        let buf = serde_json::to_string(&BENCH_INT).unwrap();
        b.iter(|| {
            serde_json::from_str(black_box(&buf))
                .map(|x: i64| x)
                .unwrap()
        })
    });
}

fn bench_str() -> Vec<u8> { (0..10_000).map(|x| x as u8).collect() }

fn kson_str_encode(c: &mut Criterion) {
    c.bench_function("KSON string encode", |b| {
        let s = bench_str();
        let k = Bytes::from(s).into_kson();
        b.iter(|| encode_full(black_box(&k)))
    });
}

fn kson_str_ser(c: &mut Criterion) {
    c.bench_function("KSON string ser", |b| {
        let s = bench_str();
        let k = Bytes::from(s);
        b.iter(|| (&mut Vec::new()).put_bytes(&k))
    });
}

fn json_str_encode(c: &mut Criterion) {
    c.bench_function("JSON string encode", |b| {
        let s = bench_str();
        b.iter(|| serde_json::to_string(&black_box(&s)).unwrap())
    });
}

fn kson_str_decode(c: &mut Criterion) {
    c.bench_function("KSON string decode", |b| {
        let s = Bytes::from(bench_str());
        let buf = encode_full(&s.into_kson());
        b.iter(|| Bytes::from_kson(decode_full(black_box(&buf)).unwrap()).unwrap())
    });
}

fn kson_str_deser(c: &mut Criterion) {
    c.bench_function("KSON string deser", |b| {
        let s = Bytes::from(bench_str());
        let buf = encode_full(&s.into_kson());
        b.iter(|| decode_full(black_box(&buf)).map(|b: Bytes| b).unwrap())
    });
}

fn json_str_decode(c: &mut Criterion) {
    c.bench_function("JSON string decode", |b| {
        let buf = serde_json::to_string(&bench_str()).unwrap();
        b.iter(|| serde_json::from_str(&buf).map(|x: Vec<u8>| x).unwrap())
    });
}

fn bench_small_str() -> Vec<u8> { (0..128).map(|x| x as u8).collect() }

fn kson_small_str_encode(c: &mut Criterion) {
    c.bench_function("KSON small_string encode", |b| {
        let s = bench_small_str();
        let k = Bytes::from(s).into_kson();
        b.iter(|| encode_full(black_box(&k)))
    });
}

fn kson_small_str_ser(c: &mut Criterion) {
    c.bench_function("KSON small_string ser", |b| {
        let s = bench_small_str();
        let k = Bytes::from(s);
        b.iter(|| (&mut Vec::new()).put_bytes(&k))
    });
}

fn json_small_str_encode(c: &mut Criterion) {
    c.bench_function("JSON small_string encode", |b| {
        let s = bench_small_str();
        b.iter(|| serde_json::to_string(&black_box(&s)))
    });
}

fn kson_small_str_decode(c: &mut Criterion) {
    c.bench_function("KSON small_string decode", |b| {
        let s = Bytes::from(bench_small_str());
        let buf = encode_full(&s.into_kson());
        b.iter(|| Bytes::from_kson(decode_full(black_box(&buf)).unwrap()).unwrap())
    });
}

fn kson_small_str_deser(c: &mut Criterion) {
    c.bench_function("KSON small_string deser", |b| {
        let s = Bytes::from(bench_small_str());
        let buf = encode_full(&s.into_kson());
        b.iter(|| decode_full(black_box(&buf)).map(|b: Bytes| b).unwrap())
    });
}

fn json_small_str_decode(c: &mut Criterion) {
    c.bench_function("JSON small_string decode", |b| {
        let buf = serde_json::to_string(&bench_small_str()).unwrap();
        b.iter(|| serde_json::from_str(&buf).map(|x: Vec<u8>| x).unwrap())
    });
}

fn bench_tiny_str() -> Vec<u8> { (0..8).map(|x| x as u8).collect() }

fn kson_tiny_str_encode(c: &mut Criterion) {
    c.bench_function("KSON tiny_string encode", |b| {
        let s = bench_tiny_str();
        let k = Bytes::from(s).into_kson();
        b.iter(|| encode_full(black_box(&k)))
    });
}

fn kson_tiny_str_ser(c: &mut Criterion) {
    c.bench_function("KSON tiny_string ser", |b| {
        let s = bench_tiny_str();
        let k = Bytes::from(s);
        b.iter(|| (&mut Vec::new()).put_bytes(&k))
    });
}

fn json_tiny_str_encode(c: &mut Criterion) {
    c.bench_function("JSON tiny_string encode", |b| {
        let s = bench_tiny_str();
        b.iter(|| serde_json::to_string(&black_box(&s)))
    });
}

fn kson_tiny_str_decode(c: &mut Criterion) {
    c.bench_function("KSON tiny_string decode", |b| {
        let s = Bytes::from(bench_tiny_str());
        let buf = encode_full(&s.into_kson());
        b.iter(|| Bytes::from_kson(decode_full(black_box(&buf)).unwrap()).unwrap())
    });
}

fn kson_tiny_str_deser(c: &mut Criterion) {
    c.bench_function("KSON tiny_string deser", |b| {
        let s = Bytes::from(bench_tiny_str());
        let buf = encode_full(&s.into_kson());
        b.iter(|| decode_full(black_box(&buf)).map(|b: Bytes| b).unwrap())
    });
}

fn json_tiny_str_decode(c: &mut Criterion) {
    c.bench_function("JSON tiny_string decode", |b| {
        let buf = serde_json::to_string(&bench_tiny_str()).unwrap();
        b.iter(|| serde_json::from_str(&buf).map(|x: Vec<u8>| x).unwrap())
    });
}

criterion_group!(
    benches,
    kson_i64_encode,
    kson_i64_ser,
    json_i64_encode,
    kson_i64_decode,
    kson_i64_deser,
    json_i64_decode,
    kson_str_encode,
    kson_str_ser,
    json_str_encode,
    kson_str_decode,
    kson_str_deser,
    json_str_decode,
    kson_small_str_encode,
    kson_small_str_ser,
    json_small_str_encode,
    kson_small_str_decode,
    kson_small_str_deser,
    json_small_str_decode,
    kson_tiny_str_encode,
    kson_tiny_str_ser,
    json_tiny_str_encode,
    kson_tiny_str_decode,
    kson_tiny_str_deser,
    json_tiny_str_decode,
);

criterion_main!(benches);
