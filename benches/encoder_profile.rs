// extern crate criterion;
// extern crate kson;
//
// use bytes::Bytes;
// use criterion::black_box;
// use kson::prelude::*;
//
// const N_ARR: usize = 10;
// const N_MAP: usize = 100;
//
// fn big_k() -> Kson {
//    let v0: Vec<Kson> = (0..N_ARR).map(|i| Kson::from(i as u64)).collect();
//    let m: VecMap<Bytes, Kson> = (0..N_MAP)
//        .map(|i| {
//            (
//                Bytes::from(u64::to_le_bytes(i as u64).to_vec()),
//                Kson::from(v0.clone()),
//            )
//        })
//        .collect();
//    let v: Vec<Kson> = std::iter::repeat(m).map(Kson::from).take(N_ARR).collect();
//    Kson::from(v)
//}
// const N_REPS: u8 = 100;
//
// fn main() {
//    let big_k = black_box(big_k());
//    // let size = black_box(&big_k).size();
//    let enc_outer = encode_full(black_box(&big_k));
//    for _ in 0..N_REPS {
//        let out = Vec::with_capacity(4096);
//        assert_eq!(encode(&big_k, out), enc_outer);
//    }
//}
