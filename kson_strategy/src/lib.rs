use bytes::Bytes;
use kson::{
    prelude::{f16, FromBuf},
    vecmap::VecMap,
    Kson,
};
use num_bigint::BigInt;
use num_traits::Num;
use proptest::prelude::*;

/// arbitrary Integer for use with proptest
pub fn arb_bigint() -> impl Strategy<Value = BigInt> {
    "-?1[0-1]{63,}".prop_map(|n| -> BigInt { BigInt::from_str_radix(&n, 2).unwrap() })
}

/// arbitrary Bytes for use with proptest
pub fn arb_bs() -> impl Strategy<Value = Bytes> {
    ".*".prop_map(|s| -> Bytes { Bytes::from(s) })
}

/// arbitrary KSON for use with proptest
pub fn arb_kson() -> impl Strategy<Value = Kson> {
    let leaf = prop_oneof![
        Just(Kson::Null),
        // misc
        any::<bool>().prop_map(Kson::Bool),
        any::<String>().prop_map(Kson::from_buf),
        any::<char>().prop_map(Kson::from),
        any::<()>().prop_map(Kson::from),
        // sizes
        any::<usize>().prop_map(Kson::from),
        any::<isize>().prop_map(Kson::from),
        // integers
        // 8-bit
        any::<u8>().prop_map(Kson::from),
        any::<i8>().prop_map(Kson::from),
        // 16-bit
        any::<u16>().prop_map(Kson::from),
        any::<i16>().prop_map(Kson::from),
        // 32-bit
        any::<u32>().prop_map(Kson::from),
        any::<i32>().prop_map(Kson::from),
        // 64-bit
        any::<u64>().prop_map(Kson::from),
        any::<i64>().prop_map(Kson::from),
        // 128-bit
        any::<u128>().prop_map(Kson::from),
        any::<i128>().prop_map(Kson::from),
        // floats
        any::<u16>().prop_map(|n| Kson::from(f16::from_bits(n))),
        any::<f32>().prop_map(Kson::from),
        any::<f64>().prop_map(Kson::from),
        // bigint
        arb_bigint().prop_map(Kson::from),
        // bytestrings
        arb_bs().prop_map(Kson::from),
    ];
    leaf.prop_recursive(
        20, // max depth
        20, // max nodes
        20, // max items per collection
        |inner| {
            prop_oneof![
                prop::collection::vec(inner.clone(), 0..10).prop_map(Kson::from),
                prop::collection::btree_map(arb_bs(), inner, 0..10)
                    .prop_map(|m| Kson::from(VecMap::from(m)))
            ]
        },
    )
}
