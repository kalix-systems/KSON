use bytes::buf::IntoBuf;
use kson::encoding::*;
use kson_strategy::*;
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig { cases: 1_000, ..ProptestConfig::default() })]

    #[test]
    fn encode_decode(k in arb_kson()) {
        println!("trying to encode {}", k);
        let enc = encode_full(&k);

        let dec = decode(&mut enc.into_buf()).ok();

        if dec != Some(k.clone()) {
            panic!("assertion failed")
        }
    }
}
