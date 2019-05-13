use common_utils::kson_strategy::*;
use kson::{encoding::*, *};
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn encode_decode_small(i in proptest::num::i64::ANY) {
        // println!("trying to encode {:?}", i);
        let k = Kson::from(i);
        let enc = encode_full(&k);
        // println!("tag is {:b}", enc[0]);
        // println!("encoded as {:?}", enc.as_slice());
        let dec = decode_full(&enc).ok();
        // println!("decoded as {:?}", dec);
        if dec != Some(k.clone()) {
            panic!(format!("Tried encoding\n {:?}\n as \n{:?}\n got \n{:?}\n", k, enc, dec))
        }
    }

    #[test]
    fn encode_decode_large(i in arb_bigint()) {
        // println!("trying to encode {:?}", i);
        let k = Kson::from(i);
        let enc = encode_full(&k);
        // println!("tag is {:b}", enc[0]);
        // println!("encoded as {:?}", enc.as_slice());
        let dec = decode_full(&enc).ok();
        // println!("decoded as {:?}", dec);
        if dec != Some(k.clone()) {
            panic!(format!("Tried encoding\n {:?}\n as \n{:?}\n got \n{:?}\n", k, enc, dec))
        }
    }

}
