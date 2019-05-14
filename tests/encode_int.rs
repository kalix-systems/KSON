use common_utils::kson_strategy::*;
use kson::{encoding::*, *};
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig { cases: 1_000, ..ProptestConfig::default() })]

    #[test]
    fn encode_decode_small(i in proptest::num::i64::ANY) {
        let k = Kson::from(i);
        let enc = encode_full(&k);

        let dec = decode_full(&enc).ok();

        if dec != Some(k.clone()) {
            panic!(format!("Tried encoding\n {:?}\n as \n{:x?}\n got \n{:?}\n", k, enc, dec))
        }
    }

    #[test]
    fn encode_decode_large(i in arb_bigint()) {
        let k = Kson::from(i);
        let enc = encode_full(&k);

        let dec = decode_full(&enc).ok();

        if dec != Some(k.clone()) {
            panic!(format!("Tried encoding\n {:?}\n as \n{:x?}\n got \n{:?}\n", k, enc, dec))
        }
    }

}
