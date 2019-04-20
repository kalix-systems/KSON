use common_utils::kson_strategy::*;
use kson::encoding::*;
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig { cases: 1_000, ..ProptestConfig::default() })]

    #[test]
    fn encode_decode(k in arb_kson()) {
        println!("trying to encode {:?}", k);
        let enc = encode_full(k.clone());
        println!("tag is {:b}", enc[0]);
        println!("encoded as {:?}", enc.as_slice());
        let dec = decode_full(&enc);
        println!("decoded as {:?}", dec);
        if dec != Some(k.clone()) {
            // panic!(format!("Tried encoding\n {:?}\n as \n{:?}\n got \n{:?}\n", k, enc, dec))
            panic!("assertion failed")
        }
    }
}
