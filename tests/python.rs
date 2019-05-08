// use common_utils::kson_strategy::*;
// use kson::Kson;
// use proptest::prelude::*;
// use pyo3::prelude::*;

// proptest! {
// test]
// fn python(val in arb_kson()) {
// let gil = Python::acquire_gil();
// let py = gil.python();

// let py_val = val.to_object(py);
// let unpy_val: Kson = py_val.extract(py).unwrap();

// assert_eq!(val, unpy_val);
//}
// }
