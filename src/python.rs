#![allow(non_snake_case)]
use crate::bytes::Bytes;
use crate::Atom::*;
use crate::Container::*;
use crate::Inum::*;
use crate::{Atom, Atomic, Contain, Container, Inum, Kson};
use pyo3::{
    prelude::*,
    types::{PyAny, PyBool, PyBytes, PyDict, PyList, PyLong, PyTuple},
    PyErr,
};
use rug::{integer::Order::Msf, Integer};
use std::collections::BTreeMap;
use std::iter::FromIterator;

impl ToPyObject for Kson {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            Atomic(a) => a.to_object(py),
            Contain(c) => c.to_object(py),
        }
    }
}

impl IntoPyObject for Kson {
    fn into_object(self, py: Python) -> PyObject {
        match self {
            Atomic(a) => a.into_object(py),
            Contain(c) => c.into_object(py),
        }
    }
}

impl<'source> FromPyObject<'source> for Kson {
    fn extract(ob: &'source PyAny) -> PyResult<Self> {
        let py_list: Result<&'source PyList, _> = ob.try_into_exact();

        match py_list {
            Ok(py_list) => Ok(Contain(py_list.extract()?)),
            Err(_e) => {
                let py_dict: Result<&'source PyDict, _> = ob.try_into_exact();
                match py_dict {
                    Ok(py_dict) => Ok(Contain(py_dict.extract()?)),
                    Err(_e) => Ok(Atomic(ob.extract()?)),
                }
            }
        }
    }
}

impl IntoPyObject for Atom {
    fn into_object(self, py: Python) -> PyObject {
        match self {
            Null => {
                let val: Option<Self> = None;
                val.into_object(py)
            }
            Bool(b) => b.into_object(py),
            Str(s) => s.into_object(py),
            ANum(val) => val.to_object(py),
        }
    }
}

impl ToPyObject for Atom {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            Null => py.None(),
            Bool(b) => b.to_object(py),
            Str(s) => s.to_object(py),
            ANum(val) => val.to_object(py),
        }
    }
}

impl<'source> FromPyObject<'source> for Atom {
    fn extract(ob: &'source PyAny) -> PyResult<Self> {
        if ob.is_none() {
            return Ok(Null);
        }

        let py_bool: Result<&'source PyBool, _> = ob.try_into_exact();
        match py_bool {
            Ok(b) => Ok(Bool(b.is_true())),
            Err(_e) => {
                let py_bytes: Result<&'source PyBytes, _> = ob.try_into_exact();
                match py_bytes {
                    Ok(py_bytes) => Ok(Str(Bytes(py_bytes.as_bytes().to_vec()))),
                    Err(_e) => {
                        let n: PyResult<Inum> = ob.extract();
                        match n {
                            Ok(n) => Ok(ANum(n)),
                            // TODO, better error handling
                            Err(_) => Ok(Null),
                        }
                    }
                }
            }
        }
    }
}

impl<T: IntoPyObject> IntoPyObject for Container<T> {
    fn into_object(self, py: Python) -> PyObject {
        match self {
            Array(vector) => vector.into_object(py),
            Map(btmap) => btmap.into_object(py),
        }
    }
}

impl<T: ToPyObject> ToPyObject for Container<T> {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            Array(vector) => vector.to_object(py),
            Map(btmap) => btmap.to_object(py),
        }
    }
}

impl<'source, T> FromPyObject<'source> for Container<T>
where
    T: FromPyObject<'source>,
{
    fn extract(ob: &'source PyAny) -> PyResult<Self> {
        let py_dict: Result<&'source PyDict, _> = ob.try_into_exact();

        match py_dict {
            Ok(py_dict) => {
                let btmap =
                    BTreeMap::from_iter(py_dict.iter().map(|(k, v)| -> (Bytes, T) {
                        (k.extract().unwrap(), v.extract().unwrap())
                    }));

                Ok(Map(btmap))
            }
            Err(_e) => {
                let py_list: Result<&'source PyList, _> = ob.try_into_exact();

                match py_list {
                    Ok(py_list) => {
                        let vector =
                            Vec::from_iter(py_list.iter().map(|v| -> T { v.extract().unwrap() }));

                        Ok(Array(vector))
                    }
                    Err(_e) => ob.extract(),
                }
            }
        }
    }
}

#[pyclass]
struct PyInt {
    sign: bool,
    digits: Vec<u64>,
}

impl ToPyObject for Inum {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            I64(num) => num.to_object(py),
            Int(num) => PyRef::new(
                py,
                PyInt {
                    sign: (num >= &0),
                    digits: num.to_digits(Msf),
                },
            )
            .unwrap()
            .to_object(py),
        }
    }
}

impl IntoPyObject for Inum {
    fn into_object(self, py: Python) -> PyObject {
        match self {
            I64(num) => num.into_object(py),
            Int(num) => PyRef::new(
                py,
                PyInt {
                    sign: (num >= 0),
                    digits: num.to_digits(Msf),
                },
            )
            .unwrap()
            .into_object(py),
        }
    }
}

impl<'source> FromPyObject<'source> for Inum {
    fn extract(ob: &'source PyAny) -> PyResult<Inum> {
        let num: Result<&'source PyLong, _> = ob.try_into_exact();
        match num {
            Ok(num) => Ok(I64(num.extract()?)),
            Err(_e) => {
                let num: &'source PyInt = ob.try_into_exact()?;
                let mut int_num = Integer::from_digits(num.digits.as_slice(), Msf);
                if !num.sign {
                    int_num = -int_num;
                }
                Ok(Int(int_num))
            }
        }
    }
}

impl ToPyObject for Bytes {
    fn to_object(&self, py: Python) -> PyObject {
        PyBytes::new(py, self.as_slice()).into_object(py)
    }
}

impl IntoPyObject for Bytes {
    fn into_object(self, py: Python) -> PyObject {
        PyBytes::new(py, self.as_slice()).into_object(py)
    }
}

impl<'a> FromPyObject<'a> for Bytes {
    fn extract(obj: &'a PyAny) -> PyResult<Bytes> {
        let bytes: &'a PyBytes = obj.try_into_exact()?;
        Ok(Bytes(bytes.as_bytes().to_vec()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn null() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Null;
        let py_val = val.to_object(py);
        assert_eq!(py_val, py.None());
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val, Some(Null));

        let py_val = val.into_object(py);
        assert_eq!(py_val, py.None());
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val, Some(Null));
    }

    #[test]
    fn bool() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Bool(true);
        let py_val = val.to_object(py);
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Bool(true));

        let py_val = val.into_object(py);
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Bool(true));
    }

    #[test]
    fn bytes() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Bytes(vec![1]);
        let py_val = val.to_object(py);
        let unpy_val: Option<Bytes> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Bytes> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Bytes(vec![1]));
    }

    #[test]
    fn str() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Str(Bytes(vec![1]));
        let py_val = val.to_object(py);
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Str(Bytes(vec![1])));
    }

    #[test]
    fn inum() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = I64(2);
        let py_val = val.to_object(py);
        let unpy_val: Option<Inum> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Inum> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), I64(2));
    }

    #[test]
    fn anum() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = ANum(I64(2));
        let py_val = val.to_object(py);
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), ANum(I64(2)));
    }

    #[test]
    fn array() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Array(vec![ANum(I64(2))]);
        let py_val = val.to_object(py);
        let unpy_val: Option<Container<Atom>> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Container<Atom>> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Array(vec![ANum(I64(2))]));
    }

    #[test]
    fn btmap() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let mut bmap = BTreeMap::new();
        bmap.insert(Bytes(vec![0]), ANum(I64(2)));

        let val = Map(bmap);
        let py_val = val.to_object(py);
        let unpy_val: Option<Container<Atom>> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.clone().into_object(py);
        let unpy_val: Option<Container<Atom>> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);
    }

    #[test]
    fn kson() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let mut bmap = BTreeMap::new();
        bmap.insert(Bytes(vec![0]), Atomic(ANum(I64(2))));

        let val = Contain(Map(bmap));
        let py_val = val.to_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.clone().into_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);
    }
}
