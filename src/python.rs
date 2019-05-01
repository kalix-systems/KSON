#![allow(non_snake_case)]
use crate::{
    vecmap::*,
    Atom::{self, *},
    Atomic, Contain,
    Container::{self, *},
    Inum::{self, *},
    Kson,
};
use bytes::Bytes;
use pyo3::{
    prelude::*,
    types::{IntoPyDict, PyAny, PyBool, PyBytes, PyDict, PyList, PyLong, PyTuple},
    PyErr,
};
use rug::{integer::Order::Msf, Integer};
use std::{collections::BTreeMap, iter::FromIterator};

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
            Bool(b) => PyBool::new(py, b).into_object(py),
            Str(s) => PyBytes::new(py, &s).into_object(py),
            ANum(val) => val.to_object(py),
        }
    }
}

impl ToPyObject for Atom {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            Null => py.None(),
            Bool(b) => PyBool::new(py, *b).into_object(py),
            Str(s) => PyBytes::new(py, s).into_object(py),
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
                    Ok(py_bytes) => Ok(Str(Bytes::from(py_bytes.as_bytes()))),
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

impl<T: IntoPyObject + ToPyObject> IntoPyObject for Container<T> {
    fn into_object(self, py: Python) -> PyObject {
        match self {
            Array(vector) => vector.into_object(py),
            Map(vmap) => vmap.into_object(py),
        }
    }
}

impl<T: ToPyObject> ToPyObject for Container<T> {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            Array(vector) => vector.to_object(py),
            Map(vmap) => vmap.to_object(py),
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
                let vmap: VecMap<Bytes, T> = py_dict
                    .iter()
                    .map(|(k, v)| (bytes_from_any(k).unwrap(), v.extract().unwrap()))
                    .collect();
                Ok(Map(vmap))
            }
            Err(_e) => Ok(Array(ob.extract()?)),
        }
    }
}

#[pyclass]
struct PyInt {
    sign:   bool,
    digits: Vec<u64>,
}

impl ToPyObject for Inum {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            I64(num) => num.to_object(py),
            Int(num) => {
                PyRef::new(
                    py,
                    PyInt {
                        sign:   (*num >= 0),
                        digits: num.to_digits(Msf),
                    },
                )
                .unwrap()
                .to_object(py)
            }
        }
    }
}

impl IntoPyObject for Inum {
    fn into_object(self, py: Python) -> PyObject {
        match self {
            I64(num) => num.into_object(py),
            Int(num) => {
                PyRef::new(
                    py,
                    PyInt {
                        sign:   (num >= 0),
                        digits: num.to_digits(Msf),
                    },
                )
                .unwrap()
                .into_object(py)
            }
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

impl<V: ToPyObject> IntoPyObject for VecMap<Bytes, V> {
    fn into_object(self, py: Python) -> PyObject {
        self.into_iter()
            .map(|(k, v)| (PyBytes::new(py, &k), v))
            .into_py_dict(py)
            .to_object(py)
    }
}

impl<V: ToPyObject> ToPyObject for VecMap<Bytes, V> {
    fn to_object(&self, py: Python) -> PyObject {
        self.iter()
            .map(|(k, v)| (PyBytes::new(py, k), v))
            .into_py_dict(py)
            .to_object(py)
    }
}

pub fn bytes_from_any(obj: &PyAny) -> PyResult<Bytes> {
    let bytes: &PyBytes = obj.try_into_exact()?;
    Ok(Bytes::from(bytes.as_bytes()))
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

        let val = Bytes::from(vec![1]);
        let py_val = PyBytes::new(py, &val).into_object(py);
        let unpy_val: Atom = py_val.extract(py).unwrap();
        assert_eq!(unpy_val, Str(Bytes::from(vec![1])));
    }

    #[test]
    fn str() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Str(Bytes::from(vec![1]));
        let py_val = val.to_object(py);
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Atom> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Str(Bytes::from(vec![1])));
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
    fn vmap() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let bmap = VecMap::from_sorted(vec![(Bytes::from(vec![0]), Atom::from(2))]);

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

        let bmap = VecMap::from_sorted(vec![(Bytes::from(vec![0]), Kson::from(2))]);

        let val = Contain(Map(bmap));
        let py_val = val.to_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.clone().into_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);
    }
}
