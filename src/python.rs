#![allow(non_snake_case)]
use crate::{
    vecmap::*,
    Inum::{self, *},
    Kson::{self, *},
};
use bytes::Bytes;
use num_bigint::{BigInt, Sign::*};
use pyo3::{
    prelude::*,
    types::{IntoPyDict, PyAny, PyBool, PyBytes, PyDict, PyLong},
};

impl ToPyObject for Kson {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            Null => py.None(),
            Bool(b) => PyBool::new(py, *b).into_object(py),
            Byt(s) => PyBytes::new(py, s).into_object(py),
            Kint(val) => val.to_object(py),
            Array(vector) => vector.to_object(py),
            Map(vmap) => vmap.to_object(py),
        }
    }
}

impl IntoPyObject for Kson {
    fn into_object(self, py: Python) -> PyObject {
        match self {
            Null => {
                let val: Option<Self> = None;
                val.into_object(py)
            }
            Bool(b) => PyBool::new(py, b).into_object(py),
            Byt(s) => PyBytes::new(py, &s).into_object(py),
            Kint(val) => val.into_object(py),
            Array(vector) => vector.into_object(py),
            Map(vmap) => vmap.into_object(py),
        }
    }
}

impl<'source> FromPyObject<'source> for Kson {
    fn extract(ob: &'source PyAny) -> PyResult<Self> {
        if ob.is_none() {
            Ok(Null)
        } else {
            ob.extract()
                .map(Bool)
                .or_else(|_| ob.extract().and_then(bytes_from_any).map(Byt))
                .or_else(|_| ob.extract().map(Kint))
                .or_else(|_| ob.extract().map(Array))
                .or_else(|_| ob.extract().and_then(pydict_to_kson))
        }
    }
}

/// Converts reference to `PyAny` into `Bytes`.
///
/// # Arguments
///
/// * `obj: &PyAny` - The python object to be converted.
///
/// # Errors
///
/// This function will return an error if the object cannot be converted into bytes.
pub fn bytes_from_any(obj: &PyAny) -> PyResult<Bytes> {
    let bytes: &PyBytes = obj.try_into_exact()?;
    Ok(Bytes::from(bytes.as_bytes()))
}

fn pydict_to_kson(pd: &PyDict) -> PyResult<Kson> {
    let mut out = Vec::with_capacity(pd.len());
    for (k, v) in pd {
        out.push((bytes_from_any(k)?, v.extract()?))
    }
    Ok(Map(VecMap::from(out)))
}

#[pyclass]
struct PyInt {
    sign: bool,
    /// little-endian digits
    digits: Vec<u8>,
}

impl ToPyObject for Inum {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            I64(num) => num.to_object(py),
            Int(num) => {
                PyRef::new(
                    py,
                    PyInt {
                        sign:   num.sign() != Minus,
                        digits: num.to_bytes_le().1,
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
                        sign:   num.sign() != Minus,
                        digits: num.to_bytes_le().1,
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
                let mut int_num = BigInt::from_bytes_le(Plus, num.digits.as_slice());
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Null;
        let py_val = val.to_object(py);
        assert_eq!(py_val, py.None());
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val, Some(Null));

        let py_val = val.into_object(py);
        assert_eq!(py_val, py.None());
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val, Some(Null));
    }

    #[test]
    fn bool() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Bool(true);
        let py_val = val.to_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Bool(true));

        let py_val = val.into_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Bool(true));
    }

    #[test]
    fn str() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Byt(Bytes::from(vec![1]));
        let py_val = val.to_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Byt(Bytes::from(vec![1])));
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
    fn kint() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Kint(I64(2));
        let py_val = val.to_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Kint(I64(2)));
    }

    #[test]
    fn array() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let val = Array(vec![Kint(I64(2))]);
        let py_val = val.to_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.into_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), Array(vec![Kint(I64(2))]));
    }

    #[test]
    fn vmap() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let bmap = VecMap::from_sorted(vec![(Bytes::from(vec![0]), Kson::from(2u64))]);

        let val = Map(bmap);
        let py_val = val.to_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.clone().into_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);
    }

    #[test]
    fn kson() {
        let gil = Python::acquire_gil();
        let py = gil.python();

        let bmap = VecMap::from_sorted(vec![(Bytes::from(vec![0]), Kson::from(2))]);

        let val = Map(bmap);
        let py_val = val.to_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);

        let py_val = val.clone().into_object(py);
        let unpy_val: Option<Kson> = py_val.extract(py).ok();
        assert_eq!(unpy_val.unwrap(), val);
    }
}
