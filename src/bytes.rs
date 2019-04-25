use pyo3::prelude::*;
use pyo3::types::*;
use std::ops::{Deref, DerefMut};
use std::vec::IntoIter;

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub struct Bytes(pub Vec<u8>);

impl Bytes {
    fn into_vec(self) -> Vec<u8> {
        self.0
    }
}

trait AsBytes: Clone {
    fn to_bytes(&self) -> Bytes {
        self.clone().into_bytes()
    }

    fn into_bytes(self) -> Bytes {
        self.to_bytes()
    }
}

impl AsBytes for &[u8] {
    fn into_bytes(self) -> Bytes {
        Bytes(self.to_vec())
    }
}

impl Deref for Bytes {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Bytes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl AsRef<[u8]> for Bytes {
    fn as_ref(&self) -> &[u8] {
        self.deref().as_ref()
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

impl From<Vec<u8>> for Bytes {
    fn from(v: Vec<u8>) -> Bytes {
        Bytes(v)
    }
}

impl IntoIterator for Bytes {
    type Item = u8;
    type IntoIter = IntoIter<u8>;
    fn into_iter(self) -> IntoIter<u8> {
        self.into_vec().into_iter()
    }
}
