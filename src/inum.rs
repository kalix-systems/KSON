use pyo3::prelude::*;
use pyo3::types::{PyAny, PyLong};
use rug::Integer;
use std::convert::TryFrom;
use std::ops::{AddAssign, MulAssign};

use crate::util::*;
use crate::{compose_from, from_as, from_fn};

/// `INum`s are either `i64` or `Integer`s
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Inum {
    I64(i64),
    Int(Integer),
}

use Inum::*;

impl ToPyObject for Inum {
    fn to_object(&self, py: Python) -> PyObject {
        match &self {
            I64(num) => num.to_object(py),
            Int(num) => {
                // Returns None until we switch back to BigInt
                let val: Option<Self> = None;
                val.to_object(py)
            }
        }
    }
}

impl<'source> FromPyObject<'source> for Inum {
    fn extract(ob: &'source PyAny) -> PyResult<Self> {
        ob.extract()
    }
}

from_fn!(Inum, i64, I64);
from_fn!(Inum, u64, |u| {
    let i = u as i64;
    if i >= 0 {
        Inum::from(i)
    } else {
        Inum::Int(Integer::from(u))
    }
});

from_fn!(Inum, Integer, |i: Integer| i
    .to_i64()
    .map_or_else(|| Int(i), I64));

impl From<Inum> for Integer {
    fn from(i: Inum) -> Integer {
        match i {
            Inum::I64(i) => Integer::from(i),
            Inum::Int(i) => i,
        }
    }
}

impl TryFrom<Inum> for i64 {
    type Error = Integer;
    fn try_from(i: Inum) -> Result<Self, Integer> {
        match i {
            Inum::I64(i) => Ok(i),
            Inum::Int(i) => Err(i),
        }
    }
}

impl TryFrom<Inum> for u64 {
    type Error = Inum;
    fn try_from(n: Inum) -> Result<Self, Inum> {
        match &n {
            Inum::I64(i) => {
                if *i >= 0 {
                    Ok(*i as u64)
                } else {
                    Err(n)
                }
            }
            Inum::Int(i) => {
                if let Some(u) = i.to_u64() {
                    Ok(u)
                } else {
                    Err(n)
                }
            }
        }
    }
}

impl AddAssign<i32> for Inum {
    fn add_assign(&mut self, other: i32) {
        match self {
            I64(i) => *i += other as i64,
            Int(i) => *i += other,
        }
    }
}
impl MulAssign<i32> for Inum {
    fn mul_assign(&mut self, other: i32) {
        match self {
            I64(i) => *i *= other as i64,
            Int(i) => *i *= other,
        }
    }
}

impl PartialEq<i64> for Inum {
    fn eq(&self, other: &i64) -> bool {
        match self {
            I64(i) => i.eq(other),
            Int(i) => i.eq(other),
        }
    }
}

impl PartialOrd<i64> for Inum {
    fn partial_cmp(&self, other: &i64) -> Option<core::cmp::Ordering> {
        match self {
            I64(i) => i.partial_cmp(other),
            Int(i) => i.partial_cmp(other),
        }
    }
}

impl Inum {
    fn into_int(self) -> Integer {
        match self {
            Inum::I64(i) => Integer::from(i),
            Inum::Int(i) => i,
        }
    }

    fn into_i64(self) -> Option<i64> {
        match self {
            Inum::I64(i) => Some(i),
            _ => None,
        }
    }

    fn to_int(&self) -> Integer {
        match self {
            Inum::I64(i) => Integer::from(i.clone()),
            Inum::Int(i) => i.clone(),
        }
    }

    fn to_i64(&self) -> Option<i64> {
        match self {
            Inum::I64(i) => Some(i.clone()),
            _ => None,
        }
    }

    fn to_i32(&self) -> Option<i32> {
        match self {
            Inum::I64(i) => {
                if std::i32::MIN as i64 <= *i || *i <= std::i32::MAX as i64 {
                    Some(i.clone() as i32)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn to_i16(&self) -> Option<i16> {
        match self {
            Inum::I64(i) => {
                if std::i16::MIN as i64 <= *i || *i <= std::i16::MAX as i64 {
                    Some(i.clone() as i16)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn to_i8(&self) -> Option<i8> {
        match self {
            Inum::I64(i) => {
                if std::i8::MIN as i64 <= *i || *i <= std::i8::MAX as i64 {
                    Some(i.clone() as i8)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn to_u8(&self) -> Option<u8> {
        match self {
            Inum::I64(i) => {
                if 0 <= *i && *i <= std::u8::MAX as i64 {
                    Some(i.clone() as u8)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn to_u16(&self) -> Option<u16> {
        match self {
            Inum::I64(i) => {
                if 0 <= *i && *i <= std::u16::MAX as i64 {
                    Some(i.clone() as u16)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn to_u32(&self) -> Option<u32> {
        match self {
            Inum::I64(i) => {
                if 0 <= *i && *i <= std::u32::MAX as i64 {
                    Some(i.clone() as u32)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn to_u64(&self) -> Option<u64> {
        match self {
            Inum::I64(i) => {
                if 0 <= *i {
                    Some(i.clone() as u64)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[macro_export]
macro_rules! from_prims {
    ($to: tt) => {
        from_as!($to, i32, i64);
        from_as!($to, i16, i64);
        from_as!($to, i8, i64);

        from_as!($to, u32, i64);
        from_as!($to, u16, i64);
        from_as!($to, u8, i64);
    };
}

from_prims!(Inum);
