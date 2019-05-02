use rug::Integer;
use std::{
    convert::TryFrom,
    ops::{AddAssign, MulAssign},
};

use crate::{from_as, from_fn};

/// `Inum`s are either `i64` or `Integer`s (i.e., big integers).
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Inum {
    I64(i64),
    Int(Integer),
}

use Inum::*;

from_fn!(Inum, i64, I64);
from_fn!(Inum, u64, |u| {
    let i = u as i64;
    if i >= 0 {
        Inum::from(i)
    } else {
        Inum::Int(Integer::from(u))
    }
});

from_fn!(Inum, Integer, |i: Integer| {
    i.to_i64().map_or_else(|| Int(i), I64)
});

impl From<Inum> for Integer {
    fn from(i: Inum) -> Integer {
        match i {
            Inum::I64(i) => Integer::from(i), // Convert `i64` to `Integer`
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
    /// Consumes `self` to produce `Integer`.
    fn into_int(self) -> Integer {
        match self {
            Inum::I64(i) => Integer::from(i),
            Inum::Int(i) => i,
        }
    }

    /// Consumes `self` to produce `i64` if `self` is an `I64`,
    /// otherwise returns `None`.
    fn into_i64(self) -> Option<i64> {
        match self {
            Inum::I64(i) => Some(i),
            _ => None,
        }
    }

    /// Produces an `Integer`
    fn to_int(&self) -> Integer {
        match self {
            Inum::I64(i) => Integer::from(i.clone()),
            Inum::Int(i) => i.clone(),
        }
    }

    /// Produces an `i64` if `self` is an `I64`, otherwise returns `None`.
    fn to_i64(&self) -> Option<i64> {
        match self {
            Inum::I64(i) => Some(i.clone()),
            _ => None,
        }
    }

    /// Produces an `i32` if `self` is small enough, otherwise returns `None`.
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

    /// Produces an `i16` if `self` is small enough, otherwise returns `None`.
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

    /// Produces an `i8` if `self` is small enough, otherwise returns `None`.
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

    /// Produces a `u8` if `self` is small enough, otherwise returns `None`.
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

    /// Produces a `u8` if `self` is small enough, otherwise returns `None`.
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

    /// Produces a `u32` if `self` is small enough, otherwise returns `None`.
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

    /// Produces an `i64` if `self` is an `I64`, otherwise returns `None`.
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
    ($to:tt) => {
        from_as!($to, i32, i64);
        from_as!($to, i16, i64);
        from_as!($to, i8, i64);

        from_as!($to, u32, i64);
        from_as!($to, u16, i64);
        from_as!($to, u8, i64);
    };
}

from_prims!(Inum);
