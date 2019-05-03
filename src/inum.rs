use num_bigint::{BigInt, ParseBigIntError};
use num_traits::*;
use std::{
    convert::TryFrom,
    num::ParseIntError,
    ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, Sub},
};

use crate::{from_as, from_fn};

/// `Inum`s are either `i64` or `BigInt`s (i.e., big integers).
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Inum {
    I64(i64),
    Int(BigInt),
}

use Inum::*;

from_fn!(Inum, i64, I64);
from_fn!(Inum, u64, |u| {
    let i = u as i64;
    if i >= 0 {
        I64(i)
    } else {
        Int(BigInt::from(u))
    }
});

from_fn!(Inum, BigInt, |i: BigInt| {
    i.to_i64().map_or_else(|| Int(i), I64)
});

impl From<Inum> for BigInt {
    fn from(i: Inum) -> BigInt {
        match i {
            Inum::I64(i) => BigInt::from(i), // Convert `i64` to `BigInt`
            Inum::Int(i) => i,
        }
    }
}

impl TryFrom<Inum> for i64 {
    type Error = BigInt;

    fn try_from(i: Inum) -> Result<Self, BigInt> {
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

impl Zero for Inum {
    fn zero() -> Self { I64(0) }

    fn is_zero(&self) -> bool {
        match self {
            I64(0) => true,
            _ => false,
        }
    }
}

impl One for Inum {
    fn one() -> Self { I64(1) }

    fn is_one(&self) -> bool {
        match self {
            I64(1) => true,
            _ => false,
        }
    }
}

macro_rules! checked_impl {
    ($arg:ty, $op_name:tt, $op_suff:tt, $op_checked:tt) => {
        impl $op_name<$arg> for Inum {
            type Output = Inum;

            fn $op_suff(self, other: $arg) -> Inum {
                match (self, other) {
                    (I64(i), I64(j)) => {
                        i.$op_checked(j)
                            .map_or_else(|| Int(BigInt::from(i).$op_suff(BigInt::from(j))), I64)
                    }
                    (I64(i), Int(j)) => Inum::from(BigInt::from(i).$op_suff(j)),
                    (Int(i), I64(j)) => Inum::from(i.$op_suff(BigInt::from(j))),
                    (Int(i), Int(j)) => Inum::from(i.$op_suff(j)),
                }
            }
        }
    };
    ($op_name:tt, $op_suff:tt, $op_checked:tt) => {
        impl $op_name for Inum {
            type Output = Inum;

            fn $op_suff(self) -> Inum {
                match self {
                    I64(i) => {
                        i.$op_checked()
                            .map_or_else(|| Int(BigInt::from(i).$op_suff()), I64)
                    }
                    Int(i) => Inum::from(i.$op_suff()),
                }
            }
        }
    };
}

checked_impl!(Inum, Add, add, checked_add);
checked_impl!(Inum, Mul, mul, checked_mul);
checked_impl!(Inum, Sub, sub, checked_sub);
checked_impl!(Inum, Div, div, checked_div);
checked_impl!(Inum, Rem, rem, checked_rem);
checked_impl!(Neg, neg, checked_neg);

// TODO: make a working version of this
// checked_impl!(&Inum, Add, add, checked_add);
// checked_impl!(&Inum, Mul, mul, checked_mul);
// checked_impl!(&Inum, Sub, sub, checked_sub);
// checked_impl!(&Inum, Div, div, checked_div);
// checked_impl!(&Inum, Rem, rem, checked_rem);

// TODO: op_assign macro, num_assign instance

impl Num for Inum {
    type FromStrRadixErr = ParseBigIntError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, ParseBigIntError> {
        i64::from_str_radix(str, radix).map_or_else(
            |_| BigInt::from_str_radix(str, radix).map(Int),
            |i| Ok(I64(i)),
        )
    }
}

impl Inum {
    /// Consumes `self` to produce `BigInt`.
    fn into_int(self) -> BigInt {
        match self {
            Inum::I64(i) => BigInt::from(i),
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

    /// Produces an `BigInt`
    fn to_int(&self) -> BigInt {
        match self {
            Inum::I64(i) => BigInt::from(i.clone()),
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
