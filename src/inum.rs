//! # Integers
//!
//! Integers behave more or less as expected.

use crate::{from_as, from_fn};
use num_bigint::{BigInt, ParseBigIntError};
use num_traits::*;
use std::{
    cmp::Ordering,
    convert::TryFrom,
    ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, Sub},
};

/// [`Inum`]s are either [`i64`]s or [`BigInt`]s (i.e., big integers).
#[derive(Eq, PartialEq, Ord, Clone, Hash, Debug)]
pub enum Inum {
    /// Small integer.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let small = Inum::from(1i32);
    /// ```
    I64(i64),
    /// Large integer.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let large = Inum::from(i64::min_value()) - Inum::from(1);
    ///
    /// println!("{}", large.clone());
    /// dbg!(i64::min_value());
    /// assert!(large < Inum::from(i64::min_value()));
    /// ```
    Int(BigInt),
}

impl std::fmt::Display for Inum {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            I64(i) => write!(f, "{}", i),
            Int(i) => write!(f, "{}", i),
        }
    }
}

impl PartialOrd for Inum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(match (self, other) {
            (Int(a), Int(b)) => a.cmp(b),
            (I64(a), I64(b)) => a.cmp(b),
            (Int(a), I64(b)) => a.cmp(&BigInt::from(*b)),
            (I64(a), Int(b)) => b.cmp(&BigInt::from(*a)),
        })
    }
}

use Inum::*;

// From implementations

// i64 -> Inum
from_fn!(Inum, i64, I64);

// u64 -> Inum
from_fn!(Inum, u64, |u| {
    let i = u as i64;
    if i >= 0 {
        I64(i)
    } else {
        Int(BigInt::from(u))
    }
});

// BigInt -> Inum
from_fn!(Inum, BigInt, |i: BigInt| {
    match i.to_i64() {
        Some(j) => I64(j),
        None => Int(i),
    }
});

// Inum -> BigInt
from_fn!(BigInt, Inum, |i: Inum| {
    match i {
        Inum::I64(i) => BigInt::from(i),
        Inum::Int(i) => i,
    }
});

// i128 -> Inum
from_fn!(Inum, i128, |i| {
    if i <= i64::max_value() as i128 && i >= i64::min_value() as i128 {
        I64(i as i64)
    } else {
        Int(BigInt::from(i))
    }
});

// u128 -> Inum
from_fn!(Inum, u128, |i| {
    if i <= i64::max_value() as u128 {
        I64(i as i64)
    } else {
        Int(BigInt::from(i))
    }
});

// usize -> Inum
from_fn!(Inum, usize, |i| { Inum::from(i as u64) });

// isize -> Inum
from_fn!(Inum, isize, |i| { Inum::from(i as i64) });

// TryFrom implementation
impl TryFrom<Inum> for i32 {
    type Error = Inum;

    fn try_from(i: Inum) -> Result<Self, Inum> {
        let n = i64::try_from(i);

        match n {
            Ok(v) => {
                if v >= i32::min_value() as i64 && v <= i32::max_value() as i64 {
                    Ok(v as i32)
                } else {
                    Err(Inum::from(v))
                }
            }
            Err(e) => Err(Int(e)),
        }
    }
}

impl TryFrom<Inum> for u32 {
    type Error = Inum;

    fn try_from(i: Inum) -> Result<Self, Inum> {
        let n = u64::try_from(i);

        match n {
            Ok(v) => {
                if v <= u32::max_value() as u64 {
                    Ok(v as u32)
                } else {
                    Err(Inum::from(v))
                }
            }
            Err(e) => Err(e),
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

impl TryFrom<Inum> for u128 {
    type Error = Inum;

    fn try_from(n: Inum) -> Result<Self, Inum> {
        match &n {
            Inum::I64(i) => {
                if *i >= 0 {
                    Ok(*i as u128)
                } else {
                    Err(n)
                }
            }
            Inum::Int(i) => {
                if let Some(u) = i.to_u128() {
                    Ok(u)
                } else {
                    Err(n)
                }
            }
        }
    }
}

impl TryFrom<Inum> for i128 {
    type Error = Inum;

    fn try_from(n: Inum) -> Result<Self, Inum> {
        match &n {
            Inum::I64(i) => Ok(*i as i128),
            Inum::Int(i) => {
                if let Some(u) = i.to_i128() {
                    Ok(u)
                } else {
                    Err(n)
                }
            }
        }
    }
}

impl TryFrom<Inum> for usize {
    type Error = Inum;

    #[cfg(target_pointer_width = "32")]
    fn try_from(n: Inum) -> Result<Self, Inum> { Ok(u32::try_from(n)? as usize) }

    #[cfg(target_pointer_width = "64")]
    fn try_from(n: Inum) -> Result<Self, Inum> { Ok(u64::try_from(n)? as usize) }
}

impl TryFrom<Inum> for isize {
    type Error = Inum;

    #[cfg(target_pointer_width = "32")]
    fn try_from(n: Inum) -> Result<Self, Inum> { Ok(u32::try_from(n)? as isize) }

    #[cfg(target_pointer_width = "64")]
    fn try_from(n: Inum) -> Result<Self, Inum> { Ok(u64::try_from(n)? as isize) }
}

// num_traits
impl Zero for Inum {
    fn zero() -> Self { I64(0) }

    fn is_zero(&self) -> bool {
        match self {
            I64(i) => i.is_zero(),
            Int(i) => {
                debug_assert!(!i.is_zero());
                false
            }
        }
    }
}

impl One for Inum {
    fn one() -> Self { I64(1) }

    fn is_one(&self) -> bool {
        match self {
            I64(i) => i.is_one(),
            Int(i) => {
                debug_assert!(!i.is_one());
                false
            }
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
                        match i.$op_checked(j) {
                            Some(k) => I64(k),
                            None => Int(BigInt::from(i).$op_suff(BigInt::from(j))),
                        }
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
                        match i.$op_checked() {
                            Some(j) => I64(j),
                            None => Int(BigInt::from(i).$op_suff()),
                        }
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

    fn from_str_radix(n_str: &str, radix: u32) -> Result<Self, ParseBigIntError> {
        match i64::from_str_radix(n_str, radix) {
            Err(_) => BigInt::from_str_radix(n_str, radix).map(Int),
            Ok(i) => Ok(I64(i)),
        }
    }
}

impl AddAssign<i64> for Inum {
    #[inline]
    fn add_assign(&mut self, other: i64) {
        let j = {
            match self {
                I64(i) => {
                    Ok(i.checked_add(other)
                        .map_or_else(|| Int(BigInt::from(*i) + other), I64))
                }
                Int(i) => {
                    *i += other;
                    Err(())
                }
            }
        };
        if let Ok(j) = j {
            *self = j;
        }
    }
}

impl MulAssign<i64> for Inum {
    #[inline]
    fn mul_assign(&mut self, other: i64) {
        let j = {
            match self {
                I64(i) => {
                    Ok(i.checked_mul(other)
                        .map_or_else(|| Int(BigInt::from(*i) * other), I64))
                }
                Int(i) => {
                    *i *= other;
                    Err(())
                }
            }
        };
        if let Ok(j) = j {
            *self = j;
        }
    }
}

#[macro_export]
/// Helper macro.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn crash_from_str_radix() {
        let n_str = "A";
        Inum::from_str_radix(n_str, 37).ok();
    }

    #[test]
    fn from_str_radix() {
        let num = "zzzzzzzzzzzzzz";
        match Inum::from_str_radix(num, 36).unwrap() {
            Int(_) => (),
            _ => panic!("Should be `Int`"),
        }

        let num = "z";
        match Inum::from_str_radix(num, 36).unwrap() {
            I64(_) => (),
            _ => panic!("Should be `I64`"),
        }
    }
}
