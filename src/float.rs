//! # Floating point numbers
//!
//! KSON supports half, single, and double precision floating-point numbers.
//!
//! Our wrapper types currently do not support arithmetic.
//!
//! # Variants
//!
//! ## Half-Precision
//!
//! Half-precision floats can be a convenient way to store floating-point numbers more
//! compactly when the additional precision is not needed. However, there are a few
//! limitations to keep in mind.
//!
//! * Half-precision floats ([`f16`]) are not a primitive type in Rust, and so cannot be
//! created from directly from literals.
//!
//! * CPU level support for half-precision arithmetic does not exist on major platforms.
//! Arithmetic is performed by converting them into single-precision floats, doing the
//! arithmetic on the single-precision floats, and converting them back into
//! half-precision at the end.
//!
//! A few ways of creating half-precision floats:
//!
//! ```
//! use kson::prelude::*;
//!
//! // from a `str`
//! let half_str = f16::from_str("1").unwrap();
//!
//! // from an f32
//! let half_f32 = f16::from_f32(1.);
//!
//! // from an f64
//! let half_f64 = f16::from_f64(1.);
//!
//! // from 16-bits, note that `1.0` can be represented as `0x3C00`
//! let half_bits = f16::from_bits(0x3C00);
//!
//! // sum up the values
//! let sum = vec![half_str, half_f32, half_f64, half_bits]
//!     .into_iter()
//!     .map(f32::from)
//!     .fold(0f32, |acc, x| acc + x);
//!
//! // they should be about the same
//! assert!((sum - 4f32).abs() < 0.00000000001);
//! ```
//!
//! Half-precision floats can easily be converted to and from [`Kson`]:
//!
//! ```
//! use kson::prelude::*;
//!
//! // create the float
//! let half = f16::from_f32(1.);
//!
//! // convert to `Kson`
//! let ks = half.to_kson();
//!
//! // convert from `Kson`
//! let half2 = f16::from_kson(ks).unwrap();
//!
//! // they are the same
//! assert_eq!(half, half2);
//! ```
//!
//! Or, alternatively:
//!
//! ```
//! use kson::prelude::*;
//!
//! // create the float
//! let half = f16::from_f32(1.);
//!
//! // convert to `Kson`
//! let ks = Kson::from(half);
//!
//! // convert from `Kson`
//! let half2 = f16::try_from(ks).unwrap();
//!
//! // they are the same
//! assert_eq!(half, half2);
//! ```
//!
//! ## Single-Precision
//!
//! Single-precision floats behave as expected.
//!
//! They are easily converted to and from `Kson`:
//!
//! ```
//! use kson::prelude::*;
//!
//! // create the float
//! let single = 1f32;
//!
//! // convert to `Kson`
//! let ks = single.to_kson();
//!
//! // convert from `Kson`
//! let single2 = f32::from_kson(ks).unwrap();
//!
//! // they are the same
//! assert_eq!(single, single2);
//! ```
//!
//! Or, alternatively:
//!
//! ```
//! use kson::prelude::*;
//!
//! // create the float
//! let single = 1f32;
//!
//! // convert to `Kson`
//! let ks = Kson::from(single);
//!
//! // convert from `Kson`
//! let single2 = f32::try_from(ks).unwrap();
//!
//! // they are the same
//! assert_eq!(single, single2);
//! ```
//!
//! ## Double-Precision
//!
//! Double-precision floats behave as expected.
//!
//! They are easily converted to and from `Kson`:
//!  
//! ```
//! use kson::prelude::*;
//!
//! // create the float
//! let double = 1f64;
//!
//! // convert to `Kson`
//! let ks = double.to_kson();
//!
//! // convert from `Kson`
//! let double2 = f64::from_kson(ks).unwrap();
//!
//! // they are the same
//! assert_eq!(double, double2);
//! ```
//!
//! Or, alternatively:
//!
//! ```
//! use kson::prelude::*;
//!
//! // create the float
//! let double = 1f64;
//!
//! // convert to `Kson`
//! let ks = Kson::from(double);
//!
//! // convert from `Kson`
//! let double2 = f64::try_from(ks).unwrap();
//!
//! // they are the same
//! assert_eq!(double, double2);
//! ```

use half::f16;
use std::{cmp::Ordering, convert::TryFrom};

// TODO arithmetic
// TODO make from_kson work for specific precisions, when possible

#[derive(Eq, Copy, PartialEq, Ord, Clone, Hash, Debug)]
/// Floating point numbers. See also: [`float`](`crate::float`).
pub enum Float {
    /// Half precision float
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let half = Float::from(f16::from_f32(1f32));
    /// ```
    Half(u16),
    /// Single precision float
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let single = Float::from(1f32);
    /// ```
    Single(u32),
    /// Double precision float
    ///
    /// # Example
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let double = Float::from(1f64);
    /// ```
    Double(u64),
}

use Float::*;

impl PartialOrd for Float {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (f64::try_from(*self), f64::try_from(*other)) {
            (Ok(a), Ok(b)) => a.partial_cmp(&b),
            _ => None,
        }
    }
}

impl std::fmt::Display for Float {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Half(n) => write!(f, "{}", f16::from_bits(*n)),
            Single(n) => write!(f, "{}", f32::from_bits(*n)),
            Double(n) => write!(f, "{}", f64::from_bits(*n)),
        }
    }
}

// From impls
impl From<f16> for Float {
    fn from(f: f16) -> Self { Half(f.to_bits()) }
}

impl From<f32> for Float {
    fn from(f: f32) -> Self { Single(f.to_bits()) }
}

impl From<f64> for Float {
    fn from(f: f64) -> Self { Double(f.to_bits()) }
}

// TryFrom impls
impl TryFrom<Float> for f16 {
    type Error = Float;

    fn try_from(f: Float) -> Result<Self, Float> {
        match f {
            Half(n) => Ok(Self::from_bits(n)),
            _ => Err(f),
        }
    }
}

impl TryFrom<Float> for f32 {
    type Error = Float;

    fn try_from(f: Float) -> Result<Self, Float> {
        match f {
            Half(n) => Ok(f16::from_bits(n).to_f32()),
            Single(n) => Ok(Self::from_bits(n)),
            _ => Err(f),
        }
    }
}

impl TryFrom<Float> for f64 {
    type Error = Float;

    fn try_from(f: Float) -> Result<Self, Float> {
        match f {
            Half(n) => Ok(f16::from_bits(n).to_f64()),
            Single(n) => Ok(f32::from_bits(n) as f64),
            Double(n) => Ok(Self::from_bits(n)),
        }
    }
}
