//! # Floating point numbers
//!
//! KSON supports half, single, and double precision floating point numbers.
//!
//! We intend to implement arithmetic for our wrapper types.
//!
//! # Variants
//!
//! ## Half-Precision
//!
//! Half-precision floats can be a convenient way to store floating point numbers more
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
//!
//! # Reading a specific precision from `Kson`
//!
//! You can specify as specific precision. This only works if the requested precision is
//! greater than or equal to the precision the value is encoded at (i.e., the conversion
//! can be performed losslessly).
//!
//! For example, this will work:
//!
//! ```
//! // use kson::prelude::*;
//!
//! // let ks = Kson::from(1f32);
//!
//! // // returns an f64
//! // let double = f64::from_kson(ks).unwrap();
//! ```
//!
//! but this will panic:
//!
//! ```should_panic
//! use kson::prelude::*;
//!
//! let ks = Kson::from(1f64);
//!
//! // returns an error, and we're cavalierly unwrapping it!
//! let double = f32::from_kson(ks).unwrap();
//! ```

use half::f16;
use std::convert::TryFrom;

// TODO arithmetic

#[derive(Eq, Copy, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
/// Floating point number variants
pub enum Float {
    /// Half precision float
    Half(u16),
    /// Single precision float
    Single(u32),
    /// Double precision float
    Double(u64),
}

use Float::*;

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
            Single(n) => Ok(Self::from_bits(n)),
            _ => Err(f),
        }
    }
}

impl TryFrom<Float> for f64 {
    type Error = Float;

    fn try_from(f: Float) -> Result<Self, Float> {
        match f {
            Double(n) => Ok(Self::from_bits(n)),
            _ => Err(f),
        }
    }
}
