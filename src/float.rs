use crate::inum::Inum;
use half::f16;
use std::convert::TryFrom;

// TODO arithmetic

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
/// Arbitrary precision float, represented as a base and an exponent
pub struct LargeFloat(Inum, Inum);

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
/// Floating point number variants
pub enum Float {
    /// Half precision float
    Half(u16),
    /// Single precision float
    Single(u32),
    /// Double precision float
    Double(u64),
    /// Arbitrary precision float
    Big(LargeFloat),
}

use Float::*;

impl LargeFloat {
    /// Creates a new `LargeFloat`
    ///
    /// # Arguments
    ///
    /// * `base: Inum` - The base of the float.
    /// * `exp: Inum` - The exponent of the float.
    ///
    /// # Examples
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// let large = LargeFloat::new(Inum::from(2), Inum::from(89));
    /// ```
    pub fn new(base: Inum, exp: Inum) -> Self { LargeFloat(base, exp) }

    /// Gets the base
    ///
    /// # Example
    /// ```
    /// use kson::prelude::*;
    ///
    /// let large = LargeFloat::new(Inum::from(2), Inum::from(89));
    ///
    /// assert_eq!(large.base(), Inum::from(2));
    /// ```
    pub fn base(&self) -> Inum { self.0.clone() }

    /// Gets the exponent
    ///
    /// # Example
    /// ```
    /// use kson::prelude::*;
    ///
    /// let large = LargeFloat::new(Inum::from(2), Inum::from(89));
    ///
    /// assert_eq!(large.exp(), Inum::from(89));
    /// ```
    pub fn exp(&self) -> Inum { self.1.clone() }

    /// Gets a reference to the base
    ///
    /// # Example
    /// ```
    /// use kson::prelude::*;
    ///
    /// let large = LargeFloat::new(Inum::from(2), Inum::from(89));
    ///
    /// assert_eq!(large.base_ref(), &Inum::from(2));
    /// ```
    pub fn base_ref(&self) -> &Inum { &self.0 }

    /// Gets a reference to the exponent
    ///
    /// # Example
    /// ```
    /// use kson::prelude::*;
    ///
    /// let large = LargeFloat::new(Inum::from(2), Inum::from(30));
    ///
    /// assert_eq!(large.base(), Inum::from(1));
    /// ```
    pub fn exp_ref(&self) -> &Inum { &self.1 }

    /// Consumes the value, returning a tuple containing the base and exponent.
    ///
    /// # Example
    /// ```
    /// use kson::prelude::*;
    ///
    /// let large = LargeFloat::new(Inum::from(1), Inum::from(30));
    ///
    /// assert_eq!(large.into_pair(), Inum::from(1));
    /// ```
    pub fn into_pair(self) -> (Inum, Inum) { (self.0, self.1) }

    /// Returns a tuple of references to the base and exponent.
    ///
    /// # Example
    /// ```
    /// use kson::prelude::*;
    ///
    /// let large = LargeFloat::new(Inum::from(1), Inum::from(30));
    ///
    /// assert_eq!(large.base(), Inum::from(1));
    /// ```
    pub fn to_pair(&self) -> (&Inum, &Inum) { (&self.0, &self.1) }
}

impl From<f16> for Float {
    fn from(f: f16) -> Self { Half(f.to_bits()) }
}

impl From<f32> for Float {
    fn from(f: f32) -> Self { Single(f.to_bits()) }
}

impl From<f64> for Float {
    fn from(f: f64) -> Self { Double(f.to_bits()) }
}

impl From<LargeFloat> for Float {
    fn from(f: LargeFloat) -> Self { Big(f) }
}

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

impl TryFrom<Float> for LargeFloat {
    type Error = Float;

    fn try_from(f: Float) -> Result<Self, Float> {
        match f {
            Big(f) => Ok(f),
            _ => Err(f),
        }
    }
}
