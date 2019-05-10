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
