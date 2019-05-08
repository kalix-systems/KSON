use crate::inum::Inum;
use half::f16;
use std::convert::TryFrom;

// TODO arithmetic

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub struct LargeFloat(Inum, Inum);

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Float {
    Half(u16),
    Single(u32),
    Double(u64),
    Big(LargeFloat),
}

use Float::*;

impl LargeFloat {
    pub fn new(base: Inum, exp: Inum) -> LargeFloat { LargeFloat(base, exp) }

    pub fn base(&self) -> Inum { self.0.clone() }

    pub fn exp(&self) -> Inum { self.1.clone() }

    pub fn base_ref(&self) -> &Inum { &self.0 }

    pub fn exp_ref(&self) -> &Inum { &self.1 }

    pub fn into_pair(self) -> (Inum, Inum) { (self.0, self.1) }

    pub fn to_pair(&self) -> (&Inum, &Inum) { (&self.0, &self.1) }
}

impl From<f16> for Float {
    fn from(f: f16) -> Float { Half(f.to_bits()) }
}

impl From<f32> for Float {
    fn from(f: f32) -> Float { Single(f.to_bits()) }
}

impl From<f64> for Float {
    fn from(f: f64) -> Float { Double(f.to_bits()) }
}

impl From<LargeFloat> for Float {
    fn from(f: LargeFloat) -> Float { Big(f) }
}

impl TryFrom<Float> for f16 {
    type Error = Float;

    fn try_from(f: Float) -> Result<Self, Float> {
        match f {
            Half(n) => Ok(f16::from_bits(n)),
            _ => Err(f),
        }
    }
}

impl TryFrom<Float> for f32 {
    type Error = Float;

    fn try_from(f: Float) -> Result<Self, Float> {
        match f {
            Single(n) => Ok(f32::from_bits(n)),
            _ => Err(f),
        }
    }
}

impl TryFrom<Float> for f64 {
    type Error = Float;

    fn try_from(f: Float) -> Result<Self, Float> {
        match f {
            Double(n) => Ok(f64::from_bits(n)),
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
