#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

pub mod encoding;
pub mod rep;
pub mod util;

use byte_string::*;
use rug::Integer;
use std::collections::BTreeMap;
use std::ops::{AddAssign, MulAssign};
use std::sync::Arc;
use std::vec::Vec;

use rep::KsonRep;
use util::unwrap_or_clone;

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Inum {
    I64(i64),
    Int(Arc<Integer>),
}

impl From<i64> for Inum {
    fn from(i: i64) -> Inum {
        Inum::I64(i)
    }
}

impl From<u64> for Inum {
    fn from(u: u64) -> Inum {
        let i = u as i64;
        if i >= 0 {
            Inum::from(i)
        } else {
            Inum::Int(Arc::new(Integer::from(u)))
        }
    }
}

impl From<Integer> for Inum {
    fn from(i: Integer) -> Inum {
        if let Some(i) = i.to_i64() {
            Inum::I64(i)
        } else {
            Inum::Int(Arc::new(i))
        }
    }
}

impl From<Arc<Integer>> for Inum {
    fn from(i: Arc<Integer>) -> Inum {
        if let Some(i) = i.to_i64() {
            Inum::I64(i)
        } else {
            Inum::Int(i)
        }
    }
}

impl Inum {
    fn into_int(self) -> Integer {
        match self {
            Inum::I64(i) => Integer::from(i),
            Inum::Int(i) => unwrap_or_clone(i),
        }
    }

    fn into_int_arc(self) -> Arc<Integer> {
        match self {
            Inum::I64(i) => Arc::new(Integer::from(i)),
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
            Inum::Int(i) => i.as_ref().clone(),
        }
    }

    fn to_int_arc(&self) -> Arc<Integer> {
        match self {
            Inum::I64(i) => Arc::new(Integer::from(i.clone())),
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

/// KSON is a JSON-like serializable value format.  `Kson` represents a KSON value.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Hash, Debug)]
pub enum Kson {
    KSNull,
    KSBool(bool),
    KSInt(Inum),
    KSString(Arc<ByteString>),
    KSArray(Arc<Vec<Kson>>),
    KSMap(Arc<BTreeMap<ByteString, Kson>>), //TODO: floats
}

use Kson::*;

impl From<Integer> for Kson {
    fn from(i: Integer) -> Kson {
        Kson::KSInt(Inum::from(i))
    }
}

impl From<Arc<Integer>> for Kson {
    fn from(i: Arc<Integer>) -> Kson {
        Kson::KSInt(Inum::from(i))
    }
}

impl From<i64> for Kson {
    fn from(i: i64) -> Kson {
        Kson::KSInt(Inum::I64(i))
    }
}

impl From<u64> for Kson {
    fn from(u: u64) -> Kson {
        Kson::KSInt(Inum::from(u))
    }
}

impl Kson {
    pub fn is_null(&self) -> bool {
        *self == Kson::KSNull
    }

    pub fn into_bool(self) -> Option<bool> {
        match self {
            Kson::KSBool(b) => Some(b),
            _ => None,
        }
    }

    pub fn to_bool(&self) -> Option<bool> {
        match self {
            Kson::KSBool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn to_inum(&self) -> Option<&Inum> {
        match self {
            Kson::KSInt(i) => Some(i),
            _ => None,
        }
    }

    pub fn into_inum(self) -> Option<Inum> {
        match self {
            Kson::KSInt(i) => Some(i),
            _ => None,
        }
    }

    pub fn to_i64(&self) -> Option<i64> {
        self.to_inum()?.to_i64()
    }

    pub fn into_i64(self) -> Option<i64> {
        self.into_inum()?.into_i64()
    }

    pub fn to_int(&self) -> Option<Arc<Integer>> {
        Some(self.to_inum()?.to_int_arc())
    }

    pub fn into_int(self) -> Option<Integer> {
        Some(self.into_inum()?.into_int())
    }

    pub fn into_int_arc(self) -> Option<Arc<Integer>> {
        Some(self.into_inum()?.into_int_arc())
    }

    pub fn to_string(&self) -> Option<Arc<ByteString>> {
        match self {
            Kson::KSString(s) => Some(s.clone()),
            _ => None,
        }
    }

    pub fn into_string(self) -> Option<Arc<ByteString>> {
        match self {
            Kson::KSString(s) => Some(s),
            _ => None,
        }
    }

    pub fn to_array(&self) -> Option<Arc<Vec<Kson>>> {
        match self {
            Kson::KSArray(vec) => Some(vec.clone()),
            _ => None,
        }
    }

    pub fn into_array(self) -> Option<Arc<Vec<Kson>>> {
        match self {
            Kson::KSArray(vec) => Some(vec),
            _ => None,
        }
    }

    pub fn to_map(&self) -> Option<Arc<BTreeMap<ByteString, Kson>>> {
        match self {
            Kson::KSMap(obj) => Some(obj.clone()),
            _ => None,
        }
    }

    pub fn into_map(self) -> Option<Arc<BTreeMap<ByteString, Kson>>> {
        match self {
            Kson::KSMap(obj) => Some(obj),
            _ => None,
        }
    }

    pub fn to_rep<T: KsonRep>(&self) -> Option<T> {
        KsonRep::from_kson(self.clone())
    }

    pub fn into_rep<T: KsonRep>(self) -> Option<T> {
        KsonRep::from_kson(self)
    }

    pub fn into_rep_arc<T: KsonRep>(self) -> Option<Arc<T>> {
        KsonRep::from_kson_arc(self)
    }

    /// `k.size()` returns an upper bound on number of bytes `encode_full(k)` would require
    pub fn size(&self) -> usize {
        fn leb_size(i: &Integer) -> usize {
            i.significant_digits::<u8>() * 8 / 7 + 1
        }
        fn str_size(bs: &ByteString) -> usize {
            let len_str = bs.len();
            len_str + leb_size(&Integer::from(len_str))
        }
        match self {
            Kson::KSString(b) => 1 + str_size(b),
            Kson::KSInt(i) => 1 + leb_size(&i.to_int()),
            Kson::KSArray(v) => v
                .iter()
                .fold(1 + leb_size(&Integer::from(v.len())), |acc, v| {
                    acc + v.size()
                }),
            Kson::KSMap(m) => m
                .iter()
                .fold(1 + leb_size(&Integer::from(m.len())), |acc, (k, v)| {
                    acc + str_size(k) + v.size()
                }),
            _ => 1,
        }
    }
}
