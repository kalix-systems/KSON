use super::*;
use byteorder::*;
use bytes::Bytes;
use failure::*;
use half::f16;
use num_bigint::{BigInt, BigUint, Sign};
use std::{
    collections::HashMap,
    convert::TryFrom,
    net::{Ipv4Addr, SocketAddrV4},
    ops::{Deref, DerefMut},
};
use KTag::*;

/// KSON types.
#[derive(Copy, Clone, Debug)]
pub enum KType {
    Null,
    Bool,
    Int,
    Float,
    Bytes,
    Array,
    Map,
}

/// KSON tags.
#[derive(Copy, Clone, Debug)]
pub enum KTag {
    /// Constant tag.
    KCon(u8),
    /// Integer tag.
    KInt(IntSize, u8),
    /// Bytestring tag.
    KByt(Size, u8),
    /// Array tag.
    KArr(Size, u8),
    /// Map tag.
    KMap(Size, u8),
    /// Float tag.
    KFloat(u8),
}

impl From<KTag> for KType {
    fn from(tag: KTag) -> Self {
        use KTag::*;
        use KType::*;
        match tag {
            KCon(u) => unimplemented!(),
            KInt(..) => Int,
            KByt(..) => Bytes,
            KFloat(..) => Float,
            KArr(..) => Array,
            KMap(..) => Map,
        }
    }
}

pub fn check_entry<T: De>(key: Bytes, value: T, field: &str) -> Result<T, Error> {
    if &key == field.as_bytes() {
        Ok(value)
    } else {
        bail!(
            "Expected field `{:?}`, found a field named `{:?}`",
            field,
            key,
        )
    }
}

pub struct KsonBytes(Bytes);

impl Deref for KsonBytes {
    type Target = Bytes;
    fn deref(&self) -> &Bytes {
        &self.0
    }
}

impl DerefMut for KsonBytes {
    fn deref_mut(&mut self) -> &mut Bytes {
        &mut self.0
    }
}

impl From<Bytes> for KsonBytes {
    fn from(b: Bytes) -> Self {
        KsonBytes(b)
    }
}

impl From<Vec<u8>> for KsonBytes {
    fn from(v: Vec<u8>) -> Self {
        KsonBytes(Bytes::from(v))
    }
}

impl<'a> From<&'a [u8]> for KsonBytes {
    fn from(s: &'a [u8]) -> Self {
        KsonBytes(Bytes::from(s))
    }
}

macro_rules! size_and_len {
    ($ctor:expr, $mask:expr, $byte:ident) => {{
        let size = if $byte & BIG_BIT == BIG_BIT {
            Size::Big
        } else {
            Size::Small
        };
        let len = $byte & $mask;
        Ok($ctor(size, len))
    }};
    ($ctor:expr, $byte:ident) => {
        size_and_len!($ctor, MASK_LEN_BITS, $byte)
    };
}

impl KsonBytes {
    #[inline]
    fn take_byte(&mut self) -> Result<u8, Error> {
        let byte = self.peek_byte()?;
        self.advance(1);
        Ok(byte)
    }

    #[inline]
    fn peek_byte(&self) -> Result<u8, Error> {
        if self.len() >= 1 {
            let byte = self[0];
            Ok(byte)
        } else {
            Err(format_err!("Buffer was empty, couldn't get byte"))
        }
    }

    #[inline]
    fn read_many(&mut self, len: usize) -> Result<Bytes, Error> {
        if self.len() >= len {
            Ok(self.split_to(len))
        } else {
            Err(format_err!(
                "tried to read {} bytes from buffer of size {}",
                len,
                self.len()
            ))
        }
    }

    #[inline]
    fn read_u16(&mut self) -> Result<u16, Error> {
        let bs = self.read_many(2)?;
        Ok(Endian::read_u16(&bs))
    }

    #[inline]
    fn read_u32(&mut self) -> Result<u32, Error> {
        let bs = self.read_many(4)?;
        Ok(Endian::read_u32(&bs))
    }

    #[inline]
    fn read_u64(&mut self) -> Result<u64, Error> {
        let bs = self.read_many(8)?;
        Ok(Endian::read_u64(&bs))
    }

    #[inline]
    fn read_u128(&mut self) -> Result<u128, Error> {
        let bs = self.read_many(16)?;
        Ok(Endian::read_u128(&bs))
    }

    #[inline]
    fn read_varu64(&mut self, len: usize) -> Result<u64, Error> {
        let bs = self.read_many(len)?;
        Ok(Endian::read_uint(&bs, len))
    }

    #[inline]
    fn read_varu128(&mut self, len: usize) -> Result<u128, Error> {
        let bs = self.read_many(len)?;
        Ok(Endian::read_uint128(&bs, len))
    }

    /// Try to read length from buffer.
    #[inline]
    fn read_len(&mut self, size: Size, len: u8) -> Result<usize, Error> {
        match size {
            Size::Big => Ok(self.read_varu64(len as usize + 1)? as usize + BIGCOL_MIN_LEN as usize),
            Size::Small => Ok(len as usize),
        }
    }

    #[inline]
    fn read_tag(&mut self) -> Result<KTag, Error> {
        use KTag::*;
        let byte = self.take_byte()?;
        match byte & MASK_TYPE {
            TYPE_CON => Ok(KCon(byte & MASK_META)),
            TYPE_INT => {
                let size = if byte & BIG_BIT == BIG_BIT {
                    Size::Big
                } else {
                    Size::Small
                };

                let sign = if byte & INT_POSITIVE == INT_POSITIVE {
                    KSign::Pos
                } else {
                    KSign::Neg
                };

                let len = byte & MASK_INT_LEN_BITS;
                debug_assert!(len <= MASK_INT_LEN_BITS);
                Ok(KInt(size, sign, len + 1))
            }
            TYPE_BYT => size_and_len!(KByt, byte),
            TYPE_ARR => size_and_len!(KArr, byte),
            TYPE_MAP => size_and_len!(KMap, byte),
            TYPE_FLOAT => Ok(KFloat(byte)),
            unknown => bail!("found unknown tag: {:b}", unknown),
        }
    }
}

/// A sequence of values that can be deserialized.
pub trait DeSeq {
    /// Reads the state of the sequence, returning a tuple of the sequence state and the
    /// length of the sequence.
    ///
    /// # Errors
    ///
    /// This will return an error if the next item in the stream is not an array
    fn start_seq(&mut self) -> Result<usize, Error>;

    /// Returns the next value in the sequence as `T`.
    ///
    /// # Errors
    ///
    /// This will return an error if the next element of the sequence cannot be converted
    /// to `T`.
    fn take_next<T: De>(&mut self) -> Result<T, Error>;
}

/// A map deserializer.
pub trait DeMap {
    /// Reads the state of the deserializer, returning a tuple of the state and the number
    /// of entries in the map.
    ///
    /// # Errors
    ///
    /// This will return an error if the next item in the stream is not an array
    fn start_map(&mut self) -> Result<usize, Error>;

    /// Reads the next key from the deserializer as [`Bytes`].
    ///
    /// # Errors
    ///
    /// This will return an error unless the next item in the stream is a bytestring.
    fn take_key(&mut self) -> Result<Bytes, Error>;

    /// Reads the next value from the serializer as `T`.
    ///
    /// # Errors
    ///
    /// This will return an error if the deserializer for `T` fails.
    fn take_val<T: De>(&mut self) -> Result<T, Error>;
}

/// Values that can be deserialized from.
pub trait Deserializer: DeSeq + DeMap {
    /// Read a tag byte as a [`KTag`].
    fn peek_type(&self) -> Result<KType, Error>;

    /// Read a  [`Kson::Null`]. Returns `Ok(())` if successful, otherwise returns an
    /// error.
    fn read_null(&mut self) -> Result<(), Error>;

    /// Read a [`bool`].
    fn read_bool(&mut self) -> Result<bool, Error>;

    /// Read an [`i8`]
    fn read_i8(&mut self) -> Result<i8, Error>;

    /// Read an [`i16`]
    fn read_i16(&mut self) -> Result<i16, Error>;

    /// Read an [`i32`]
    fn read_i32(&mut self) -> Result<i32, Error>;

    /// Read an [`i64`]
    fn read_i64(&mut self) -> Result<i64, Error>;

    /// Read an [`i128`]
    fn read_i128(&mut self) -> Result<i128, Error>;

    /// Read an [`u8`]
    fn read_u8(&mut self) -> Result<u8, Error> {
        let i = self.read_i16()?;
        if 0 <= i && i < u8::max_value() as i16 {
            Ok(i as u8)
        } else {
            bail!("tried to read u8 but value {} was too large", i)
        }
    }

    /// Read an [`u16`]
    fn read_u16(&mut self) -> Result<u16, Error> {
        let i = self.read_i32()?;
        if 0 <= i && i < u16::max_value() as i32 {
            Ok(i as u16)
        } else {
            bail!("tried to read u8 but value {} was too large", i)
        }
    }

    /// Read an [`u32`]
    fn read_u32(&mut self) -> Result<u32, Error> {
        unimplemented!()
    }

    /// Read an [`u64`]
    fn read_u64(&mut self) -> Result<u64, Error> {
        unimplemented!()
    }

    /// Read an [`u128`]
    fn read_u128(&mut self) -> Result<u128, Error> {
        unimplemented!()
    }

    /// Read a [`BigUint`].
    fn read_biguint(&mut self) -> Result<BigUint, Error> {
        unimplemented!()
    }

    /// Read a [`BigInt`].
    fn read_bigint(&mut self) -> Result<BigInt, Error>;

    /// Read an [`f16`].
    fn read_f16(&mut self) -> Result<f16, Error>;

    /// Read an [`f32`].
    fn read_f32(&mut self) -> Result<f32, Error>;

    /// Read an [`f64`].
    fn read_f64(&mut self) -> Result<f64, Error>;

    /// Read a [`Bytes`].
    fn read_bytes(&mut self) -> Result<Bytes, Error>;
}

impl Deserializer for KsonBytes {
    #[inline]
    fn peek_type(&self) -> Result<KType, Error> {
        use KType::*;
        let byte = self.peek_byte()?;
        match byte & MASK_TYPE {
            TYPE_INT => Ok(Int),
            TYPE_BYT => Ok(Bytes),
            TYPE_FLOAT => Ok(Float),
            TYPE_ARR => Ok(Array),
            TYPE_MAP => Ok(Map),
            TYPE_CON => match byte {
                CON_NULL => Ok(Null),
                CON_TRUE => Ok(Bool),
                CON_FALSE => Ok(Bool),
                unknown => bail!("found unknown constant: {:b}", unknown),
            },
            unknown => bail!("found unknown tag: {:b}", unknown),
        }
    }

    #[inline]
    fn read_null(&mut self) -> Result<(), Error> {
        match self.read_tag()? {
            KCon(CON_NULL) => Ok(()),
            _ => bail!("bad tag when reading null"),
        }
    }

    #[inline]
    fn read_bool(&mut self) -> Result<bool, Error> {
        match self.read_tag()? {
            KCon(CON_TRUE) => Ok(true),
            KCon(CON_FALSE) => Ok(false),
            _ => bail!("bad tag when reading bool"),
        }
    }

    #[inline]
    fn read_i8(&mut self) -> Result<i8, Error> {
        if let Some(KInt(Size::Small, 
        unimplemented!()
    }

    fn read_i16(&mut self) -> Result<i16, Error> {
        unimplemented!()
    }

    fn read_i32(&mut self) -> Result<i32, Error> {
        unimplemented!()
    }

    fn read_i64(&mut self) -> Result<i64, Error> {
        unimplemented!()
    }

    fn read_i128(&mut self) -> Result<i128, Error> {
        unimplemented!()
    }

    fn read_bigint(&mut self) -> Result<BigInt, Error> {
        unimplemented!()
    }

    fn read_f16(&mut self) -> Result<f16, Error> {
        unimplemented!()
    }

    fn read_f32(&mut self) -> Result<f32, Error> {
        unimplemented!()
    }

    fn read_f64(&mut self) -> Result<f64, Error> {
        unimplemented!()
    }

    #[inline]
    fn read_bytes(&mut self) -> Result<Bytes, Error> {
        match self.read_tag()? {
            KByt(size, len) => {
                let len = self.read_len(size, len)?;
                self.read_many(len)
            }
            _ => bail!("bad tag"),
        }
    }

    //     #[inline]
    //     fn read_i64(&mut self) -> Result<i64, Error> {
    //         match self.read_tag()? {
    //             KInt(Size::Small, sign, len) if len <= 8 => {
    //                 let val = self.read_uint(len)?;
    //                 if val <= i64::max_value() as u64 {
    //                     match sign {
    //                         KSign::Pos => Ok(val as i64),
    //                         KSign::Neg => Ok(-(val as i64) - 1),
    //                     }
    //                 } else {
    //                     bail!("int too large to be i64")
    //                 }
    //             }
    //             _ => bail!("Bad tag when reading i64"),
    //         }
    //     }

    //     #[inline]
    //     fn read_bigint(&mut self) -> Result<BigInt, Error> {
    //         match self.read_tag()? {
    //             KInt(size, sign, len) => {
    //                 debug_assert!(len <= 8 || size == Size::Small);
    //                 let val = self.read_uint(len)?;

    //                 let mut i = match size {
    //                     Size::Small => BigInt::from(val),
    //                     Size::Big => {
    //                         let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
    //                         BigInt::from_bytes_le(Sign::Plus, &digs)
    //                     }
    //                 };

    //                 if sign == KSign::Neg {
    //                     i *= -1;
    //                     i += -1;
    //                 }

    //                 Ok(i)
    //             }
    //             _ => bail!("Bad tag when reading BigInt"),
    //         }
    //     }

    //     #[inline]
    //     fn read_inum(&mut self) -> Result<Inum, Error> {
    //         match self.read_tag()? {
    //             KInt(size, sign, len) => {
    //                 debug_assert!(len <= 8 || size == Size::Small);

    //                 let val = self.read_uint(len)?;

    //                 let mut i = match size {
    //                     Size::Small => Inum::from(val),
    //                     Size::Big => {
    //                         let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
    //                         Inum::from(BigInt::from_bytes_le(Sign::Plus, &digs))
    //                     }
    //                 };

    //                 if sign == KSign::Neg {
    //                     i *= -1;
    //                     i += -1;
    //                 }
    //                 Ok(i)
    //             }
    //             _ => bail!("bad tag when reading inum"),
    //         }
    //     }

    //     #[inline]
    //     fn read_f16(&mut self) -> Result<f16, Error> {
    //         match self.read_tag()? {
    //             KFloat(HALF) => self.read_u16().map(f16::from_bits),
    //             _ => bail!("bad tag when reading half-precision float"),
    //         }
    //     }

    //     #[inline]
    //     fn read_f32(&mut self) -> Result<f32, Error> {
    //         match self.read_tag()? {
    //             KFloat(SINGLE) => self.read_u32().map(f32::from_bits),
    //             _ => bail!("bad tag when reading single-precision float"),
    //         }
    //     }

    //     #[inline]
    //     fn read_f64(&mut self) -> Result<f64, Error> {
    //         match self.read_tag()? {
    //             KFloat(DOUBLE) => self.read_u64().map(f64::from_bits),
    //             _ => bail!("bad tag when reading double-precision float"),
    //         }
    //     }
}

impl DeSeq for KsonBytes {
    fn start_seq(&mut self) -> Result<usize, Error> {
        match self.read_tag()? {
            KArr(size, len) => self.read_len(size, len),
            t => bail!("bad tag when starting sequence, tag was {:?}", t),
        }
    }

    fn take_next<T: De>(&mut self) -> Result<T, Error> {
        T::de(self)
    }
}

impl DeMap for KsonBytes {
    fn start_map(&mut self) -> Result<usize, Error> {
        match self.read_tag()? {
            KMap(size, len) => self.read_len(size, len),
            t => bail!("bad tag when starting map, tag was {:?}", t),
        }
    }

    fn take_key(&mut self) -> Result<Bytes, Error> {
        self.read_bytes()
    }

    fn take_val<T: De>(&mut self) -> Result<T, Error> {
        T::de(self)
    }
}

/// Values that can be deserialized.
pub trait De: Sized {
    /// Read a value of type `Self` from a [`Deserializer`].
    ///
    /// # Arguments
    ///
    /// * `d` - The [`Deserializer`] to be read from.
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error>;
}

//impl<T: De> De for Vec<T> {
//    #[inline]
//    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//        let (mut s, len) = d.read()?;
//        let mut out = Vec::with_capacity(len);
//        for _ in 0..len {
//            out.push(d.take(&mut s)?);
//        }
//        Ok(out)
//    }
//}

//impl<T: De, S: ::std::hash::BuildHasher + Default> De for HashMap<Bytes, T, S> {
//    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//        let (mut s, len) = d.take_map()?;
//        let mut out = HashMap::with_capacity_and_hasher(len, Default::default());
//        for _ in 0..len {
//            out.insert(d.take_key(&mut s)?, d.take_val(&mut s)?);
//        }
//        Ok(out)
//    }
//}

//// Implementations for primitive types
//macro_rules! easy_de {
//    ($typ:ty, $read:tt) => {
//        impl De for $typ {
//            #[inline]
//            fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//                match Self::try_from(d.$read()?) {
//                    Err(_) => bail!("Value too big to be `{}`", stringify!(Self)),
//                    Ok(v) => Ok(v),
//                }
//            }
//        }
//    };
//}

//macro_rules! trivial_de {
//    ($typ:ty, $read:tt) => {
//        impl De for $typ {
//            #[inline]
//            fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//                d.$read()
//            }
//        }
//    };
//}

//// Inum

//// BigInt
//trivial_de!(BigInt, read_bigint);

//// sizes
//easy_de!(isize, read_i64);

//// 8-bit ints
//easy_de!(u8, read_i64);
//easy_de!(i8, read_i64);

//// 16-bit ints
//easy_de!(u16, read_i64);
//easy_de!(i16, read_i64);

//// 32-bit ints
//easy_de!(u32, read_i64);
//easy_de!(i32, read_i64);

//// 64-bit ints
//easy_de!(u64, read_inum);
//trivial_de!(i64, read_i64);

//// 128-bit ints
//easy_de!(u128, read_inum);
//easy_de!(i128, read_inum);

//// Floats
//trivial_de!(Float, read_float);
//trivial_de!(f16, read_f16);
//trivial_de!(f32, read_f32);
//trivial_de!(f64, read_f64);

//// Misc

//// unit/nil
//trivial_de!((), read_null);

//// boolean
//trivial_de!(bool, read_bool);

//// bytes
//trivial_de!(Bytes, read_bytes);

//impl De for String {
//    #[inline]
//    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//        let bs = d.read_bytes()?;

//        match String::from_utf8(bs.to_vec()) {
//            Ok(s) => Ok(s),
//            Err(_) => {
//                // pre-allocate
//                let mut chars = Vec::with_capacity(bs.len() / 2 + 1);

//                // bytestring into buffer
//                let buf = &mut bs.into_buf();

//                // get u16s
//                for _ in 0..buf.remaining() {
//                    chars.push(buf.get_u16_le());
//                }

//                // try to read
//                match String::from_utf16(&chars) {
//                    Ok(s) => Ok(s),
//                    Err(_) => bail!("Bytestring was neither valid utf-8 nor utf-16",),
//                }
//            }
//        }
//    }
//}

//impl De for char {
//    #[inline]
//    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//        let mut buf = d.read_bytes()?.into_buf();

//        let rem = buf.remaining();

//        let c = if rem == 4 {
//            buf.get_u32_le()
//        } else {
//            bail!("Characters are expected to be four bytes, found {}", rem)
//        };

//        match std::char::from_u32(c) {
//            None => bail!("Bytestring is not a valid character"),
//            Some(ch) => Ok(ch),
//        }
//    }
//}

//// impl<T: De> De for Option<T> {
////     fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
////         match d.read_kson()? {
////             Null => Ok(None),
////             Array(v) => {
////                 let mut iter = v.into_iter();
////                 let val = &mut match iter.next() {
////                     None => bail!("Value is not an `Option`"),
////                     Some(v) => KContainer::new_place(v),
////                 };

////                 if iter.next().is_none() {
////                     Ok(Some(T::de(val)?))
////                 } else {
////                     bail!("Value is not an `Option`")
////                 }
////             }
////             _ => bail!("Value is not an `Option`"),
////         }
////     }
//// }

//impl De for Ipv4Addr {
//    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//        let bs = Bytes::de(d)?;

//        if bs.len() == 4 {
//            Ok(Self::new(bs[0], bs[1], bs[2], bs[3]))
//        } else {
//            bail!(
//                "Value is {} bytes long, an `Ipv4Addr` should be 4 bytes long",
//                bs.len(),
//            )
//        }
//    }
//}

//impl De for SocketAddrV4 {
//    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//        let (ip, port) = <(Ipv4Addr, u16)>::de(d)?;
//        Ok(Self::new(ip, port))
//    }
//}

//macro_rules! tuple_de {
//    ($len:expr, $($typ:ident),*) => {
//        impl<$($typ: De),*> De for ($($typ,)*) {
//            fn de<Des: Deserializer>(d: &mut Des) -> Result<Self, Error> {
//                let exp_len = $len;
//                let (mut iter, len) = d.read()?;

//                if len == exp_len {
//                    let tuple = ($(d.take::<$typ>(&mut iter)?,)*);
//                    Ok(tuple)

//                } else {
//                    bail!("Tuple has wrong number of fields; expected {}, found {}",
//                          exp_len,
//                          len
//                    )
//                }
//            }
//        }
//    }
//}

//tuple_de!(1, A);
//tuple_de!(2, A, B);
//tuple_de!(3, A, B, C);
//tuple_de!(4, A, B, C, D);
//tuple_de!(5, A, B, C, D, E);
//tuple_de!(6, A, B, C, D, E, F);
//tuple_de!(7, A, B, C, D, E, F, G);
//tuple_de!(8, A, B, C, D, E, F, G, H);
//tuple_de!(9, A, B, C, D, E, F, G, H, I);
//tuple_de!(10, A, B, C, D, E, F, G, H, I, J);
//tuple_de!(11, A, B, C, D, E, F, G, H, I, J, K);
//tuple_de!(12, A, B, C, D, E, F, G, H, I, J, K, L);
