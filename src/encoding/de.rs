use super::*;
use crate::{
    float::Float::{self, *},
    prelude::*,
};
use failure::*;
use half::f16;
use num_bigint::{BigInt, Sign};
use std::{
    collections::HashMap,
    convert::TryFrom,
    net::{Ipv4Addr, SocketAddrV4},
};
use KTag::*;

/// KSON tags.
#[derive(Copy, Clone, Debug)]
pub enum KTag {
    /// Constant tag.
    KCon(u8),
    /// Integer tag.
    KInt(Size, KSign, u8),
    /// Bytestring tag.
    KByt(Size, u8),
    /// Array tag.
    KArr(Size, u8),
    /// Map tag.
    KMap(Size, u8),
    /// Float tag.
    KFloat(u8),
}

pub fn check_entry<T: De>(key: Bytes, value: T, field: &str) -> Result<T, Error> {
    if key == Bytes::from_buf(field) {
        Ok(value)
    } else {
        bail!(
            "Expected field `{:?}`, found a field named `{:?}`",
            field,
            key,
        )
    }
}

// TODO: error-chain based handling
/// A sequence of bytes with read methods.
pub trait DeserializerBytes {
    /// Read a tag byte as a [`KTag`].
    fn read_tag(&mut self) -> Result<KTag, Error>;

    /// Read a specified number of bytes as a `Vec<u8>`.
    ///
    /// # Arguments
    ///
    /// * `len: usize` - The number of bytes to be read.
    fn read_many(&mut self, len: usize) -> Result<Vec<u8>, Error>;

    /// Read a single byte.
    fn read_u8(&mut self) -> Result<u8, Error>;

    /// Read two bytes as a [`u16`].
    fn read_u16(&mut self) -> Result<u16, Error>;

    /// Read four bytes as a [`u32`].
    fn read_u32(&mut self) -> Result<u32, Error>;

    /// Read eight bytes as a [`u64`].
    fn read_u64(&mut self) -> Result<u64, Error>;

    /// Reads an unsigned n-bytes integer.
    ///
    /// # Arguments
    ///
    /// * `len: u8` - The number of bytes to be read, where `1 <= len <= 8`.
    fn read_uint(&mut self, len: u8) -> Result<u64, Error>;
}

/// A sequence of values that can be deserialized.
pub trait DeSeq {
    /// The state of the sequence. This is idiomatically [`()`] if the sequence doesn't
    /// need to track intermediate states.
    type State: Sized;

    /// Reads the state of the sequence, returning a tuple of the sequence state and the
    /// length of the sequence.
    fn read(&mut self) -> Result<(Self::State, usize), Error>;

    /// Returns the next value in the sequence as `T`.
    ///
    /// # Arguments
    ///
    /// * `s: &mut Self::State` - A mutable reference to the current state of the
    ///   sequence.
    ///
    /// # Errors
    ///
    /// This will return an error if the next element of the sequence cannot be converted
    /// to `T`.
    fn take<T: De>(&mut self, s: &mut Self::State) -> Result<T, Error>;
}

/// A map deserializer.
pub trait DeMap {
    /// The state of the map deserializer. This is idiomatically [`()`] if the
    /// deserializer doesn't need to track intermediate states.
    type State: Sized;

    /// Reads the state of the deserializer, returning a tuple of the state and the number
    /// of entries in the map.
    fn take_map(&mut self) -> Result<(Self::State, usize), Error>;

    /// Reads the next key from the deserializer as [`Bytes`].
    ///
    /// # Arguments
    ///
    /// * `s: &mut Self::State` - A mutable reference to the current state of the
    ///   deserializer.
    ///
    /// # Errors
    ///
    /// This will return an error if no keys are remaining.
    fn take_key(&mut self, s: &mut Self::State) -> Result<Bytes, Error>;

    /// Reads the next value from the serializer as `T`.
    ///
    /// # Errors
    ///
    /// This will return an error if no values are remaining, or the associated key has
    /// not yet been read.
    fn take_val<T: De>(&mut self, s: &mut Self::State) -> Result<T, Error>;
}

/// Values that can be deserialized from.
pub trait Deserializer: DeSeq + DeMap {
    /// Read a  [`Kson::Null`]. Returns `Ok(())` if successful, otherwise returns an
    /// error.
    fn read_null(&mut self) -> Result<(), Error>;

    /// Read a [`bool`].
    fn read_bool(&mut self) -> Result<bool, Error>;

    /// Read an [`i64`].
    fn read_i64(&mut self) -> Result<i64, Error>;

    /// Read a [`BigInt`].
    fn read_bigint(&mut self) -> Result<BigInt, Error>;

    /// Read an [`Inum`].
    fn read_inum(&mut self) -> Result<Inum, Error>;

    /// Read an [`f16`].
    fn read_f16(&mut self) -> Result<f16, Error>;

    /// Read an [`f32`].
    fn read_f32(&mut self) -> Result<f32, Error>;

    /// Read an [`f64`].
    fn read_f64(&mut self) -> Result<f64, Error>;

    /// Read a [`Float`].
    fn read_float(&mut self) -> Result<Float, Error>;

    /// Read a [`Bytes`].
    fn read_bytes(&mut self) -> Result<Bytes, Error>;
}

/// Try to read length from buffer.
fn read_len<D: DeserializerBytes>(data: &mut D, size: Size, len: u8) -> Result<usize, Error> {
    match size {
        Size::Big => Ok(data.read_uint(len + 1)? as usize + BIGCOL_MIN_LEN as usize),
        Size::Small => Ok(len as usize),
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

impl<B: Buf> DeserializerBytes for B {
    #[inline(always)]
    fn read_tag(&mut self) -> Result<KTag, Error> {
        if self.has_remaining() {
            let byte = self.get_u8();

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
        } else {
            bail!("Buffer was empty, couldn't get tag byte")
        }
    }

    #[inline(always)]
    fn read_many(&mut self, len: usize) -> Result<Vec<u8>, Error> {
        if self.remaining() >= len {
            let mut bts = vec![0; len];
            self.copy_to_slice(&mut bts);
            Ok(bts)
        } else {
            bail!(
                "Requested {} bytes, but only {} bytes were left",
                len,
                self.remaining()
            )
        }
    }

    #[inline(always)]
    fn read_u8(&mut self) -> Result<u8, Error> {
        if self.has_remaining() {
            Ok(self.get_u8())
        } else {
            bail!("Buffer was empty, couldn't get byte")
        }
    }

    #[inline(always)]
    fn read_u16(&mut self) -> Result<u16, Error> {
        if self.remaining() >= 2 {
            Ok(self.get_u16_le())
        } else {
            bail!(
                "Tried to read u16, but only {} bytes were left",
                self.remaining()
            )
        }
    }

    #[inline(always)]
    fn read_u32(&mut self) -> Result<u32, Error> {
        if self.remaining() >= 4 {
            Ok(self.get_u32_le())
        } else {
            bail!(
                "Tried to read u32, but only {} bytes were left",
                self.remaining()
            )
        }
    }

    #[inline(always)]
    fn read_u64(&mut self) -> Result<u64, Error> {
        if self.remaining() >= 8 {
            Ok(self.get_u64_le())
        } else {
            bail!(
                "Tried to read u64, but only {} bytes were left",
                self.remaining()
            )
        }
    }

    #[inline(always)]
    fn read_uint(&mut self, len: u8) -> Result<u64, Error> {
        debug_assert!(len <= 8);
        if self.remaining() >= len as usize {
            Ok(self.get_uint_le(len as usize))
        } else {
            bail!(
                "Tried to read uint of length {}, but only {} bytes were left",
                len,
                self.remaining()
            )
        }
    }
}
impl<D: DeserializerBytes> Deserializer for D {
    #[inline(always)]
    fn read_bytes(&mut self) -> Result<Bytes, Error> {
        match self.read_tag()? {
            KByt(size, len) => {
                let len = read_len(self, size, len)?;
                self.read_many(len).map(Bytes::from)
            }
            _ => bail!("bad tag"),
        }
    }

    #[inline(always)]
    fn read_i64(&mut self) -> Result<i64, Error> {
        match self.read_tag()? {
            KInt(Size::Small, sign, len) if len <= 8 => {
                let val = self.read_uint(len)?;
                if val <= i64::max_value() as u64 {
                    match sign {
                        KSign::Pos => Ok(val as i64),
                        KSign::Neg => Ok(-(val as i64) - 1),
                    }
                } else {
                    bail!("int too large to be i64")
                }
            }
            _ => bail!("Bad tag when reading i64"),
        }
    }

    #[inline(always)]
    fn read_bigint(&mut self) -> Result<BigInt, Error> {
        match self.read_tag()? {
            KInt(size, sign, len) => {
                debug_assert!(len <= 8 || size == Size::Small);
                let val = self.read_uint(len)?;

                let mut i = match size {
                    Size::Small => BigInt::from(val),
                    Size::Big => {
                        let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
                        BigInt::from_bytes_le(Sign::Plus, &digs)
                    }
                };

                if sign == KSign::Neg {
                    i *= -1;
                    i += -1;
                }

                Ok(i)
            }
            _ => bail!("Bad tag when reading BigInt"),
        }
    }

    #[inline(always)]
    fn read_inum(&mut self) -> Result<Inum, Error> {
        match self.read_tag()? {
            KInt(size, sign, len) => {
                debug_assert!(len <= 8 || size == Size::Small);

                let val = self.read_uint(len)?;

                let mut i = match size {
                    Size::Small => Inum::from(val),
                    Size::Big => {
                        let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
                        Inum::from(BigInt::from_bytes_le(Sign::Plus, &digs))
                    }
                };

                if sign == KSign::Neg {
                    i *= -1;
                    i += -1;
                }
                Ok(i)
            }
            _ => bail!("bad tag when reading inum"),
        }
    }

    #[inline(always)]
    fn read_bool(&mut self) -> Result<bool, Error> {
        match self.read_tag()? {
            KCon(CON_TRUE) => Ok(true),
            KCon(CON_FALSE) => Ok(false),
            _ => bail!("bad tag when reading bool"),
        }
    }

    #[inline(always)]
    fn read_null(&mut self) -> Result<(), Error> {
        match self.read_tag()? {
            KCon(CON_NULL) => Ok(()),
            _ => bail!("bad tag when reading null"),
        }
    }

    #[inline(always)]
    fn read_f16(&mut self) -> Result<f16, Error> {
        match self.read_tag()? {
            KFloat(HALF) => self.read_u16().map(f16::from_bits),
            _ => bail!("bad tag when reading half-precision float"),
        }
    }

    #[inline(always)]
    fn read_f32(&mut self) -> Result<f32, Error> {
        match self.read_tag()? {
            KFloat(SINGLE) => self.read_u32().map(f32::from_bits),
            _ => bail!("bad tag when reading single-precision float"),
        }
    }

    #[inline(always)]
    fn read_f64(&mut self) -> Result<f64, Error> {
        match self.read_tag()? {
            KFloat(DOUBLE) => self.read_u64().map(f64::from_bits),
            _ => bail!("bad tag when reading double-precision float"),
        }
    }

    #[inline(always)]
    fn read_float(&mut self) -> Result<Float, Error> {
        match self.read_tag()? {
            KFloat(HALF) => self.read_u16().map(Half),
            KFloat(SINGLE) => self.read_u32().map(Single),
            KFloat(DOUBLE) => self.read_u64().map(Double),
            _ => bail!("bad tag when reading float"),
        }
    }
}

impl<D: DeserializerBytes> DeSeq for D {
    type State = ();

    fn read(&mut self) -> Result<((), usize), Error> {
        match self.read_tag()? {
            KArr(size, len) => {
                let len = read_len(self, size, len)?;
                Ok(((), len))
            }
            _ => bail!("bad tag when starting sequence"),
        }
    }

    fn take<T: De>(&mut self, _: &mut ()) -> Result<T, Error> { T::de(self) }
}

impl<D: DeserializerBytes> DeMap for D {
    type State = ();

    fn take_map(&mut self) -> Result<((), usize), Error> {
        match self.read_tag()? {
            KMap(size, len) => {
                let len = read_len(self, size, len)?;
                Ok(((), len))
            }
            _ => bail!("bad tag when starting map"),
        }
    }

    fn take_key(&mut self, _: &mut ()) -> Result<Bytes, Error> { self.read_bytes() }

    fn take_val<T: De>(&mut self, _: &mut ()) -> Result<T, Error> { T::de(self) }
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

impl<T: De> De for Vec<T> {
    #[inline(always)]
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
        let (mut s, len) = d.read()?;
        let mut out = Vec::with_capacity(len);
        for _ in 0..len {
            out.push(d.take(&mut s)?);
        }
        Ok(out)
    }
}

impl<T: De, S: ::std::hash::BuildHasher + Default> De for HashMap<Bytes, T, S> {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
        let (mut s, len) = d.take_map()?;
        let mut out = HashMap::with_capacity_and_hasher(len, Default::default());
        for _ in 0..len {
            out.insert(d.take_key(&mut s)?, d.take_val(&mut s)?);
        }
        Ok(out)
    }
}

// Implementations for primitive types
macro_rules! easy_de {
    ($typ:ty, $read:tt) => {
        impl De for $typ {
            #[inline(always)]
            fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
                match Self::try_from(d.$read()?) {
                    Err(_) => bail!("Value too big to be `{}`", stringify!(Self)),
                    Ok(v) => Ok(v),
                }
            }
        }
    };
}

macro_rules! trivial_de {
    ($typ:ty, $read:tt) => {
        impl De for $typ {
            #[inline(always)]
            fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.$read() }
        }
    };
}

// Inum
trivial_de!(Inum, read_inum);

// BigInt
trivial_de!(BigInt, read_bigint);

// sizes
easy_de!(usize, read_inum);
easy_de!(isize, read_i64);

// 8-bit ints
easy_de!(u8, read_i64);
easy_de!(i8, read_i64);

// 16-bit ints
easy_de!(u16, read_i64);
easy_de!(i16, read_i64);

// 32-bit ints
easy_de!(u32, read_i64);
easy_de!(i32, read_i64);

// 64-bit ints
easy_de!(u64, read_inum);
trivial_de!(i64, read_i64);

// 128-bit ints
easy_de!(u128, read_inum);
easy_de!(i128, read_inum);

// Floats
trivial_de!(Float, read_float);
trivial_de!(f16, read_f16);
trivial_de!(f32, read_f32);
trivial_de!(f64, read_f64);

// Misc

// unit/nil
trivial_de!((), read_null);

// boolean
trivial_de!(bool, read_bool);

// bytes
trivial_de!(Bytes, read_bytes);

impl De for String {
    #[inline(always)]
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
        let bs = d.read_bytes()?;

        match String::from_utf8(bs.to_vec()) {
            Ok(s) => Ok(s),
            Err(_) => {
                // pre-allocate
                let mut chars = Vec::with_capacity(bs.len() / 2 + 1);

                // bytestring into buffer
                let buf = &mut bs.into_buf();

                // get u16s
                for _ in 0..buf.remaining() {
                    chars.push(buf.get_u16_le());
                }

                // try to read
                match String::from_utf16(&chars) {
                    Ok(s) => Ok(s),
                    Err(_) => bail!("Bytestring was neither valid utf-8 nor utf-16",),
                }
            }
        }
    }
}

impl De for char {
    #[inline(always)]
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
        let mut buf = d.read_bytes()?.into_buf();

        let rem = buf.remaining();

        let c = if rem == 4 {
            buf.get_u32_le()
        } else {
            bail!("Characters are expected to be four bytes, found {}", rem)
        };

        match std::char::from_u32(c) {
            None => bail!("Bytestring is not a valid character"),
            Some(ch) => Ok(ch),
        }
    }
}

// impl<T: De> De for Option<T> {
//     fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
//         match d.read_kson()? {
//             Null => Ok(None),
//             Array(v) => {
//                 let mut iter = v.into_iter();
//                 let val = &mut match iter.next() {
//                     None => bail!("Value is not an `Option`"),
//                     Some(v) => KContainer::new_place(v),
//                 };

//                 if iter.next().is_none() {
//                     Ok(Some(T::de(val)?))
//                 } else {
//                     bail!("Value is not an `Option`")
//                 }
//             }
//             _ => bail!("Value is not an `Option`"),
//         }
//     }
// }

impl De for Ipv4Addr {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
        let bs = Bytes::de(d)?;

        if bs.len() == 4 {
            Ok(Self::new(bs[0], bs[1], bs[2], bs[3]))
        } else {
            bail!(
                "Value is {} bytes long, an `Ipv4Addr` should be 4 bytes long",
                bs.len(),
            )
        }
    }
}

impl De for SocketAddrV4 {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
        let (ip, port) = <(Ipv4Addr, u16)>::de(d)?;
        Ok(Self::new(ip, port))
    }
}

macro_rules! tuple_de {
    ($len:expr, $($typ:ident),*) => {
        impl<$($typ: De),*> De for ($($typ,)*) {
            fn de<Des: Deserializer>(d: &mut Des) -> Result<Self, Error> {
                let exp_len = $len;
                let (mut iter, len) = d.read()?;

                if len == exp_len {
                    let tuple = ($(d.take::<$typ>(&mut iter)?,)*);
                    Ok(tuple)

                } else {
                    bail!("Tuple has wrong number of fields; expected {}, found {}",
                          exp_len,
                          len
                    )
                }
            }
        }
    }
}

tuple_de!(1, A);
tuple_de!(2, A, B);
tuple_de!(3, A, B, C);
tuple_de!(4, A, B, C, D);
tuple_de!(5, A, B, C, D, E);
tuple_de!(6, A, B, C, D, E, F);
tuple_de!(7, A, B, C, D, E, F, G);
tuple_de!(8, A, B, C, D, E, F, G, H);
tuple_de!(9, A, B, C, D, E, F, G, H, I);
tuple_de!(10, A, B, C, D, E, F, G, H, I, J);
tuple_de!(11, A, B, C, D, E, F, G, H, I, J, K);
tuple_de!(12, A, B, C, D, E, F, G, H, I, J, K, L);
