use super::*;
use crate::float::Float;
use failure::*;
use half::f16;
use num_bigint::{BigInt, Sign};
use std::{
    convert::TryFrom,
    net::{Ipv4Addr, SocketAddrV4},
    vec::IntoIter,
};
use KTag::*;

/// KSON tags.
#[derive(Copy, Clone, Debug)]
pub enum KTag {
    /// Constant tag.
    KCon(u8),
    /// Integer tag.
    KInt(bool, bool, u8),
    /// Bytestring tag.
    KByt(bool, u8),
    /// Array tag.
    KArr(bool, u8),
    /// Map tag.
    KMap(bool, u8),
    /// Float tag.
    KFloat(u8),
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

pub trait DeSeq<D>: Sized {
    fn start(d: &mut D) -> Result<(Self, usize), Error>;
    fn take<T: De>(&mut self, d: &mut D) -> Result<T, Error>;
}

pub trait DeMap<D>: Sized {
    fn start(d: &mut D) -> Result<(Self, usize), Error>;
    fn take_key(&mut self, d: &mut D) -> Result<Bytes, Error>;
    fn take_val<T: De>(&mut self, d: &mut D) -> Result<T, Error>;
}

/// Values that can be deserialized from.
pub trait Deserializer {
    // type Seq: DeSeq<Self>;
    // type Map: DeMap<Self>;

    /// Read a [`Kson`] value.
    fn read_kson(&mut self) -> Result<Kson, Error>;

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

    /// Read a vector.
    fn read_arr<T: De>(&mut self) -> Result<Vec<T>, Error>;

    /// Read a [`VecMap`].
    fn read_map<T: De>(&mut self) -> Result<VecMap<Bytes, T>, Error>;
}

/// Try to read length from buffer.
fn read_len<D: DeserializerBytes>(data: &mut D, big: bool, len: u8) -> Result<usize, Error> {
    if big {
        Ok(data.read_uint(len + 1)? as usize + BIGCOL_MIN_LEN as usize)
    } else {
        Ok(len as usize)
    }
}

macro_rules! big_and_len {
    ($ctor:expr, $mask:expr, $byte:ident) => {{
        let big = $byte & BIG_BIT == BIG_BIT;
        let len = $byte & $mask;
        Ok($ctor(big, len))
    }};
    ($ctor:expr, $byte:ident) => {
        big_and_len!($ctor, MASK_LEN_BITS, $byte)
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
                    let big = byte & BIG_BIT == BIG_BIT;
                    let pos = byte & INT_POSITIVE == INT_POSITIVE;
                    let len = byte & MASK_INT_LEN_BITS;
                    debug_assert!(len <= MASK_INT_LEN_BITS);
                    Ok(KInt(big, pos, len + 1))
                }
                TYPE_BYT => big_and_len!(KByt, byte),
                TYPE_ARR => big_and_len!(KArr, byte),
                TYPE_MAP => big_and_len!(KMap, byte),
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
    fn read_kson(&mut self) -> Result<Kson, Error> {
        match self.read_tag()? {
            KCon(CON_NULL) => Ok(Null),
            KCon(CON_TRUE) => Ok(Bool(true)),
            KCon(CON_FALSE) => Ok(Bool(false)),
            KInt(big, pos, len) => {
                let val = self.read_uint(len)?;
                let mut i = if !big {
                    Inum::from(val)
                } else {
                    let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
                    Inum::from(BigInt::from_bytes_le(Sign::Plus, &digs))
                };

                if !pos {
                    i = -i - I64(1);
                }
                Ok(Kint(i))
            }

            KFloat(HALF) => self.read_u16().map(Half).map(Kfloat),
            KFloat(SINGLE) => self.read_u32().map(Single).map(Kfloat),
            KFloat(DOUBLE) => self.read_u64().map(Double).map(Kfloat),

            KByt(big, len) => {
                let len = read_len(self, big, len)?;
                self.read_many(len).map(Bytes::from).map(Byt)
            }

            KArr(big, len) => {
                let len = read_len(self, big, len)?;
                let mut out = Vec::with_capacity(len);
                for _ in 0..len {
                    out.push(Kson::de(self)?);
                }
                Ok(Array(out))
            }

            KMap(big, len) => {
                let len = read_len(self, big, len)?;
                let mut out = Vec::with_capacity(len);
                for _ in 0..len {
                    out.push((self.read_bytes()?, self.read_kson()?));
                }
                // doesn't enforce canonicity - maybe it should?
                Ok(Map(VecMap::from(out)))
            }
            k => bail!("bad tag when reading Kson: {:?}", k),
        }
    }

    #[inline(always)]
    fn read_bytes(&mut self) -> Result<Bytes, Error> {
        match self.read_tag()? {
            KByt(big, len) => {
                let len = read_len(self, big, len)?;
                self.read_many(len).map(Bytes::from)
            }
            _ => bail!("bad tag"),
        }
    }

    #[inline(always)]
    fn read_i64(&mut self) -> Result<i64, Error> {
        match self.read_tag()? {
            KInt(false, pos, len) if len <= 8 => {
                let val = self.read_uint(len)?;
                if val <= i64::max_value() as u64 {
                    if pos {
                        Ok(val as i64)
                    } else {
                        Ok(-(val as i64) - 1)
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
            KInt(big, pos, len) => {
                debug_assert!((big && len <= 8) || (!big && len >= 8));
                let val = self.read_uint(len)?;

                let mut i = if !big {
                    BigInt::from(val)
                } else {
                    let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
                    let sign = if big { Sign::Plus } else { Sign::Minus };
                    BigInt::from_bytes_le(sign, &digs)
                };

                if !pos {
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
            KInt(big, pos, len) => {
                debug_assert!((big && len <= 8) || (!big && len >= 8));
                let val = self.read_uint(len)?;

                let mut i = if !big {
                    Inum::from(val)
                } else {
                    let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
                    Inum::from(BigInt::from_bytes_le(Sign::Plus, &digs))
                };

                if !pos {
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

    #[inline(always)]
    fn read_arr<T: De>(&mut self) -> Result<Vec<T>, Error> {
        match self.read_tag()? {
            KArr(big, len) => {
                let len = read_len(self, big, len)?;
                let mut out = Vec::with_capacity(len);
                for _ in 0..len {
                    out.push(T::de(self)?);
                }
                Ok(out)
            }
            _ => bail!("bad tag when reading array"),
        }
    }

    #[inline(always)]
    fn read_map<T: De>(&mut self) -> Result<VecMap<Bytes, T>, Error> {
        match self.read_tag()? {
            KMap(big, len) => {
                let len = read_len(self, big, len)?;
                let mut out = Vec::with_capacity(len);
                for _ in 0..len {
                    out.push((self.read_bytes()?, T::de(self)?));
                }
                // doesn't enforce canonicity - maybe it should?
                Ok(VecMap::from(out))
            }
            _ => bail!("bad tag when reading array"),
        }
    }
}

pub struct DeSeqBytes {}

impl<D: DeserializerBytes> DeSeq<D> for DeSeqBytes {
    fn start(d: &mut D) -> Result<(Self, usize), Error> {
        match d.read_tag()? {
            KArr(big, len) => {
                let len = read_len(d, big, len)?;
                Ok((DeSeqBytes {}, len))
            }
            _ => bail!("bad tag when starting sequence"),
        }
    }

    fn take<T: De>(&mut self, d: &mut D) -> Result<T, Error> { T::de(d) }
}

pub struct DeMapBytes {}

impl<D: DeserializerBytes> DeMap<D> for DeMapBytes {
    fn start(d: &mut D) -> Result<(Self, usize), Error> {
        match d.read_tag()? {
            KMap(big, len) => {
                let len = read_len(d, big, len)?;
                Ok((DeMapBytes {}, len))
            }
            _ => bail!("bad tag when starting map"),
        }
    }

    fn take_key(&mut self, d: &mut D) -> Result<Bytes, Error> { d.read_bytes() }

    fn take_val<T: De>(&mut self, d: &mut D) -> Result<T, Error> { T::de(d) }
}

impl Deserializer for KContainer {
    #[inline(always)]
    fn read_kson(&mut self) -> Result<Kson, Error> { Ok(self.take()) }

    #[inline(always)]
    fn read_null(&mut self) -> Result<(), Error> {
        let k = self.take();
        match k {
            Null => Ok(()),
            k => bail!("expected Null, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_bool(&mut self) -> Result<bool, Error> {
        let k = self.take();
        match k {
            Bool(b) => Ok(b),
            k => bail!("expected bool, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_i64(&mut self) -> Result<i64, Error> {
        let k = self.take();
        match k {
            Kint(I64(i)) => Ok(i),
            k => bail!("expected i64, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_bigint(&mut self) -> Result<BigInt, Error> {
        let k = self.take();
        match k {
            Kint(Int(i)) => Ok(i),
            k => bail!("expected bigint, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_inum(&mut self) -> Result<Inum, Error> {
        let k = self.take();
        match k {
            Kint(i) => Ok(i),
            k => bail!("expected inum, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_f16(&mut self) -> Result<f16, Error> {
        let k = self.take();
        match k {
            Kfloat(Half(u)) => Ok(f16::from_bits(u)),
            k => bail!("expected half-precision float, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_f32(&mut self) -> Result<f32, Error> {
        let k = self.take();
        match k {
            Kfloat(Single(u)) => Ok(f32::from_bits(u)),
            k => bail!("expected single-precision float, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_f64(&mut self) -> Result<f64, Error> {
        let k = self.take();
        match k {
            Kfloat(Double(u)) => Ok(f64::from_bits(u)),
            k => bail!("expected double-precision float, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_float(&mut self) -> Result<Float, Error> {
        let k = self.take();
        match k {
            Kfloat(f) => Ok(f),
            k => bail!("expected float, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_bytes(&mut self) -> Result<Bytes, Error> {
        let k = self.take();
        match k {
            Byt(b) => Ok(b),
            k => bail!("expected bytes, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_arr<T: De>(&mut self) -> Result<Vec<T>, Error> {
        match self.take() {
            Array(a) => a.into_iter().map(from_kson).collect(),
            k => bail!("expected array, got {:?}", k),
        }
    }

    #[inline(always)]
    fn read_map<T: De>(&mut self) -> Result<VecMap<Bytes, T>, Error> {
        match self.take() {
            Map(m) => {
                let pairs: Result<Vec<(Bytes, T)>, Error> =
                    m.into_iter().map(|(k, v)| Ok((k, from_kson(v)?))).collect();
                pairs.map(VecMap::from_sorted)
            }
            k => bail!("expected array, got {:?}", k),
        }
    }
}

impl DeSeq<KContainer> for IntoIter<Kson> {
    fn start(d: &mut KContainer) -> Result<(Self, usize), Error> {
        match d.take() {
            Array(a) => {
                let len = a.len();
                Ok((a.into_iter(), len))
            }
            k => bail!("tried to read array from value: {:?}", k),
        }
    }

    fn take<T: De>(&mut self, _: &mut KContainer) -> Result<T, Error> {
        T::de(&mut KContainer {
            internal: self.next(),
        })
    }
}

// impl DeMap<KContainer> for IntoIter<(Bytes, Kson)> {}

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
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_arr() }
}

fn from_kson<T: De>(ks: Kson) -> Result<T, Error> { T::de(&mut KContainer::new_place(ks)) }

// Implementations for primitive types
macro_rules! easy_de {
    ($typ:ty, $read:tt) => {
        impl De for $typ {
            #[inline(always)]
            fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
                match Self::try_from(d.$read()?) {
                    Err(_) => bail!("Value to big to be `{}`", stringify!(Self)),
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

// Kson
trivial_de!(Kson, read_kson);

// Inum
trivial_de!(Inum, read_inum);

// BigInt
trivial_de!(BigInt, read_bigint);

// unsigned
easy_de!(u8, read_i64);
easy_de!(u16, read_i64);
easy_de!(u32, read_i64);
easy_de!(u64, read_inum);
easy_de!(usize, read_inum);
easy_de!(u128, read_inum);

// signed
easy_de!(i8, read_i64);
easy_de!(i16, read_i64);
easy_de!(i32, read_i64);
trivial_de!(i64, read_i64);
easy_de!(isize, read_i64);
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

impl<T: De> De for Option<T> {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> {
        match d.read_kson()? {
            Null => Ok(None),
            Array(v) => {
                let mut iter = v.into_iter();
                let val = &mut match iter.next() {
                    None => bail!("Value is not an `Option`"),
                    Some(v) => KContainer::new_place(v),
                };

                if iter.next().is_none() {
                    Ok(Some(T::de(val)?))
                } else {
                    bail!("Value is not an `Option`")
                }
            }
            _ => bail!("Value is not an `Option`"),
        }
    }
}

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
    ($len:expr, $($idx:tt : $typ:ident),*) => {
        impl<$($typ: De),*> De for ($($typ,)*) {
            fn de<Des: Deserializer>(d: &mut Des) -> Result<Self, Error> {
                let exp_len = $len;
                let arr: Vec<Kson> = d.read_arr()?;

                if arr.len() == exp_len {
                    let mut k_iter = arr.into_iter();

                    let tuple = ($($typ::de(&mut KContainer::new_place(k_iter.next().unwrap()))?,)*);
                    Ok(tuple)

                } else {
                    bail!("Tuple has wrong number of fields; expected {}, found {}",
                          exp_len,
                          arr.len()
                    )
                }
            }
        }
    }
}

tuple_de!(1, 0: A);
tuple_de!(2, 0: A, 1: B);
tuple_de!(3, 0: A, 1: B, 2: C);
tuple_de!(4, 0: A, 1: B, 2: C, 3: D);
tuple_de!(5, 0: A, 1: B, 2: C, 3: D, 4: E);
tuple_de!(6, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F);
tuple_de!(7, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G);
tuple_de!(8, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H);
tuple_de!(9, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I);
tuple_de!(
    10,
    0: A,
    1: B,
    2: C,
    3: D,
    4: E,
    5: F,
    6: G,
    7: H,
    8: I,
    9: J
);
tuple_de!(
    11,
    0: A,
    1: B,
    2: C,
    3: D,
    4: E,
    5: F,
    6: G,
    7: H,
    8: I,
    9: J,
    10: K
);
tuple_de!(
    12,
    0: A,
    1: B,
    2: C,
    3: D,
    4: E,
    5: F,
    6: G,
    7: H,
    8: I,
    9: J,
    10: K,
    11: L
);
