use super::*;
use crate::{float::Float, rentable::Rentable};
use failure::*;
use half::f16;
use num_bigint::{BigInt, Sign};
use KTag::*;

/// KSON tags.
#[derive(Copy, Clone, Debug)]
pub enum KTag {
    KCon(u8),
    KInt(bool, bool, u8),
    KByt(bool, u8),
    KArr(bool, u8),
    KMap(bool, u8),
    KFloat(u8),
}

// TODO: error-chain based handling instead of this
// but I'm lazy
pub trait DeserializerBytes {
    #[inline(always)]
    fn read_tag(&mut self) -> Result<KTag, Error>;
    #[inline(always)]
    fn read_many(&mut self, len: usize) -> Result<Vec<u8>, Error>;
    #[inline(always)]
    fn read_u8(&mut self) -> Result<u8, Error>;
    #[inline(always)]
    fn read_u16(&mut self) -> Result<u16, Error>;
    #[inline(always)]
    fn read_u32(&mut self) -> Result<u32, Error>;
    #[inline(always)]
    fn read_u64(&mut self) -> Result<u64, Error>;
    #[inline(always)]
    fn read_uint(&mut self, len: u8) -> Result<u64, Error>;
}

pub trait Deserializer {
    #[inline(always)]
    fn read_kson(&mut self) -> Result<Kson, Error>;
    #[inline(always)]
    fn read_null(&mut self) -> Result<(), Error>;
    #[inline(always)]
    fn read_bool(&mut self) -> Result<bool, Error>;
    #[inline(always)]
    fn read_i64(&mut self) -> Result<i64, Error>;
    #[inline(always)]
    fn read_bigint(&mut self) -> Result<BigInt, Error>;
    #[inline(always)]
    fn read_inum(&mut self) -> Result<Inum, Error>;
    #[inline(always)]
    fn read_half(&mut self) -> Result<f16, Error>;
    #[inline(always)]
    fn read_single(&mut self) -> Result<f32, Error>;
    #[inline(always)]
    fn read_double(&mut self) -> Result<f64, Error>;
    #[inline(always)]
    fn read_float(&mut self) -> Result<Float, Error>;
    #[inline(always)]
    fn read_bytes(&mut self) -> Result<Bytes, Error>;
    #[inline(always)]
    fn read_arr<T: De>(&mut self) -> Result<Vec<T>, Error>;
    #[inline(always)]
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
    fn read_kson(&mut self) -> Result<Kson, Error> {
        match self.read_tag()? {
            KCon(CON_NULL) => Ok(Null),
            KCon(CON_TRUE) => Ok(Bool(true)),
            KCon(CON_FALSE) => Ok(Bool(false)),
            KInt(big, pos, len) => {
                // debug_assert!((!big && len <= 8) || (big && len >= 8));
                let val = self.read_uint(len)?;
                let mut i;
                if !big {
                    i = Inum::from(val);
                } else {
                    let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
                    i = Inum::from(BigInt::from_bytes_le(Sign::Plus, &digs));
                }
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

    fn read_bytes(&mut self) -> Result<Bytes, Error> {
        match self.read_tag()? {
            KByt(big, len) => {
                let len = read_len(self, big, len)?;
                self.read_many(len).map(Bytes::from)
            }
            _ => bail!("bad tag"),
        }
    }

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
                    bail!("int too large for i64")
                }
            }
            _ => bail!("bad tag when reading i64"),
        }
    }

    fn read_bigint(&mut self) -> Result<BigInt, Error> {
        match self.read_tag()? {
            KInt(big, pos, len) => {
                debug_assert!((big && len <= 8) || (!big && len >= 8));
                let val = self.read_uint(len)?;
                let mut i;
                if !big {
                    i = BigInt::from(val);
                } else {
                    let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
                    let sign = if big { Sign::Plus } else { Sign::Minus };
                    i = BigInt::from_bytes_le(sign, &digs);
                }
                if !pos {
                    i *= -1;
                    i += -1;
                }
                Ok(i)
            }
            _ => bail!("bad tag when reading bigint"),
        }
    }

    fn read_inum(&mut self) -> Result<Inum, Error> {
        match self.read_tag()? {
            KInt(big, pos, len) => {
                debug_assert!((big && len <= 8) || (!big && len >= 8));
                let val = self.read_uint(len)?;
                let mut i;
                if !big {
                    i = Inum::from(val);
                } else {
                    let digs = self.read_many(val as usize + BIGINT_MIN_LEN as usize)?;
                    i = Inum::from(BigInt::from_bytes_le(Sign::Plus, &digs));
                }
                if !pos {
                    i *= -1;
                    i += -1;
                }
                Ok(i)
            }
            _ => bail!("bad tag when reading inum"),
        }
    }

    fn read_bool(&mut self) -> Result<bool, Error> {
        match self.read_tag()? {
            KCon(CON_TRUE) => Ok(true),
            KCon(CON_FALSE) => Ok(false),
            _ => bail!("bad tag when reading bool"),
        }
    }

    fn read_null(&mut self) -> Result<(), Error> {
        match self.read_tag()? {
            KCon(CON_NULL) => Ok(()),
            _ => bail!("bad tag when reading null"),
        }
    }

    fn read_half(&mut self) -> Result<f16, Error> {
        match self.read_tag()? {
            KFloat(HALF) => self.read_u16().map(f16::from_bits),
            _ => bail!("bad tag when reading half-precision float"),
        }
    }

    fn read_single(&mut self) -> Result<f32, Error> {
        match self.read_tag()? {
            KFloat(SINGLE) => self.read_u32().map(f32::from_bits),
            _ => bail!("bad tag when reading single-precision float"),
        }
    }

    fn read_double(&mut self) -> Result<f64, Error> {
        match self.read_tag()? {
            KFloat(DOUBLE) => self.read_u64().map(f64::from_bits),
            _ => bail!("bad tag when reading double-precision float"),
        }
    }

    fn read_float(&mut self) -> Result<Float, Error> {
        match self.read_tag()? {
            KFloat(HALF) => self.read_u16().map(Half),
            KFloat(SINGLE) => self.read_u32().map(Single),
            KFloat(DOUBLE) => self.read_u64().map(Double),
            _ => bail!("bad tag when reading float"),
        }
    }

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

impl Deserializer for Rentable<Kson> {
    fn read_kson(&mut self) -> Result<Kson, Error> {
        let k = self.rent();
        self.replace(Null);
        Ok(k)
    }

    fn read_null(&mut self) -> Result<(), Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Null => Ok(()),
            k => bail!("expected Null, got {:?}", k),
        }
    }

    fn read_bool(&mut self) -> Result<bool, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Bool(b) => Ok(b),
            k => bail!("expected bool, got {:?}", k),
        }
    }

    fn read_i64(&mut self) -> Result<i64, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Kint(I64(i)) => Ok(i),
            k => bail!("expected i64, got {:?}", k),
        }
    }

    fn read_bigint(&mut self) -> Result<BigInt, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Kint(Int(i)) => Ok(i),
            k => bail!("expected bigint, got {:?}", k),
        }
    }

    fn read_inum(&mut self) -> Result<Inum, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Kint(i) => Ok(i),
            k => bail!("expected inum, got {:?}", k),
        }
    }

    fn read_half(&mut self) -> Result<f16, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Kfloat(Half(u)) => Ok(f16::from_bits(u)),
            k => bail!("expected half-precision float, got {:?}", k),
        }
    }

    fn read_single(&mut self) -> Result<f32, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Kfloat(Single(u)) => Ok(f32::from_bits(u)),
            k => bail!("expected single-precision float, got {:?}", k),
        }
    }

    fn read_double(&mut self) -> Result<f64, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Kfloat(Double(u)) => Ok(f64::from_bits(u)),
            k => bail!("expected double-precision float, got {:?}", k),
        }
    }

    fn read_float(&mut self) -> Result<Float, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Kfloat(f) => Ok(f),
            k => bail!("expected float, got {:?}", k),
        }
    }

    fn read_bytes(&mut self) -> Result<Bytes, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Byt(b) => Ok(b),
            k => bail!("expected bytes, got {:?}", k),
        }
    }

    fn read_arr<T: De>(&mut self) -> Result<Vec<T>, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Array(a) => {
                a.into_iter()
                    .map(|k| T::de(&mut Rentable::new(k)))
                    .collect()
            }
            k => bail!("expected array, got {:?}", k),
        }
    }

    fn read_map<T: De>(&mut self) -> Result<VecMap<Bytes, T>, Error> {
        let k = self.rent();
        self.replace(Null);
        match k {
            Map(m) => {
                let pairs: Result<Vec<(Bytes, T)>, Error> = m
                    .into_iter()
                    .map(|(k, v)| Ok((k, T::de(&mut Rentable::new(v))?)))
                    .collect();
                pairs.map(VecMap::from_sorted)
            }
            k => bail!("expected array, got {:?}", k),
        }
    }
}

pub trait De: Sized {
    #[inline(always)]
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error>;
}

impl De for Kson {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_kson() }
}

impl De for Bytes {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_bytes() }
}
impl De for i64 {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_i64() }
}
impl De for BigInt {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_bigint() }
}

impl De for Inum {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_inum() }
}

impl De for bool {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_bool() }
}

impl De for () {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_null() }
}

impl<T: De> De for Vec<T> {
    fn de<D: Deserializer>(d: &mut D) -> Result<Self, Error> { d.read_arr() }
}
