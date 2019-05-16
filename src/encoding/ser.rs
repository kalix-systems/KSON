use super::*;
use half::f16;
use num_bigint::{BigInt, Sign};
use smallvec::SmallVec;

/// TODO docstring
pub trait SerializerBytes {
    /// Add a byte to the output value.
    fn put_byte(&mut self, u: u8);
    /// Add a slice to the output value.
    fn put_slice(&mut self, slice: &[u8]);
}

pub trait SerSeq: Default {
    fn put<T: Ser>(&mut self, t: T);
}

pub trait SerMap: Default {
    fn put<T: Ser>(&mut self, key: Bytes, t: T);
}

/// Convenience methods for [`Serializer`].
pub trait Serializer: Sized {
    type Seq: SerSeq;
    type Map: SerMap;
    /// Add an [`i8`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: i8`  - The value to be added.
    #[inline(always)]
    fn put_i8(&mut self, i: i8) { self.put_i16(i as i16) }
    /// Add an [`i16`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: i16`  - The value to be added.
    #[inline(always)]
    fn put_i16(&mut self, i: i16) { self.put_i32(i as i32) }
    /// Add an [`i32`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: i32`  - The value to be added.
    #[inline(always)]
    fn put_i32(&mut self, i: i32) { self.put_i64(i as i64) }
    /// Add an [`i64`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: i64`  - The value to be added.
    #[inline(always)]
    fn put_i64(&mut self, i: i64) { self.put_bigint(&BigInt::from(i)) }
    /// Add a [`BigInt`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: &BigInt` - The value to be added.
    fn put_bigint(&mut self, i: &BigInt);

    /// Add [`Bytes`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `b: &Bytes` - The value to be added.
    fn put_bytes(&mut self, b: &Bytes);

    /// Add a [`f16] to the output value.
    ///
    /// # Arguments
    ///
    /// * `f: f16` - The value to be added.
    #[inline(always)]
    fn put_f16(&mut self, f: f16) { self.put_f32(f32::from(f)) }
    /// Add an [`f32`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `f: f32` - The value to be added.
    #[inline(always)]
    fn put_f32(&mut self, f: f32) { self.put_f64(f64::from(f)) }
    /// Add an [`f64`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `f: f64` - The value to be added.
    fn put_f64(&mut self, f: f64);

    /// Add a [`bool`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `b: bool` - The value to be added.
    fn put_bool(&mut self, b: bool);
    /// Add [`Kson::Null`] to the output value.
    fn put_null(&mut self);

    /// Add a vector to the output value.
    ///
    /// # Arguments
    ///
    /// * `v` - The value to be added.
    // fn put_arr<S: Ser>(&mut self, v: &[S]);
    /// Add a map to the output value.
    ///
    /// # Arguments
    ///
    /// * `m` - The value to be added.
    // fn put_map<S: Ser>(&mut self, m: &VecMap<Bytes, S>);

    fn put_seq(&mut self, s: Self::Seq);
    fn put_map(&mut self, m: Self::Map);

    // this is only here so that we can have Ser do double-duty as KsonRep
    // default implementation is almost always correct
    #[inline(always)]
    fn put_kson(&mut self, k: Kson) { ser_kson(self, &k) }
}

pub fn ser_kson<S: Serializer>(s: &mut S, k: &Kson) {
    match k {
        Null => s.put_null(),
        Bool(b) => s.put_bool(*b),
        Kint(Int(i)) => s.put_bigint(i),
        Kint(I64(i)) => s.put_i64(*i),
        Kfloat(Half(n)) => s.put_f16(f16::from_bits(*n)),
        Kfloat(Single(n)) => s.put_f32(f32::from_bits(*n)),
        Kfloat(Double(n)) => s.put_f64(f64::from_bits(*n)),
        Byt(bs) => s.put_bytes(bs),
        Array(a) => {
            let mut seq = S::Seq::default();
            for k in a {
                seq.put(k);
            }
            s.put_seq(seq);
        }
        Map(m) => {
            let mut map = S::Map::default();
            for (k, v) in m.iter() {
                map.put(k.clone(), v);
            }
            s.put_map(map);
        }
    }
}

#[inline(always)]
fn compute_int_tag(big: bool, pos: bool, len: u8) -> u8 {
    TYPE_INT | ((big as u8) << 4) | ((pos as u8) << 3) | (len - 1)
}

#[derive(Clone, Debug)]
/// The second element in a tagged KSON integer, bytestring, array, or map.
/// It is either a length (in the case of large versions)
/// or digits (in the case of small versions).
enum LenOrDigs {
    /// Length variant
    Len(u8),
    /// Digits variant
    Digs(SmallVec<[u8; 8]>),
}

use LenOrDigs::*;

impl SerializerBytes for Vec<u8> {
    fn put_byte(&mut self, u: u8) { self.push(u) }

    fn put_slice(&mut self, slice: &[u8]) { self.extend_from_slice(slice) }
}

impl SerializerBytes for Bytes {
    fn put_byte(&mut self, u: u8) { self.extend_from_slice(&[u]) }

    fn put_slice(&mut self, slice: &[u8]) { self.extend_from_slice(slice) }
}

macro_rules! len_or_digs {
    ($id:ident) => {
        if $id.len() <= MASK_LEN_BITS as usize {
            Len($id.len() as u8)
        } else {
            Digs(u64_to_digits($id.len() as u64 - BIGCOL_MIN_LEN))
        }
    };
}

macro_rules! len_or_tag {
    ($tag:ident, $len_digs:ident, $id:ident, $f:expr) => {
        match $id {
            Len(l) => {
                $tag |= $f(l);
                $len_digs = smallvec![];
            }
            Digs(l_d) => {
                let len_len = l_d.len() as u8 - 1;
                $tag |= BIG_BIT;
                $tag |= len_len;
                $len_digs = l_d;
            }
        }
    };
    ($tag:ident, $len_digs:ident, $id:ident) => {
        len_or_tag!($tag, $len_digs, $id, |x| x)
    };
}

macro_rules! tag_and_len {
    ($type:expr, $len_or_digs:ident, $out:ident) => {
        let mut tag = $type;
        let len_digs;
        len_or_tag!(tag, len_digs, $len_or_digs);
        $out.put_byte(tag);
        $out.put_slice(&len_digs);
    };
}

#[derive(Default, Debug)]
pub struct SerSeqBytes {
    len: u64,
    buf: Vec<u8>,
}

impl SerSeq for SerSeqBytes {
    fn put<T: Ser>(&mut self, t: T) {
        self.len += 1;
        t.ser(&mut self.buf);
    }
}

#[derive(Default, Debug)]
pub struct SerMapBytes {
    len: u64,
    buf: Vec<u8>,
}

impl SerMap for SerMapBytes {
    fn put<T: Ser>(&mut self, key: Bytes, t: T) {
        self.len += 1;
        key.ser(&mut self.buf);
        t.ser(&mut self.buf);
    }
}

impl<S: SerializerBytes> Serializer for S {
    type Map = SerMapBytes;
    type Seq = SerSeqBytes;

    #[inline]
    fn put_i64(&mut self, mut i: i64) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let digs = u64_to_digits(i as u64);
        debug_assert!(digs.len() <= 8);

        self.put_byte(compute_int_tag(false, pos, digs.len() as u8));
        self.put_slice(&digs);
    }

    fn put_i32(&mut self, mut i: i32) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let digs = u32_to_digits(i as u32);
        debug_assert!(digs.len() <= 4);

        self.put_byte(compute_int_tag(false, pos, digs.len() as u8));
        self.put_slice(&digs);
    }

    fn put_i16(&mut self, mut i: i16) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let digs = u16_to_digits(i as u16);
        debug_assert!(digs.len() <= 2);

        self.put_byte(compute_int_tag(false, pos, digs.len() as u8));
        self.put_slice(&digs);
    }

    fn put_i8(&mut self, mut i: i8) {
        let pos = !i.is_negative();
        if !pos {
            i += 1;
            i *= -1;
        }
        debug_assert!(i >= 0);

        let mut tag = TYPE_INT;
        tag |= (pos as u8) << 3;

        self.put_byte(tag);
        self.put_byte(i as u8);
    }

    fn put_bigint(&mut self, i: &BigInt) {
        let (sign, mut digs) = i.to_bytes_le();
        let pos = sign != Sign::Minus;
        debug_assert!(digs.len() >= 8);
        if !pos {
            decr_digs(&mut digs)
        };
        if digs.len() == 8 {
            push_digs(pos, &digs, self);
        } else {
            let len = digs.len() - BIGINT_MIN_LEN as usize;
            if len <= u16::max_value() as usize {
                let len_digs = u16_to_digits(len as u16);
                let tag = compute_int_tag(true, pos, len_digs.len() as u8);
                self.put_byte(tag);
                self.put_slice(&len_digs);
                self.put_slice(&digs);
            } else {
                u64_digs(pos, len as u64, digs, self)
            }
        }
    }

    fn put_f16(&mut self, f: f16) {
        self.put_byte(HALF);
        self.put_slice(&u16::to_le_bytes(f.to_bits()));
    }

    fn put_f32(&mut self, f: f32) {
        self.put_byte(SINGLE);
        self.put_slice(&u32::to_le_bytes(f.to_bits()));
    }

    fn put_f64(&mut self, f: f64) {
        self.put_byte(DOUBLE);
        self.put_slice(&u64::to_le_bytes(f.to_bits()));
    }

    fn put_bytes(&mut self, b: &Bytes) {
        let len_or_digs = len_or_digs!(b);
        tag_and_len!(TYPE_BYT, len_or_digs, self);
        self.put_slice(b);
    }

    fn put_bool(&mut self, b: bool) {
        if b {
            self.put_byte(CON_TRUE)
        } else {
            self.put_byte(CON_FALSE)
        }
    }

    fn put_null(&mut self) { self.put_byte(CON_NULL) }

    fn put_seq(&mut self, s: Self::Seq) {
        if s.len <= MASK_LEN_BITS as u64 {
            let tag = TYPE_ARR | s.len as u8;
            self.put_byte(tag);
        } else {
            let len_digs = u64_to_digits(s.len - BIGCOL_MIN_LEN);
            let len_len = len_digs.len() as u8 - 1;
            let tag = TYPE_ARR | BIG_BIT | len_len;
            self.put_byte(tag);
            self.put_slice(&len_digs);
        }
        self.put_slice(&s.buf);
    }

    fn put_map(&mut self, m: Self::Map) {
        if m.len <= MASK_LEN_BITS as u64 {
            let tag = TYPE_MAP | m.len as u8;
            self.put_byte(tag);
        } else {
            let len_digs = u64_to_digits(m.len - BIGCOL_MIN_LEN);
            let len_len = len_digs.len() as u8 - 1;
            let tag = TYPE_MAP | BIG_BIT | len_len;
            self.put_byte(tag);
            self.put_slice(&len_digs);
        }
        self.put_slice(&m.buf);
    }
    // fn put_arr<T: Ser>(&mut self, v: &[T]) {
    //     let len_or_digs = len_or_digs!(v);
    //     tag_and_len!(TYPE_ARR, len_or_digs, self);
    //     for t in v {
    //         t.ser(self);
    //     }
    // }

    // fn put_map<T: Ser>(&mut self, m: &VecMap<Bytes, T>) {
    //     let len_or_digs = len_or_digs!(m);
    //     tag_and_len!(TYPE_MAP, len_or_digs, self);
    //     for (k, v) in m.iter() {
    //         self.put_bytes(k);
    //         v.ser(self);
    //     }
    // }
}

impl SerSeq for Vec<Kson> {
    fn put<T: Ser>(&mut self, t: T) { self.push(into_kson(t)) }
}

impl SerMap for Vec<(Bytes, Kson)> {
    fn put<T: Ser>(&mut self, key: Bytes, t: T) { self.push((key, into_kson(t))) }
}

fn into_kson<T: Ser>(t: T) -> Kson {
    let mut kc = KContainer::new();
    t.ser(&mut kc);
    kc.take()
}

struct KContainer {
    internal: Option<Kson>,
}

impl KContainer {
    fn new() -> KContainer { KContainer { internal: None } }

    fn place(&mut self, k: Kson) {
        assert!(self.internal.is_none());
        self.internal = Some(k);
    }

    fn take(self) -> Kson { self.internal.unwrap() }
}

impl Serializer for KContainer {
    type Map = Vec<(Bytes, Kson)>;
    type Seq = Vec<Kson>;

    fn put_null(&mut self) { self.place(Null); }

    fn put_bool(&mut self, b: bool) { self.place(Kson::from(b)); }

    fn put_i64(&mut self, i: i64) { self.place(Kson::from(i)); }

    fn put_bigint(&mut self, i: &BigInt) { self.place(Kson::from(i.clone())) }

    fn put_f16(&mut self, f: f16) { self.place(Kson::from(f)); }

    fn put_f32(&mut self, f: f32) { self.place(Kson::from(f)); }

    fn put_f64(&mut self, f: f64) { self.place(Kson::from(f)); }

    fn put_bytes(&mut self, b: &Bytes) { self.place(Kson::from(b.clone())); }

    fn put_seq(&mut self, s: Self::Seq) { self.place(Kson::from(s)); }

    fn put_map(&mut self, m: Self::Map) { self.place(Kson::from(VecMap::from(m))); }

    fn put_kson(&mut self, k: Kson) { self.place(Kson::from(k)); }
}

#[cold]
#[inline]
fn decr_digs(digs: &mut Vec<u8>) {
    // subtract 1 directly on the digits
    for dig in digs.iter_mut() {
        *dig = dig.wrapping_sub(1);
        if *dig != 255 {
            break;
        }
    }

    let last = digs.pop().unwrap();
    if last != 0 {
        digs.push(last)
    }
}

#[cold]
#[inline]
fn push_digs<S: SerializerBytes>(pos: bool, digs: &[u8], out: &mut S) {
    out.put_byte(compute_int_tag(false, pos, digs.len() as u8));
    out.put_slice(digs);
}

#[cold]
#[inline]
fn u64_digs<S: SerializerBytes>(pos: bool, u: u64, digs: Vec<u8>, out: &mut S) {
    let len_digs = u64_to_digits(u);
    out.put_byte(compute_int_tag(true, pos, len_digs.len() as u8));
    out.put_slice(&len_digs);
    out.put_slice(&digs);
}

/// An value that can be serialized.
pub trait Ser {
    /// TODO docstring
    fn ser<S: Serializer>(self, s: &mut S);
}

impl Ser for &Kson {
    fn ser<S: Serializer>(self, s: &mut S) { ser_kson(s, self) }
}

impl Ser for Kson {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_kson(self) }
}

impl Ser for &Bytes {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bytes(self) }
}

impl Ser for Bytes {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bytes(&self) }
}
