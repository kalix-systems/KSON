use super::*;
use half::f16;
use num_bigint::{BigInt, Sign};
use smallvec::SmallVec;

/// TODO docstring
pub trait SerializerBytes {
    /// Add a byte to the output value.
    ///
    /// # Arguments
    ///
    /// * `u: u8` - The byte to be added.
    /// ```
    /// use kson::prelude::*;
    ///
    /// // intialize buffer
    /// let buf = &mut Vec::new();
    ///
    /// // add byte to ouput
    /// buf.put_byte(1);
    /// ```
    fn put_byte(&mut self, u: u8);
    /// Add a slice to the output value.
    ///
    /// ```
    /// use kson::prelude::*;
    ///
    /// // initialize buffer
    /// let buf = &mut Vec::new();
    ///
    /// // add byte to output
    /// buf.put_slice(&[1, 2, 3, 4]);
    /// ```
    fn put_slice(&mut self, slice: &[u8]);
}

/// Sequences of serializable values.
pub trait SerSeq<S> {
    /// # Arguments
    ///
    /// * `start` - TODO
    /// * `len: usize` - The length of the sequence.
    ///
    /// ```
    /// use kson::prelude::*;
    /// ```
    fn start(start: &mut S, len: usize) -> Self;
    /// TODO
    fn put<T: Ser>(&mut self, s: &mut S, t: T);
    /// TODO
    fn finalize(self, s: &mut S);
}

/// Maps with serializable values.
pub trait SerMap<S> {
    /// # Arguments
    ///
    /// * `start` - TODO
    /// * `len: usize` - The length of the sequence.
    fn start(start: &mut S, len: usize) -> Self;
    /// TODO
    fn put<T: Ser>(&mut self, s: &mut S, key: &Bytes, t: T);
    /// TODO
    fn finalize(self, s: &mut S);
}

/// TODO
pub trait Serializer: Sized {
    /// TODO
    type Seq: SerSeq<Self>;
    /// TODO
    type Map: SerMap<Self>;

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
    // fn put_arr<S: Ser>(&mut self, v: &Vec<S>);
    /// Add a map to the output value.
    ///
    /// # Arguments
    ///
    /// * `m` - The value to be added.
    // fn put_map<S: Ser>(&mut self, m: &VecMap<Bytes, S>);

    // this is only here so that we can have Ser do double-duty as KsonRep
    // most of the time you'll want an associated SerSeq, SerMap, and use the default impl
    #[inline(always)]
    fn put_kson(&mut self, k: Kson) { ser_kson(self, &k) }
}

#[inline(always)]
/// Serialize an arbitrary [`Kson`] object.
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
            let mut b = S::Seq::start(s, a.len());
            for v in a {
                b.put(s, v);
            }
            b.finalize(s);
        }
        Map(m) => {
            let mut b = S::Map::start(s, m.len());
            for (k, v) in m.iter() {
                b.put(s, k, v);
            }
            b.finalize(s);
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
    ($len:expr) => {
        if $len <= MASK_LEN_BITS as usize {
            Len($len as u8)
        } else {
            Digs(u64_to_digits($len as u64 - BIGCOL_MIN_LEN))
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

#[derive(Debug, Copy, Clone)]
/// TODO
pub struct SerSeqBytes {}

impl<S: SerializerBytes> SerSeq<S> for SerSeqBytes {
    #[inline(always)]
    fn start(start: &mut S, len: usize) -> Self {
        // let len_or_digs = len_or_digs!(len);
        // tag_and_len!(TYPE_ARR, len_or_digs, start);
        if len <= MASK_LEN_BITS as usize {
            let tag = TYPE_ARR | len as u8;
            start.put_byte(tag);
        } else {
            let len_digs = u64_to_digits(len as u64 - BIGCOL_MIN_LEN);
            let len_len = len_digs.len() as u8 - 1;
            let tag = TYPE_ARR | BIG_BIT | len_len;
            start.put_byte(tag);
            start.put_slice(&len_digs);
        }

        SerSeqBytes {}
    }

    #[inline(always)]
    fn put<T: Ser>(&mut self, s: &mut S, t: T) { t.ser(s) }

    #[inline(always)]
    fn finalize(self, _: &mut S) {}
}

#[derive(Debug, Copy, Clone)]
/// TODO.
pub struct SerMapBytes {}

impl<S: SerializerBytes> SerMap<S> for SerMapBytes {
    #[inline(always)]
    fn start(start: &mut S, len: usize) -> Self {
        if len <= MASK_LEN_BITS as usize {
            let tag = TYPE_MAP | len as u8;
            start.put_byte(tag);
        } else {
            let len_digs = u64_to_digits(len as u64 - BIGCOL_MIN_LEN);
            let len_len = len_digs.len() as u8 - 1;
            let tag = TYPE_MAP | BIG_BIT | len_len;
            start.put_byte(tag);
            start.put_slice(&len_digs);
        }

        SerMapBytes {}
    }

    #[inline(always)]
    fn put<T: Ser>(&mut self, s: &mut S, key: &Bytes, t: T) {
        s.put_bytes(key);
        t.ser(s);
    }

    #[inline(always)]
    fn finalize(self, _: &mut S) {}
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
        let len_or_digs = len_or_digs!(b.len());
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

    // fn put_seq(&mut self, s: Self::Seq) {
    //     if s.len <= MASK_LEN_BITS as u64 {
    //         let tag = TYPE_ARR | s.len as u8;
    //         self.put_byte(tag);
    //     } else {
    //         let len_digs = u64_to_digits(s.len - BIGCOL_MIN_LEN);
    //         let len_len = len_digs.len() as u8 - 1;
    //         let tag = TYPE_ARR | BIG_BIT | len_len;
    //         self.put_byte(tag);
    //         self.put_slice(&len_digs);
    //     }
    //     self.put_slice(&s.buf);
    // }

    // fn put_map(&mut self, m: Self::Map) {
    //     if m.len <= MASK_LEN_BITS as u64 {
    //         let tag = TYPE_MAP | m.len as u8;
    //         self.put_byte(tag);
    //     } else {
    //         let len_digs = u64_to_digits(m.len - BIGCOL_MIN_LEN);
    //         let len_len = len_digs.len() as u8 - 1;
    //         let tag = TYPE_MAP | BIG_BIT | len_len;
    //         self.put_byte(tag);
    //         self.put_slice(&len_digs);
    //     }
    //     self.put_slice(&m.buf);
    // }
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

// struct KContainerSeq {
//     internal: Vec<Kson>,
// }

impl SerSeq<KContainer> for Vec<Kson> {
    #[inline(always)]
    fn start(start: &mut KContainer, len: usize) -> Self {
        debug_assert!(start.is_none());
        Vec::with_capacity(len)
    }

    #[inline(always)]
    fn put<T: Ser>(&mut self, k: &mut KContainer, t: T) {
        debug_assert!(k.is_none());
        self.push(into_kson(t))
    }

    #[inline(always)]
    fn finalize(self, start: &mut KContainer) { start.place(Kson::from(self)) }
}

impl SerMap<KContainer> for Vec<(Bytes, Kson)> {
    #[inline(always)]
    fn start(start: &mut KContainer, len: usize) -> Self {
        debug_assert!(start.is_none());
        Vec::with_capacity(len)
    }

    fn put<T: Ser>(&mut self, k: &mut KContainer, key: &Bytes, t: T) {
        debug_assert!(k.is_none());
        self.push((key.clone(), into_kson(t)));
    }

    fn finalize(self, k: &mut KContainer) { k.place(Kson::from(VecMap::from(self))) }
}

fn into_kson<T: Ser>(t: T) -> Kson {
    let mut k = KContainer::new();
    t.ser(&mut k);
    k.take()
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

    fn put_kson(&mut self, k: Kson) { self.place(k) }
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
