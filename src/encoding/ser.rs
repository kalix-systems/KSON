use super::*;
use bytes::buf::{FromBuf, IntoBuf};
use half::f16;
use hashbrown::HashMap;
use num_bigint::{BigInt, Sign};
use smallvec::SmallVec;
use std::{
    hash::{BuildHasher, Hash},
    net::{Ipv4Addr, SocketAddrV4},
};

/// Byte-oriented serializer.
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
    /// buf.put_buf([1, 2, 3, 4].into_buf());
    /// ```
    fn put_buf<B: Buf>(&mut self, buf: B) {
        for b in buf.iter() {
            self.put_byte(b)
        }
    }
}

/// A serializer that works from sequences of values.
pub trait SerSeq {
    /// The state of the sequence. This is idiomatically [`()`] if the
    /// deserializer doesn't need to track intermediate states.

    type State: Sized;
    /// # Arguments
    ///
    /// * `len: usize` - The length of the sequence.
    ///
    /// ```
    /// use kson::prelude::*;
    /// ```

    fn seq_start(&mut self, len: usize) -> Self::State;

    // TODO: consider renaming
    /// Add an element to the sequence.
    ///
    /// # Arguments
    ///
    /// * `s: &mut Self::State` - A mutable reference to the current state of the
    ///   serializer.
    fn seq_put<T: Ser>(&mut self, s: &mut Self::State, t: T);

    /// Finalize the sequence.
    ///
    /// # Arguments
    ///
    /// * `s: Self::State` - The current (and final) state of the serializer.
    fn seq_finalize(&mut self, s: Self::State);
}

/// A serializer that is able to accept sequences of (key, value) pairs.
pub trait SerMap {
    /// The state of the serializer.
    type State: Sized;

    /// # Arguments
    ///
    /// * `len: usize` - The number of entries in the map.
    fn map_start(&mut self, len: usize) -> Self::State;

    // TODO: consider renaming
    /// Add a key-value entry to the serializer.
    ///
    /// # Arguments
    ///
    /// * `s: &mut Self::State` - The current state of the serializer.
    fn map_put<K: Ord + IntoBuf, T: Ser>(&mut self, s: &mut Self::State, key: K, t: T);

    /// Finalize the map serializer.
    ///
    /// # Arguments
    ///
    /// * `s: Self::State` - The current (and final) state of the serializer.
    fn map_finalize(&mut self, s: Self::State);
}

/// Note: Overriding the provided implementations when possible can often improve
/// performance.
pub trait Serializer: SerSeq + SerMap + Sized {
    /// Add an [`u8`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `u: u8`  - The value to be added.
    #[inline(always)]
    fn put_u8(&mut self, u: u8) { self.put_i8(i8::from_ne_bytes([u])) }

    /// Add an [`i8`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: i8`  - The value to be added.
    fn put_i8(&mut self, i: i8) { self.put_i16(i as i16) }

    /// Add an [`i16`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: i16`  - The value to be added.
    fn put_i16(&mut self, i: i16) { self.put_i32(i as i32) }

    /// Add an [`i32`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: i32`  - The value to be added.
    fn put_i32(&mut self, i: i32) { self.put_i64(i as i64) }

    /// Add an [`i64`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `i: i64`  - The value to be added.
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
    fn put_bytes<B: IntoBuf>(&mut self, b: B);

    /// Add an [`f16] to the output value.
    ///
    /// # Arguments
    ///
    /// * `f: f16` - The value to be added.
    fn put_f16(&mut self, f: f16) { self.put_f32(f32::from(f)) }

    /// Add an [`f32`] to the output value.
    ///
    /// # Arguments
    ///
    /// * `f: f32` - The value to be added.
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

    /// Add arbitrary [`Kson`] to the output value.
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
            let mut b = s.seq_start(a.len());
            for v in a {
                s.seq_put(&mut b, v);
            }
            s.seq_finalize(b);
        }
        Map(m) => {
            let mut b = s.map_start(m.len());
            for (k, v) in m.iter() {
                s.map_put(&mut b, k, v);
            }
            s.map_finalize(b);
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

    fn put_buf<B: Buf>(&mut self, mut buf: B) {
        while buf.remaining() > 0 {
            let slice = buf.bytes();
            self.extend_from_slice(slice);
            let len = slice.len();
            buf.advance(len);
        }
    }
}

impl SerializerBytes for Bytes {
    fn put_byte(&mut self, u: u8) { self.extend_from_slice(&[u]) }

    fn put_buf<B: Buf>(&mut self, mut buf: B) {
        while buf.remaining() > 0 {
            let slice = buf.bytes();
            self.extend_from_slice(slice);
            let len = slice.len();
            buf.advance(len);
        }
    }
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
        $out.put_buf(len_digs.into_buf());
    };
}

impl<S: SerializerBytes> SerSeq for S {
    type State = ();

    #[inline(always)]
    fn seq_start(&mut self, len: usize) {
        // let len_or_digs = len_or_digs!(len);
        // tag_and_len!(TYPE_ARR, len_or_digs, start);
        if len <= MASK_LEN_BITS as usize {
            let tag = TYPE_ARR | len as u8;
            self.put_byte(tag);
        } else {
            let len_digs = u64_to_digits(len as u64 - BIGCOL_MIN_LEN);
            let len_len = len_digs.len() as u8 - 1;
            let tag = TYPE_ARR | BIG_BIT | len_len;
            self.put_byte(tag);
            self.put_buf(len_digs.into_buf());
        }
    }

    #[inline(always)]
    fn seq_put<T: Ser>(&mut self, _: &mut (), t: T) { t.ser(self) }

    #[inline(always)]
    fn seq_finalize(&mut self, _: ()) {}
}

impl<S: SerializerBytes> SerMap for S {
    type State = ();

    #[inline(always)]
    fn map_start(&mut self, len: usize) {
        if len <= MASK_LEN_BITS as usize {
            let tag = TYPE_MAP | len as u8;
            self.put_byte(tag);
        } else {
            let len_digs = u64_to_digits(len as u64 - BIGCOL_MIN_LEN);
            let len_len = len_digs.len() as u8 - 1;
            let tag = TYPE_MAP | BIG_BIT | len_len;
            self.put_byte(tag);
            self.put_buf(len_digs.into_buf());
        }
    }

    #[inline(always)]
    fn map_put<K: Ord + IntoBuf, T: Ser>(&mut self, _: &mut Self::State, key: K, t: T) {
        self.put_bytes(key);
        t.ser(self);
    }

    #[inline(always)]
    fn map_finalize(&mut self, _: ()) {}
}

impl<S: SerializerBytes> Serializer for S {
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
        self.put_buf(digs.into_buf());
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
        self.put_buf(digs.into_buf());
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
        self.put_buf(digs.into_buf());
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
                self.put_buf(len_digs.into_buf());
                self.put_buf(digs.into_buf());
            } else {
                u64_digs(pos, len as u64, digs, self)
            }
        }
    }

    fn put_f16(&mut self, f: f16) {
        self.put_byte(HALF);
        self.put_buf(u16::to_le_bytes(f.to_bits()).into_buf());
    }

    fn put_f32(&mut self, f: f32) {
        self.put_byte(SINGLE);
        self.put_buf(u32::to_le_bytes(f.to_bits()).into_buf());
    }

    fn put_f64(&mut self, f: f64) {
        self.put_byte(DOUBLE);
        self.put_buf(u64::to_le_bytes(f.to_bits()).into_buf());
    }

    fn put_bytes<B: IntoBuf>(&mut self, b: B) {
        let buf = b.into_buf();
        let len_or_digs = len_or_digs!(buf.remaining());
        tag_and_len!(TYPE_BYT, len_or_digs, self);
        self.put_buf(buf);
    }

    fn put_bool(&mut self, b: bool) {
        if b {
            self.put_byte(CON_TRUE)
        } else {
            self.put_byte(CON_FALSE)
        }
    }

    fn put_null(&mut self) { self.put_byte(CON_NULL) }
}

impl SerSeq for KContainer {
    type State = Vec<Kson>;

    #[inline(always)]
    fn seq_start(&mut self, len: usize) -> Vec<Kson> {
        debug_assert!(self.is_none());
        Vec::with_capacity(len)
    }

    #[inline(always)]
    fn seq_put<T: Ser>(&mut self, v: &mut Vec<Kson>, t: T) {
        debug_assert!(self.is_none());
        v.push(into_kson(t))
    }

    #[inline(always)]
    fn seq_finalize(&mut self, vec: Vec<Kson>) { self.place(Kson::from(vec)) }
}

impl SerMap for KContainer {
    type State = Vec<(Bytes, Kson)>;

    #[inline(always)]
    fn map_start(&mut self, len: usize) -> Vec<(Bytes, Kson)> {
        debug_assert!(self.is_none());
        Vec::with_capacity(len)
    }

    #[inline(always)]
    fn map_put<K: Ord + IntoBuf, T: Ser>(&mut self, s: &mut Self::State, key: K, t: T) {
        debug_assert!(self.is_none());
        s.push((Bytes::from_buf(key), into_kson(t)));
    }

    #[inline(always)]
    fn map_finalize(&mut self, m: Self::State) { self.place(Kson::from(VecMap::from(m))) }
}

pub fn into_kson<T: Ser>(t: T) -> Kson {
    let mut k = KContainer::new();
    t.ser(&mut k);
    k.take()
}

impl Serializer for KContainer {
    fn put_null(&mut self) { self.place(Null); }

    fn put_bool(&mut self, b: bool) { self.place(Kson::from(b)); }

    fn put_i64(&mut self, i: i64) { self.place(Kson::from(i)); }

    fn put_bigint(&mut self, i: &BigInt) { self.place(Kson::from(i.clone())) }

    fn put_f16(&mut self, f: f16) { self.place(Kson::from(f)); }

    fn put_f32(&mut self, f: f32) { self.place(Kson::from(f)); }

    fn put_f64(&mut self, f: f64) { self.place(Kson::from(f)); }

    fn put_bytes<B: IntoBuf>(&mut self, b: B) {
        self.place(Kson::from(Bytes::from_buf(b.into_buf())));
    }

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
    out.put_buf(digs.into_buf());
}

#[cold]
#[inline]
fn u64_digs<S: SerializerBytes>(pos: bool, u: u64, digs: Vec<u8>, out: &mut S) {
    let len_digs = u64_to_digits(u);
    out.put_byte(compute_int_tag(true, pos, len_digs.len() as u8));
    out.put_buf(len_digs.into_buf());
    out.put_buf(digs.into_buf());
}

/// An value that can be serialized.
pub trait Ser {
    /// Serializes the value, consuming it.
    ///
    /// # Arguments
    ///
    /// * `s: &mut S` - A mutable reference to the serializer.
    fn ser<S: Serializer>(self, s: &mut S);
}

// Kson
impl Ser for &Kson {
    fn ser<S: Serializer>(self, s: &mut S) { ser_kson(s, self) }
}
impl Ser for Kson {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_kson(self) }
}

// Bytes
impl Ser for &Bytes {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bytes(self) }
}

impl Ser for Bytes {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bytes(&self) }
}

// BigInt
impl Ser for &BigInt {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bigint(self) }
}
impl Ser for BigInt {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bigint(&self) }
}

// Inum
impl Ser for Inum {
    fn ser<S: Serializer>(self, s: &mut S) {
        match self {
            I64(i) => s.put_i64(i),
            Int(i) => s.put_bigint(&i),
        }
    }
}
impl Ser for &Inum {
    fn ser<S: Serializer>(self, s: &mut S) {
        match self {
            I64(i) => s.put_i64(*i),
            Int(i) => s.put_bigint(i),
        }
    }
}

macro_rules! easy_ser_copy {
    ($typ:ty, $put:tt) => {
        impl Ser for $typ {
            #[inline(always)]
            fn ser<S: Serializer>(self, s: &mut S) { s.$put(self.into()) }
        }
    };
}

macro_rules! inum_ser_copy {
    ($typ:ty) => {
        impl Ser for $typ {
            #[inline(always)]
            fn ser<S: Serializer>(self, s: &mut S) { Inum::ser(self.into(), s) }
        }
    };
}

macro_rules! trivial_ser_copy {
    ($typ:ty, $put:tt) => {
        impl Ser for $typ {
            fn ser<S: Serializer>(self, s: &mut S) { s.$put(self) }
        }
    };
}

// TODO many of these are less efficient than they should be

// sizes
impl Ser for isize {
    fn ser<S: Serializer>(self, s: &mut S) { i64::ser(self as i64, s) }
}

impl Ser for usize {
    fn ser<S: Serializer>(self, s: &mut S) { u64::ser(self as u64, s) }
}

// 8-bit ints
trivial_ser_copy!(u8, put_u8);
easy_ser_copy!(i8, put_i8);

// 16-bit ints
easy_ser_copy!(u16, put_i64);
easy_ser_copy!(i16, put_i16);

// 32-bit ints
easy_ser_copy!(u32, put_i64);
easy_ser_copy!(i32, put_i32);

// 64-bit ints
trivial_ser_copy!(i64, put_i64);
inum_ser_copy!(u64);

// 128-bit ints
inum_ser_copy!(i128);
inum_ser_copy!(u128);

// floats
trivial_ser_copy!(f16, put_f16);
trivial_ser_copy!(f32, put_f32);
trivial_ser_copy!(f64, put_f64);

// boolean
trivial_ser_copy!(bool, put_bool);

impl Ser for () {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_null() }
}

// Strings
impl Ser for String {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bytes(&Bytes::from_buf(self)) }
}

impl Ser for &str {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bytes(&Bytes::from_buf(self)) }
}

// chars
impl Ser for char {
    fn ser<S: Serializer>(self, s: &mut S) { String::ser(self.to_string(), s) }
}

impl<T: Ser> Ser for Option<T> {
    fn ser<S: Serializer>(self, s: &mut S) {
        match self {
            None => s.put_null(),
            Some(t) => vec![t].ser(s),
        }
    }
}

impl<'a, T> Ser for &'a Vec<T>
where
    &'a T: Ser,
{
    fn ser<S: Serializer>(self, s: &mut S) {
        let mut bs = s.seq_start(self.len());
        for t in self {
            s.seq_put(&mut bs, t);
        }
    }
}

impl<T: Ser> Ser for Vec<T> {
    fn ser<S: Serializer>(self, s: &mut S) {
        let mut bs = s.seq_start(self.len());
        for t in self {
            s.seq_put(&mut bs, t);
        }
    }
}

impl<'a, K, T> Ser for &'a VecMap<K, T>
where
    K: Ord,
    &'a K: IntoBuf,
    &'a T: Ser,
{
    fn ser<S: Serializer>(self, s: &mut S) {
        let mut b = s.map_start(self.len());
        for (k, v) in self.iter() {
            s.map_put(&mut b, k, v);
        }
        s.map_finalize(b);
    }
}

impl<K: Ord + IntoBuf, T: Ser> Ser for VecMap<K, T> {
    fn ser<S: Serializer>(self, s: &mut S) {
        let mut b = s.map_start(self.len());
        for (k, v) in self.into_iter() {
            s.map_put(&mut b, k, v);
        }
        s.map_finalize(b);
    }
}

impl<K: Hash + Ord + IntoBuf, T: Ser, S: BuildHasher + Default + Clone> Ser for HashMap<K, T, S> {
    fn ser<Se: Serializer>(self, s: &mut Se) { VecMap::from(self).ser(s) }
}

impl Ser for Ipv4Addr {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bytes(Bytes::from(self.octets().to_vec())) }
}

impl Ser for &Ipv4Addr {
    fn ser<S: Serializer>(self, s: &mut S) { s.put_bytes(Bytes::from(self.octets().to_vec())) }
}

impl Ser for SocketAddrV4 {
    fn ser<S: Serializer>(self, s: &mut S) { (self.ip(), self.port()).ser(s) }
}

macro_rules! tuple_ser {
    ($len:expr, $($typ:ident),*) => {
        impl<$($typ: Ser),*> Ser for ($($typ,)*) {
            #[allow(non_snake_case)]
            #[inline(always)]
            fn ser<Se: Serializer>(self, s: &mut Se) {
                let mut state = s.seq_start($len);
                let ($($typ,)*) = self;
                $(s.seq_put(&mut state, $typ);)*
                s.seq_finalize(state);
            }
        }
    };
}

tuple_ser!(1, A);
tuple_ser!(2, A, B);
tuple_ser!(3, A, B, C);
tuple_ser!(4, A, B, C, D);
tuple_ser!(5, A, B, C, D, E);
tuple_ser!(6, A, B, C, D, E, F);
tuple_ser!(7, A, B, C, D, E, F, G);
tuple_ser!(8, A, B, C, D, E, F, G, H);
tuple_ser!(9, A, B, C, D, E, F, G, H, I);
tuple_ser!(10, A, B, C, D, E, F, G, H, I, J);
tuple_ser!(11, A, B, C, D, E, F, G, H, I, J, K);
tuple_ser!(12, A, B, C, D, E, F, G, H, I, J, K, L);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;
    // extern crate kson_derive;
    use kson_derive::*;

    #[test]
    // Test `KsonRep` auto-derive for unit-like struct
    fn unit_struct() {
        #[derive(KSerDe, KsonRep, Clone)]
        struct UnitStruct;

        //// to_kson
        // match UnitStruct::from_kson(UnitStruct.to_kson()) {
        //    Ok(UnitStruct) => {}
        //    Err(_e) => panic!("Couldn't retrieve unit struct"),
        //}

        // into_kson
        match crate::encoding::de::from_kson(into_kson(UnitStruct)) {
            Ok(UnitStruct) => (),
            Err(_e) => panic!("Couldn't retrieve unit struct"),
        }
    }

    #[test]
    // Test `KsonRep` autoderive for named-tuple struct
    fn tuple_struct() {
        #[derive(KSerDe, KsonRep, Clone, Debug)]
        struct Foo(u8, String);
        let ks = into_kson(Foo(1, "hello".to_string()));
        dbg!(&ks);
        match crate::encoding::de::from_kson(ks) {
            Ok(Foo(num, s)) => {
                assert_eq!(num, 1);
                assert_eq!(s, "hello".to_string());
            }
            Err(e) => panic!("No Foo: {}", e),
        }
    }

    #[test]
    // Test `KsonRep` auto-derive for C-style struct
    fn c_struct() {
        #[derive(KSerDe, KsonRep, Clone)]
        struct CStruct {
            fu:  u8,
            baz: String,
            bar: i8,
        };

        let c_struct = CStruct {
            fu:  1,
            bar: 0,
            baz: "hello".to_owned(),
        };

        // to_kson
        // match CStruct::from_kson(c_struct.to_kson()) {
        //    Ok(CStruct { fu }) => assert_eq!(fu, 1),
        //    Err(_e) => panic!("Couldn't retrieve c-type struct"),
        //}

        // into_kson
        assert_eq!(c_struct.to_kson(), into_kson(c_struct.clone()));
        match crate::encoding::de::from_kson(into_kson(c_struct)) {
            Ok(CStruct { fu, bar: _, baz: _ }) => assert_eq!(fu, 1),
            Err(_e) => panic!("Couldn't retrieve c-type struct"),
        }
    }

    #[test]
    // Test `KsonRep` auto-derive for enum of unit-like structs
    fn unit_enum() {
        #[derive(KSerDe, KsonRep, Clone, Debug)]
        enum UnitEnum {
            Foo,
            Bar,
        }

        use UnitEnum::*;

        dbg!(into_kson(Foo));
        // to_kson
        match de::from_kson(into_kson(Foo)) {
            Ok(Foo) => (),
            _ => panic!("Failed to retrieve unit-like struct"),
        }

        // into_kson
        // match UnitEnum::from_kson(Foo.into_kson()) {
        //    Ok(Foo) => (),
        //    _ => panic!("Failed to retrieve unit-like struct"),
        //}
    }

    #[test]
    // Test `KsonRep` autoderive for enum of named-tuple structs
    fn named_tuple_enum() {
        #[derive(KSerDe, KsonRep, Clone, Debug)]
        enum Named {
            Foo(u8, String),
            Bar(Option<u8>),
        }

        use Named::*;

        let fu = Foo(1, "hello".to_string());

        // to_kson
        match de::from_kson(into_kson(fu)) {
            Ok(Foo(num, string)) => {
                assert_eq!(num, 1);
                assert_eq!(string, "hello".to_string());
            }
            Err(e) => panic!("{}", e),
            _ => panic!("Couldn't retrive tuple-like variant"),
        }

        // into_kson
        // match Named::from_kson(fu.into_kson()) {
        //    Ok(Foo(num, string)) => {
        //        assert_eq!(num, 1);
        //        assert_eq!(&string, "hello");
        //    }
        //    _ => panic!("Couldn't retrieve tuple variant"),
        //}
    }

    // Test `KsonRep` auto-derive for enum of C-style structs
    //#[test]
    // fn c_style_enum() {
    //    #[derive(KSerDe, KsonRep, Clone, Debug)]
    //    enum CStyle {
    //        Foo { num: u8, string: String },
    //        Bar,
    //    }

    //    use CStyle::*;

    //    let fu = Foo {
    //        num:    1,
    //        string: "hello".to_string(),
    //    };

    //    // to_kson
    //    match CStyle::from_kson(fu.to_kson()) {
    //        Ok(Foo { num, string }) => {
    //            assert_eq!(num, 1);
    //            assert_eq!(&string, "hello");
    //        }
    //        _ => panic!("Couldn't retrieve tuple variant"),
    //    }

    //    // into_kson
    //    match CStyle::from_kson(fu.into_kson()) {
    //        Ok(Foo { num, string }) => {
    //            assert_eq!(num, 1);
    //            assert_eq!(&string, "hello");
    //        }
    //        _ => panic!("Couldn't retrieve tuple variant"),
    //    }
    //}
}
