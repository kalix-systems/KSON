use crate::{util::*, vecmap::*, *};
use bytes::Bytes;
use hashbrown::HashMap;
use std::{
    fmt::Debug,
    net::{Ipv4Addr, SocketAddrV4},
    vec::{IntoIter, Vec},
};

/// A value representable as `Kson`.
pub trait KsonRep: Clone + Sized {
    /// Converts value into `Kson`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::rep::*;
    ///
    /// let k_num = 1.to_kson();
    /// ```
    fn to_kson(&self) -> Kson { self.clone().into_kson() }

    /// Consumes value, converting it into kson.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::rep::*;
    ///
    /// let k_num = 1.into_kson();
    /// ```
    fn into_kson(self) -> Kson { self.to_kson() }

    /// Converts value from `Kson`.
    ///
    /// # Arguments
    ///
    /// `ks: Kson` - The value to be converted from `Kson`.
    ///
    /// # Example
    ///
    /// ```
    /// use kson::rep::*;
    ///
    /// let k_num = "foo".to_string().into_kson();
    ///
    /// assert_eq!(String::from_kson(k_num).unwrap(), "foo");
    /// ```
    fn from_kson(ks: Kson) -> Option<Self>;
}

macro_rules! chain_try_from {
    ($e: expr) => { $e.and_then(|x| x.try_into().map_err(|_| ())) };
    ($e: expr, $i: tt) => {
        chain_try_from!($e.and_then(|x| $i::try_from(x).map_err(|_| ())))
    };
    ($e: expr, $i: tt, $($is:tt)*) => {
        chain_try_from!($e.and_then(|x| $i::try_from(x).map_err(|_| ())), $($is)*)
    };
}

#[macro_export]
macro_rules! try_from_kson {
    ($t: ty) => {
        impl TryFrom<Kson> for $t {
            type Error = ();
            fn try_from(ks: Kson) -> Result<$t, ()> {
                ks.try_into().map_err(|_| ())
            }
        }
    };
    ($t: ty, $($is:tt)*) => {
        impl TryFrom<Kson> for $t {
            type Error = ();
            fn try_from(ks: Kson) -> Result<$t, ()> {
                chain_try_from!(Ok(ks), $($is)*)
            }
        }
    };
}

try_from_kson!(i64, Inum);
try_from_kson!(u64, Inum);

try_from_kson!(u8, Inum, i64);
try_from_kson!(u16, Inum, i64);
try_from_kson!(u32, Inum, i64);
try_from_kson!(i8, Inum, i64);
try_from_kson!(i16, Inum, i64);
try_from_kson!(i32, Inum, i64);

macro_rules! try_from_kson_rep {
    ($t:ty) => {
        impl KsonRep for $t {
            fn into_kson(self) -> Kson { self.into() }

            fn from_kson(ks: Kson) -> Option<Self> { ks.try_into().ok() }
        }
    };
}

try_from_kson_rep!(Kson);
try_from_kson_rep!(bool);
try_from_kson_rep!(u8);
try_from_kson_rep!(u16);
try_from_kson_rep!(u32);
try_from_kson_rep!(u64);
try_from_kson_rep!(i8);
try_from_kson_rep!(i16);
try_from_kson_rep!(i32);
try_from_kson_rep!(i64);
try_from_kson_rep!(Inum);
try_from_kson_rep!(Bytes);

impl KsonRep for String {
    fn into_kson(self) -> Kson { Byt(Bytes::from(self.into_bytes())) }

    fn to_kson(&self) -> Kson { Byt(Bytes::from(self.as_bytes())) }

    fn from_kson(ks: Kson) -> Option<Self> {
        String::from_utf8(Bytes::from_kson(ks)?.to_vec()).ok()
    }
}

impl<T: KsonRep> KsonRep for Vec<T> {
    fn into_kson(self) -> Kson { Array(self.into_iter().map(T::into_kson).collect()) }

    fn to_kson(&self) -> Kson { Array(self.iter().map(T::to_kson).collect()) }

    fn from_kson(ks: Kson) -> Option<Self> {
        ks.into_vec()?.into_iter().map(T::from_kson).collect()
    }
}

impl<T: KsonRep> KsonRep for VecMap<Bytes, T> {
    fn into_kson(self) -> Kson {
        Map(VecMap::from_sorted(
            self.into_iter().map(|(k, v)| (k, v.into_kson())).collect(),
        ))
    }

    fn to_kson(&self) -> Kson { Map(self.iter().map(|(k, v)| (k.clone(), v.to_kson())).collect()) }

    fn from_kson(ks: Kson) -> Option<Self> {
        let vm = ks.into_vecmap()?;
        let mut out = Vec::with_capacity(vm.len());
        for (k, v) in vm {
            out.push((k, T::from_kson(v)?));
        }
        Some(VecMap::from_sorted(out))
    }
}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonRep for HashMap<Bytes, T, S> {
    fn into_kson(self) -> Kson { Map(self.into_iter().map(|(k, v)| (k, v.into_kson())).collect()) }

    fn to_kson(&self) -> Kson { Map(self.iter().map(|(k, v)| (k.clone(), v.to_kson())).collect()) }

    fn from_kson(ks: Kson) -> Option<Self> {
        ks.into_vecmap()?
            .into_iter()
            .map(|(k, v)| Some((k, T::from_kson(v)?)))
            .collect()
    }
}

impl KsonRep for () {
    fn into_kson(self) -> Kson { Array(vec![]) }

    fn from_kson(ks: Kson) -> Option<()> {
        if ks.into_vec()?.is_empty() {
            Some(())
        } else {
            None
        }
    }
}

impl<A: KsonRep, B: KsonRep> KsonRep for (A, B) {
    fn into_kson(self) -> Kson { Array(vec![self.0.into_kson(), self.1.into_kson()]) }

    fn from_kson(ks: Kson) -> Option<Self> {
        let arr = ks.into_vec()?;
        if arr.len() == 2 {
            let mut iter = arr.into_iter();
            let k1 = iter.next()?;
            let k2 = iter.next()?;
            Some((A::from_kson(k1)?, B::from_kson(k2)?))
        } else {
            None
        }
    }
}

impl<A: KsonRep, B: KsonRep, C: KsonRep> KsonRep for (A, B, C) {
    fn into_kson(self) -> Kson {
        Array(vec![
            self.0.into_kson(),
            self.1.into_kson(),
            self.2.into_kson(),
        ])
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let arr = ks.into_vec()?;
        if arr.len() == 3 {
            let mut iter = arr.into_iter();
            let k1 = iter.next().unwrap();
            let k2 = iter.next().unwrap();
            let k3 = iter.next().unwrap();
            Some((A::from_kson(k1)?, B::from_kson(k2)?, C::from_kson(k3)?))
        } else {
            None
        }
    }
}
impl<A: KsonRep, B: KsonRep, C: KsonRep, D: KsonRep> KsonRep for (A, B, C, D) {
    fn into_kson(self) -> Kson {
        Array(vec![
            self.0.into_kson(),
            self.1.into_kson(),
            self.2.into_kson(),
            self.3.into_kson(),
        ])
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let arr = ks.into_vec()?;
        if arr.len() == 4 {
            let mut iter = arr.into_iter();
            let k1 = iter.next().unwrap();
            let k2 = iter.next().unwrap();
            let k3 = iter.next().unwrap();
            let k4 = iter.next().unwrap();
            Some((
                A::from_kson(k1)?,
                B::from_kson(k2)?,
                C::from_kson(k3)?,
                D::from_kson(k4)?,
            ))
        } else {
            None
        }
    }
}

impl<T: KsonRep> KsonRep for Option<T> {
    fn into_kson(self) -> Kson {
        match self {
            Some(x) => Array(vec![x.into_kson()]),
            None => Null,
        }
    }

    fn to_kson(&self) -> Kson {
        match self {
            Some(x) => Array(vec![x.to_kson()]),
            _ => Null,
        }
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        match ks {
            Null => Some(None),
            Array(v) => {
                let mut iter = v.into_iter();
                let val = iter.next()?;
                if iter.next().is_none() {
                    Some(Some(T::from_kson(val)?))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl KsonRep for Ipv4Addr {
    fn into_kson(self) -> Kson {
        let octs = self.octets();
        Bytes::from(&[octs[0], octs[1], octs[2], octs[3]] as &[u8]).into_kson()
    }

    fn from_kson(ks: Kson) -> Option<Self> {
        let bs: Bytes = KsonRep::from_kson(ks)?;
        if bs.len() != 4 {
            None
        } else {
            Some(Ipv4Addr::new(bs[0], bs[1], bs[2], bs[3]))
        }
    }
}

impl KsonRep for SocketAddrV4 {
    fn into_kson(self) -> Kson { (*self.ip(), self.port()).into_kson() }

    fn from_kson(ks: Kson) -> Option<Self> {
        let (ip, port) = KsonRep::from_kson(ks)?;
        Some(SocketAddrV4::new(ip, port))
    }
}

/// Manually specify how the fields of a struct should be converted to `Kson`. Usually,
/// you should just add `#[derive(KsonRep)]` to your struct definition instead of doing it
/// manually.
///
/// # Arguments
///
/// * `entries: Vec<&str, Kson>` - A veconstructor of pairs containing the name of the
///   field and the value.
///
/// # Examples
///
/// An example using `#[derive(KsonRep)]`.
///
/// ```
/// use kson::{kson_macro::*, rep::*, Kson};
///
/// #[derive(KsonRep, Clone)]
/// /// This is a silly struct.
/// struct SillyStruct {
///     foo: String,
///     bar: u8,
/// }
///
/// /// This is an example using a silly struct.
/// let example = SillyStruct {
///     foo: "hello world".to_string(),
///     bar: 0,
/// };
///
/// /// Here, in the spirit of the silly struct, we convert it to and from `Kson`.
/// let extracted = SillyStruct::from_kson(example.to_kson()).unwrap();
///
/// assert_eq!(extracted.foo, example.foo);
/// assert_eq!(extracted.bar, example.bar);
/// ```
///
/// An example of how this might be done manually.
///
/// ```
/// use kson::{rep::*, Kson};
///
/// #[derive(Clone)]
/// /// This is, again, a silly struct.
/// struct SillyStruct {
///     foo: String,
///     bar: u8,
/// }
///
/// // Implement `KsonRep`.
/// impl KsonRep for SillyStruct {
///     fn to_kson(&self) -> Kson {
///         struct_to_kson_helper(vec![
///             ("foo", self.foo.to_kson()),
///             ("bar", self.bar.to_kson()),
///         ])
///     }
///
///     fn from_kson(ks: Kson) -> Option<SillyStruct> {
///         // did `struct_from_kson_helper` return `None`?
///         match struct_from_kson_helper(ks, &["foo", "bar"]) {
///             Some(vec) => {
///                 Some(SillyStruct {
///                     // did this `from_kson` return `None`?
///                     foo: match String::from_kson(vec[0].clone()) {
///                         Some(val) => val,
///                         None => return None,
///                     },
///                     // what about this one?
///                     bar: match u8::from_kson(vec[1].clone()) {
///                         Some(val) => val,
///                         None => return None,
///                     },
///                 })
///             }
///             // all is lost
///             None => None,
///         }
///     }
/// }
///
/// let example = SillyStruct {
///     foo: "hello world".to_string(),
///     bar: 0,
/// };
///
/// // this example is even more in the spirit of the silly struct
/// let extracted = SillyStruct::from_kson(example.to_kson()).unwrap();
///
/// assert_eq!(extracted.foo, example.foo);
/// assert_eq!(extracted.bar, example.bar);
/// ```
///
/// If you find this tedious and repetitive (we do), please see the previous example.
pub fn struct_to_kson_helper(entries: Vec<(&str, Kson)>) -> Kson {
    let vm: VecMap<Bytes, Kson> = entries
        .into_iter()
        .map(|(k, v)| (str_to_bs(k), v))
        .collect();
    Kson::from(vm)
}

/// Manually specify how the fields a struct should be read from `Kson`. Usually, you
/// should just add `#[derive(KsonRep)]` to your struct definition instead of doing it
/// manually. See `struct_to_kson_helper` for an example of usage.
///
/// # Arguments
///
/// * `ks: Kson` - The `Kson` value containg the struct data.
/// * `names: &[&str]` - The names of the fields in the order they are to be extracted.
pub fn struct_from_kson_helper(ks: Kson, names: &[&str]) -> Option<Vec<Kson>> {
    let m = ks.into_map()?;
    let outs: Vec<Kson> = names
        .iter()
        .filter_map(|n| m.get(&str_to_bs(n)).cloned())
        .collect();
    if outs.len() == names.len() && outs.len() == m.len() {
        Some(outs)
    } else {
        None
    }
}

/// Helper function to manually specify how the variants an enum should be converted to
/// `Kson`. Usually, you should just add `#[derive(KsonRep)]` to your enum definition
/// instead of doing it manually.
///
/// # Arguments
///
/// * `name: &str` - The name of the enum variant.
/// * `fields: Vec<Kson>` - The corresponding values.
///
/// # Examples
///
/// An example using `#[derive(KsonRep)]`.
///
/// ```
/// use kson::{kson_macro::*, rep::*, Kson};
///
/// // Note: You need to derive `Clone` and `Debug` for the auto-derive to work.
/// #[derive(Clone, KsonRep, Debug)]
/// /// This is a silly enum. It has no purpose in life beyond being used for an example.
/// enum SillyEnum {
///     Foo(String),
///     Bar(String, u8),
/// }
///
/// use SillyEnum::*;
///
/// let foo = Foo("hello".to_string());
/// let bar = Bar("world".to_string(), 1);
///
/// /// Returns the `String` inside `Foo` if the value is
/// /// indeed a `Foo`, otherwise returns `None`.
/// fn foo_or_none(maybe_foo: SillyEnum) -> Option<String> {
///     match maybe_foo {
///         Foo(s) => Some(s), // Great! We got some `Foo`. It's what I always wanted.
///         Bar(_, _) => None, // It's not a `Foo`! All is lost. I must rethink my life.
///     }
/// }
///
/// let extract_foo = SillyEnum::from_kson(foo.to_kson()).unwrap();
///
/// assert_eq!(foo_or_none(extract_foo).unwrap(), "hello".to_string());
/// ```
///
/// An example example of how this might be done manually.
///
/// ```
/// use kson::{rep::*, Kson};
/// use std::vec::IntoIter;
///
/// #[derive(Clone, Debug)]
/// /// This, again, a silly enum.
/// enum SillyEnum {
///     Foo(String),
///     Bar(String, u8),
/// }
///
/// use SillyEnum::*;
///
/// // Implement `KsonRep`.
/// impl KsonRep for SillyEnum {
///     fn to_kson(&self) -> Kson {
///         match self {
///             Foo(string) => enum_to_kson_helper("Foo", vec![string.to_kson()]),
///             Bar(string, num) => {
///                 enum_to_kson_helper("Bar", vec![string.to_kson(), num.to_kson()])
///             }
///         }
///     }
///
///     fn from_kson(ks: Kson) -> Option<SillyEnum> {
///         let fns: Vec<(&str, Box<FnMut(IntoIter<Kson>) -> Option<SillyEnum>>)> = vec![
///             (
///                 "Foo",
///                 Box::new(|mut iter: IntoIter<Kson>| -> Option<SillyEnum> {
///                     let string = pop_kson(&mut iter)?;
///                     if iter.next().is_none() {
///                         Some(Foo(string))
///                     } else {
///                         None
///                     }
///                 }),
///             ),
///             (
///                 "Bar",
///                 Box::new(|mut iter: IntoIter<Kson>| -> Option<SillyEnum> {
///                     let string = pop_kson(&mut iter)?;
///                     let num = pop_kson(&mut iter)?;
///                     if iter.next().is_none() {
///                         Some(Bar(string, num))
///                     } else {
///                         None
///                     }
///                 }),
///             ),
///         ];
///
///         match enum_from_kson_helper(ks, fns) {
///             Some(value) => Some(value),
///             None => None,
///         }
///     }
/// }
/// ```
pub fn enum_to_kson_helper(name: &str, mut fields: Vec<Kson>) -> Kson {
    fields.insert(0, Kson::from(str_to_bs(name)));
    Array(fields)
}

/// Manually specify how the variants an enum should be read from `Kson`. Usually, you
/// should just add `#[derive(KsonRep)]` to your enum definition instead of doing it
/// manually.
pub fn enum_from_kson_helper<T: Debug>(
    ks: Kson,
    fns: Vec<(&str, Box<FnMut(IntoIter<Kson>) -> Option<T>>)>,
) -> Option<T> {
    let mut fields = ks.into_vec()?.into_iter();

    let constructor: Bytes = fields.next()?.try_into().ok()?;
    for (name, mut f) in fns {
        if constructor == str_to_bs(name) {
            return f(fields);
        }
    }
    None
}

/// Gets the next element from an iterator of `Kson` values as `T`.
///
/// # Arguments
///
/// * `iter: &mut IntoIter<Kson>` - An interator of `Kson` values to be converted into
///   `T`.
///
/// # Example
///
/// ```
/// use kson::{rep::*, Kson};
///
/// let ks_values = vec![1, 2, 3].into_kson().into_vec().unwrap();
///
/// let first: u8 = pop_kson(&mut ks_values.into_iter()).unwrap();
/// assert_eq!(first, 1);
/// ```
pub fn pop_kson<T: KsonRep>(iter: &mut IntoIter<Kson>) -> Option<T> {
    KsonRep::from_kson(iter.next()?)
}

/// Values whose KSON representation is never `Null`.
pub trait KsonNotNull: KsonRep {}
// impl KsonNotNull for u8 {}
// impl KsonNotNull for u16 {}
// impl KsonNotNull for u32 {}
// impl KsonNotNull for u64 {}
// impl KsonNotNull for i8 {}
// impl KsonNotNull for i16 {}
// impl KsonNotNull for i32 {}
// impl KsonNotNull for i64 {}
// impl KsonNotNull for Bytes {}
impl<T: KsonRep> KsonNotNull for Vec<T> {}

impl<T: KsonRep, S: ::std::hash::BuildHasher + Default + Clone> KsonNotNull
    for HashMap<Bytes, T, S>
{
}
impl KsonNotNull for () {}
impl<A: KsonRep, B: KsonRep> KsonNotNull for (A, B) {}
impl<A: KsonRep, B: KsonRep, C: KsonRep> KsonNotNull for (A, B, C) {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kson_macro::*;

    #[test]
    // Test `KsonRep` autoderive for unit-like struct
    fn unit_struct() {
        #[derive(KsonRep, Clone)]
        struct UnitStruct;

        // to_kson
        match UnitStruct::from_kson(UnitStruct.to_kson()) {
            Some(UnitStruct) => (),
            None => panic!("Couldn't retrieve unit struct"),
        }

        // into_kson
        match UnitStruct::from_kson(UnitStruct.into_kson()) {
            Some(UnitStruct) => (),
            None => panic!("Couldn't retrieve unit struct"),
        }
    }

    #[test]
    // Test `KsonRep` autoderive for C-style struct
    fn c_struct() {
        #[derive(KsonRep, Clone)]
        struct CStruct {
            foo: u8,
        };

        let c_struct = CStruct { foo: 1 };

        // to_kson
        match CStruct::from_kson(c_struct.to_kson()) {
            Some(CStruct { foo }) => assert_eq!(foo, 1),
            None => panic!("Couldn't retrieve c-type struct"),
        }

        // into_kson
        match CStruct::from_kson(c_struct.into_kson()) {
            Some(CStruct { foo }) => assert_eq!(foo, 1),
            None => panic!("Couldn't retrieve c-type struct"),
        }
    }

    #[test]
    // Test `KsonRep` autoderive for enum of named-tuple structs
    fn named_tuple_enum() {
        #[derive(KsonRep, Clone, Debug)]
        enum Named {
            Foo(u8, String),
            Bar(u8),
        }

        use Named::*;

        let foo = Foo(1, "hello".to_string());

        // to_kson
        match Named::from_kson(foo.to_kson()) {
            Some(Foo(num, string)) => {
                assert_eq!(num, 1);
                assert_eq!(string, "hello".to_string());
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }

        // into_kson
        match Named::from_kson(foo.into_kson()) {
            Some(Foo(num, string)) => {
                assert_eq!(num, 1);
                assert_eq!(&string, "hello");
            }
            _ => panic!("Couldn't retrieve tuple variant"),
        }
    }

    #[test]
    // Test `KsonRep` autoderive for enum of unit-like structs
    fn unit_enum() {
        #[derive(KsonRep, Clone, Debug)]
        enum UnitEnum {
            Foo,
            Bar(u8),
        }

        use UnitEnum::*;

        // to_kson
        match UnitEnum::from_kson(Foo.to_kson()) {
            Some(Foo) => (),
            _ => panic!("Failed to retrieve unit-like struct"),
        }

        // into_kson
        match UnitEnum::from_kson(Foo.into_kson()) {
            Some(Foo) => (),
            _ => panic!("Failed to retrieve unit-like struct"),
        }
    }

    // TODO extend macro to support these cases
    #[test]
    /// Test `KsonRep` autoderive for named-tuple struct
    fn named_tuple() {
        #[derive(KsonRep, Clone, Debug)]
        struct Foo(u8, String);

        match Foo::from_kson(Foo(1, "hello".to_string()).to_kson()) {
            Some(Foo(num, s)) => {
                assert_eq!(num, 1);
                assert_eq!(s, "hello".to_string());
            }
            _ => panic!("No Foo"),
        }
    }

    // // Test `KsonRep` autoderive for enum of named-tuple structs
    // fn c_type_enum() {
    //    #[derive(KsonRep, Clone, Debug)]
    //    enum CType {
    //        Foo { num: u8, string: String },
    //        Bar,
    //    }

    //    use CType::*;

    //    let foo = Foo {
    //        num:    1,
    //        string: "hello".to_string(),
    //    };

    //    // to_kson
    //    match CType::from_kson(foo.to_kson()) {
    //        Some(Foo(num, string)) => {
    //            assert_eq!(num, 1);
    //            assert_eq!(&string, "hello");
    //        }
    //        _ => panic!("Couldn't retrieve tuple variant"),
    //    }

    //    // into_kson
    //    match Named::from_kson(foo.into_kson()) {
    //        Some(Foo(num, string)) => {
    //            assert_eq!(num, 1);
    //            assert_eq!(&string, "hello");
    //        }
    //        _ => panic!("Couldn't retrieve tuple variant"),
    //    }
    // }

}
