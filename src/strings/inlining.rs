use core::{
    borrow,
    cmp::Ordering,
    convert::Infallible,
    fmt,
    hash::{Hash, Hasher},
    ops,
    str,
};

#[cfg(not(feature = "std"))]
use alloc::{
    borrow::{Cow, ToOwned},
    boxed::Box,
    string::String,
    vec::Vec,
};

#[cfg(feature = "std")]
use std::borrow::Cow;

use super::CappedString;

/// A non-growable string where strings 22 bytes or shorter are stored inline and longer strings
/// use a separate heap allocation. If maximum inline lengths other than 22 are desired, see the
/// more general [InliningString].
///
/// 22 bytes is chosen because it is optimal for 64-bit architectures; the minimum possible size
/// of the data structure on 64-bit architectures which always keeps the data properly aligned is
/// 24 bytes (because, when heap-allocated, the data structure contains a 16-byte `Box<[u8]>` with
/// 8-byte alignment and a 1-byte discriminant, and the greatest multiple of 8 which is ≥17 is 24),
/// and the inline variant needs to use 2 bytes for the length and disciminant.
pub type InliningString22 = InliningString<22>;

/// A non-growable string which stores small strings inline; strings of length less than or equal
/// to `N` are stored inside the data structure itself, whereas strings of length greater than `N`
/// use a separate heap allocation.
///
/// This type is intended to be used when lots of small strings need to be stored, and these
/// strings do not need to grow.
///
/// For 64-bit targets, `N = 22` allows the greatest amount of inline string data to be stored
/// without exceeding the size of a regular [String]. Therefore, [InliningString22] is provided as
/// a type alias for `InliningString<22>`.
///
/// Although `N` is a `usize`, it may be no greater than `u8::MAX`; larger values will result in a
/// compile-time error.
///
/// ```
/// # use libshire::strings::InliningString;
/// let s1 = InliningString::<22>::new("Hello, InliningString!");
/// assert_eq!(&*s1, "Hello, InliningString!");
/// assert!(!s1.heap_allocated());
///
/// let s2 = InliningString::<22>::new("This string is 23 bytes");
/// assert_eq!(&*s2, "This string is 23 bytes");
/// assert!(s2.heap_allocated());
/// ```
#[derive(Clone)]
pub struct InliningString<const N: usize>(Repr<N>);

impl<const N: usize> InliningString<N> {
    /// Creates a new `InliningString` from the given string, storing the string data inline if
    /// possible or creating a new heap allocation otherwise.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s = InliningString::<22>::new("Hello, InliningString!");
    /// assert_eq!(&*s, "Hello, InliningString!");
    /// ```
    #[inline]
    #[must_use]
    pub fn new<S>(s: S) -> Self
    where
        S: AsRef<str>,
        Box<str>: From<S>,
    {
        match CappedString::new(&s) {
            Ok(buf) => Self(Repr::Inline(buf)),
            Err(_) => Self(Repr::Boxed(Box::<str>::from(s))),
        }
    }

    /// Returns a new empty `InliningString`.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s = InliningString::<22>::empty();
    /// assert_eq!(&*s, "");
    /// ```
    #[inline]
    #[must_use]
    pub const fn empty() -> Self {
        Self(Repr::Inline(CappedString::empty()))
    }

    /// Returns a string slice for the underlying string data.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self(Repr::Inline(buf)) => buf,
            Self(Repr::Boxed(buf)) => buf,
        }
    }

    /// Returns a mutable string slice for the underlying string data.
    #[inline]
    #[must_use]
    pub fn as_str_mut(&mut self) -> &mut str {
        match self {
            Self(Repr::Inline(buf)) => buf,
            Self(Repr::Boxed(buf)) => buf,
        }
    }

    #[inline]
    #[must_use]
    pub fn into_boxed_str(self) -> Box<str> {
        match self {
            Self(Repr::Inline(buf)) => buf.into_boxed_str(),
            Self(Repr::Boxed(buf)) => buf,
        }
    }

    /// Consumes the `InliningString` and converts it to a heap-allocated `String`.
    #[inline]
    #[must_use]
    pub fn into_string(self) -> String {
        match self {
            Self(Repr::Inline(buf)) => buf.into_string(),
            Self(Repr::Boxed(buf)) => buf.into_string(),
        }
    }

    /// Returns the length of the string in bytes.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s = InliningString::<22>::new("こんにちは");
    /// assert_eq!(s.len(), 15);
    /// ```
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            Self(Repr::Inline(buf)) => buf.len(),
            Self(Repr::Boxed(buf)) => buf.len(),
        }
    }

    /// Returns `true` if the string has length 0.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s1 = InliningString::<22>::new("");
    /// assert!(s1.is_empty());
    ///
    /// let s2 = InliningString::<22>::new("Hello");
    /// assert!(!s2.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        match self {
            Self(Repr::Inline(buf)) => buf.is_empty(),
            Self(Repr::Boxed(buf)) => buf.is_empty(),
        }
    }

    /// Returns `true` if the string data is stored on the heap, and `false` otherwise.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s1 = InliningString::<22>::new("This string's 22 bytes");
    /// assert!(!s1.heap_allocated());
    ///
    /// let s2 = InliningString::<22>::new("This string is 23 bytes");
    /// assert!(s2.heap_allocated());
    /// ```
    #[inline]
    #[must_use]
    pub fn heap_allocated(&self) -> bool {
        match self {
            Self(Repr::Inline(_)) => false,
            Self(Repr::Boxed(_)) => true,
        }
    }
}

impl<const N: usize> Default for InliningString<N> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

impl<const N: usize> ops::Deref for InliningString<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> ops::DerefMut for InliningString<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_str_mut()
    }
}

impl<const N: usize> AsRef<str> for InliningString<N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> AsMut<str> for InliningString<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> borrow::Borrow<str> for InliningString<N> {
    #[inline]
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> borrow::BorrowMut<str> for InliningString<N> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        self
    }
}

impl<'a, const N: usize> From<&'a str> for InliningString<N> {
    #[inline]
    fn from(s: &'a str) -> Self {
        Self::new(s)
    }
}

impl<const N: usize> From<String> for InliningString<N> {
    #[inline]
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

impl<'a, const N: usize> From<Cow<'a, str>> for InliningString<N> {
    #[inline]
    fn from(s: Cow<'a, str>) -> Self {
        Self::new(s)
    }
}

impl<const N: usize> From<InliningString<N>> for String {
    #[inline]
    fn from(s: InliningString<N>) -> Self {
        s.into_string()
    }
}

impl<const N: usize, const M: usize> PartialEq<InliningString<M>> for InliningString<N> {
    #[inline]
    fn eq(&self, other: &InliningString<M>) -> bool {
        **self == **other
    }
}

impl<const N: usize> Eq for InliningString<N> {}

impl<const N: usize, const M: usize> PartialOrd<InliningString<M>> for InliningString<N> {
    #[inline]
    fn partial_cmp(&self, other: &InliningString<M>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<const N: usize> Ord for InliningString<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<const N: usize> Hash for InliningString<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<const N: usize> str::FromStr for InliningString<N> {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s))
    }
}

impl<const N: usize> fmt::Debug for InliningString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for InliningString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[cfg(feature = "serde")]
impl<const N: usize> serde::Serialize for InliningString<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serde::Serialize::serialize(&**self, serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> serde::Deserialize<'de> for InliningString<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::{Error, Unexpected, Visitor};

        struct InliningStringVisitor<const N: usize>;

        impl<'de, const N: usize> Visitor<'de> for InliningStringVisitor<N> {
            type Value = InliningString<N>;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a string")
            }

            fn visit_str<E: Error>(self, v: &str) -> Result<Self::Value, E> {
                Ok(Self::Value::new(v))
            }

            fn visit_string<E: Error>(self, v: String) -> Result<Self::Value, E> {
                Ok(Self::Value::new(v))
            }

            fn visit_bytes<E: Error>(self, v: &[u8]) -> Result<Self::Value, E> {
                str::from_utf8(v)
                    .map(Self::Value::new)
                    .map_err(|_| Error::invalid_value(Unexpected::Bytes(v), &self))
            }

            fn visit_byte_buf<E: Error>(self, v: Vec<u8>) -> Result<Self::Value, E> {
                String::from_utf8(v)
                    .map(Self::Value::new)
                    .map_err(|err| {
                        Error::invalid_value(Unexpected::Bytes(&err.into_bytes()), &self)
                    })
            }
        }

        deserializer.deserialize_string(InliningStringVisitor)
    }
}

#[derive(Clone)]
enum Repr<const N: usize> {
    Inline(CappedString<N>),
    Boxed(Box<str>),
}

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "std"))]
    use alloc::borrow::{Cow, ToOwned};

    #[cfg(feature = "std")]
    use std::borrow::Cow;

    use super::{InliningString, InliningString22};

    #[test]
    fn test_new() {
        let test_strings = [
            "",
            "Hello",
            "Somethingfortheweekend",
            "Dichlorodifluoromethane",
            "こんにちは",
            "❤️🧡💛💚💙💜",
        ];

        for s in test_strings {
            let buf = s.to_owned();
            let borrowed = Cow::Borrowed(s);
            let owned = Cow::<'static, str>::Owned(buf.clone());

            assert_eq!(InliningString22::new(s).as_str(), s);
            assert_eq!(InliningString22::new(buf).as_str(), s);
            assert_eq!(InliningString22::new(borrowed).as_str(), s);
            assert_eq!(InliningString22::new(owned).as_str(), s);
        }
    }

    #[test]
    fn test_as_str_mut() {
        let mut s1 = InliningString22::new("hello");
        s1.as_str_mut().make_ascii_uppercase();
        assert_eq!(s1.as_str(), "HELLO");

        let mut s2 = InliningString22::new("the quick brown fox jumps over the lazy dog");
        s2.as_str_mut().make_ascii_uppercase();
        assert_eq!(s2.as_str(), "THE QUICK BROWN FOX JUMPS OVER THE LAZY DOG");
    }

    #[test]
    fn test_len() {
        assert_eq!(InliningString22::new("").len(), 0);
        assert_eq!(InliningString22::new("Hello").len(), 5);
        assert_eq!(InliningString22::new("Somethingfortheweekend").len(), 22);
        assert_eq!(InliningString22::new("Dichlorodifluoromethane").len(), 23);
        assert_eq!(InliningString22::new("こんにちは").len(), 15);
        assert_eq!(InliningString22::new("❤️🧡💛💚💙💜").len(), 26);
    }

    #[test]
    fn test_heap_allocated() {
        assert!(!InliningString22::new("").heap_allocated());
        assert!(!InliningString22::new("Hello").heap_allocated());
        assert!(!InliningString22::new("Somethingfortheweekend").heap_allocated());
        assert!(!InliningString22::new("こんにちは").heap_allocated());

        assert!(InliningString22::new("Dichlorodifluoromethane").heap_allocated());
        assert!(InliningString22::new("Squishedbuginsidethescreen").heap_allocated());
        assert!(InliningString22::new("❤️🧡💛💚💙💜").heap_allocated());
    }

    #[test]
    fn test_zero_capacity() {
        assert_eq!(InliningString::<0>::new("").as_str(), "");
        assert!(!InliningString::<0>::new("").heap_allocated());
        assert_eq!(InliningString::<0>::new("a").as_str(), "a");
        assert!(InliningString::<0>::new("a").heap_allocated());
        assert_eq!(InliningString::<0>::new("Hello").as_str(), "Hello");
        assert!(InliningString::<0>::new("Hello").heap_allocated());
    }
}
