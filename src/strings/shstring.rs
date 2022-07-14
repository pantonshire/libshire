use std::{
    borrow::{self, Cow},
    cmp::Ordering,
    convert::Infallible,
    fmt,
    hash::{Hash, Hasher},
    ops,
    str::FromStr,
};

use super::InlineString;

/// A non-growable string where strings 22 bytes or shorter are stored on the stack and longer
/// strings are stored on the heap.
/// 
/// 22 bytes is chosen because it is optimal for 64-bit architectures; the minimum possible size
/// of the data structure on 64-bit architectures which always keeps the data properly aligned is
/// 24 bytes (because, when heap-allocated, the data structure contains a 16-byte `Box<[u8]>` with
/// 8-byte alignment and a 1-byte discriminant, and the greatest multiple of 8 which is ≥17 is 24),
/// and the stack-allocated variant needs to store 2 extra bytes for the length and disciminant.
pub type ShString22 = ShString<22>;

/// A non-growable string which may be allocated either on the stack or on the heap; strings `N`
/// bytes or shorter will be allocated on the stack, while strings longer than `N` bytes will be
/// allocated on the heap. Intended to be used when lots of small strings need to be stored, and
/// these strings do not need to grow.
/// 
/// `N` must be less than or equal to `u8::MAX`. Exceeding this limit will cause a compile-time
/// error. Clearly it be better for `N` to be a `u8` rather than a `usize`, but this is
/// unfortunately not possible due to limitations of const generics.
#[derive(Clone)]
pub struct ShString<const N: usize>(Repr<N>);

impl<const N: usize> ShString<N> {
    #[inline]
    #[must_use]
    pub const fn empty() -> Self {
        Self(Repr::Inline(InlineString::empty()))
    }

    /// Creates a new `ShString` from the given string slice, putting it on the stack if possible
    /// or creating a new heap allocation otherwise.
    #[inline]
    #[must_use]
    pub fn new<S>(s: S) -> Self
    where
        S: AsRef<str>,
        Box<str>: From<S>,
    {
        match InlineString::new(&s) {
            Ok(stack_buf) => Self(Repr::Inline(stack_buf)),
            Err(_) => Self(Repr::Boxed(Box::<str>::from(s))),
        }
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

    /// Consumes the `ShString` and converts it to a heap-allocated `String`.
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
    /// # use libshire::strings::ShString;
    /// let s = ShString::<22>::new("こんにちは");
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
    /// # use libshire::strings::ShString;
    /// let s1 = ShString::<22>::new("");
    /// assert!(s1.is_empty());
    /// 
    /// let s2 = ShString::<22>::new("Hello");
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
    /// # use libshire::strings::ShString;
    /// let s1 = ShString::<22>::new("This string's 22 bytes");
    /// assert!(!s1.heap_allocated());
    /// 
    /// let s2 = ShString::<22>::new("This string is 23 bytes");
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

impl<const N: usize> Default for ShString<N> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

impl<const N: usize> ops::Deref for ShString<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> ops::DerefMut for ShString<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_str_mut()
    }
}

impl<const N: usize> AsRef<str> for ShString<N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> AsMut<str> for ShString<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> borrow::Borrow<str> for ShString<N> {
    #[inline]
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> borrow::BorrowMut<str> for ShString<N> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        self
    }
}

impl<'a, const N: usize> From<&'a str> for ShString<N> {
    #[inline]
    fn from(s: &'a str) -> Self {
        Self::new(s)
    }
}

impl<const N: usize> From<String> for ShString<N> {
    #[inline]
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

impl<'a, const N: usize> From<Cow<'a, str>> for ShString<N> {
    #[inline]
    fn from(s: Cow<'a, str>) -> Self {
        Self::new(s)
    }
}

impl<const N: usize> From<ShString<N>> for String {
    #[inline]
    fn from(s: ShString<N>) -> Self {
        s.into_string()
    }
}

impl<const N: usize, const M: usize> PartialEq<ShString<M>> for ShString<N> {
    #[inline]
    fn eq(&self, other: &ShString<M>) -> bool {
        **self == **other
    }
}

impl<const N: usize> Eq for ShString<N> {}

impl<const N: usize, const M: usize> PartialOrd<ShString<M>> for ShString<N> {
    #[inline]
    fn partial_cmp(&self, other: &ShString<M>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<const N: usize> Ord for ShString<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<const N: usize> Hash for ShString<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<const N: usize> FromStr for ShString<N> {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s))
    }
}

impl<const N: usize> fmt::Debug for ShString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for ShString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[cfg(feature = "serde")]
impl<const N: usize> serde::Serialize for ShString<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer
    {
        serde::Serialize::serialize(&**self, serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> serde::Deserialize<'de> for ShString<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>
    {
        serde::Deserialize::deserialize(deserializer)
            .map(Self::new::<&'de str>)
    }
}

#[derive(Clone)]
enum Repr<const N: usize> {
    Inline(InlineString<N>),
    Boxed(Box<str>),
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use super::{ShString, ShString22};

    #[test]
    fn test_new() {
        let test_strings = [
            "",
            "Hello",
            "Somethingfortheweekend",
            "Dichlorodifluoromethane",
            "こんにちは",
            "❤️🧡💛💚💙💜"
        ];

        for s in test_strings {
            let buf = s.to_owned();
            let borrowed = Cow::Borrowed(s);
            let owned = Cow::<'static, str>::Owned(buf.clone());

            assert_eq!(ShString22::new(s).as_str(), s);
            assert_eq!(ShString22::new(buf).as_str(), s);
            assert_eq!(ShString22::new(borrowed).as_str(), s);
            assert_eq!(ShString22::new(owned).as_str(), s);
        }
    }

    #[test]
    fn test_as_str_mut() {
        let mut s1 = ShString22::new("hello");
        s1.as_str_mut().make_ascii_uppercase();
        assert_eq!(s1.as_str(), "HELLO");

        let mut s2 = ShString22::new("the quick brown fox jumps over the lazy dog");
        s2.as_str_mut().make_ascii_uppercase();
        assert_eq!(s2.as_str(), "THE QUICK BROWN FOX JUMPS OVER THE LAZY DOG");
    }

    #[test]
    fn test_len() {
        assert_eq!(ShString22::new("").len(), 0);
        assert_eq!(ShString22::new("Hello").len(), 5);
        assert_eq!(ShString22::new("Somethingfortheweekend").len(), 22);
        assert_eq!(ShString22::new("Dichlorodifluoromethane").len(), 23);
        assert_eq!(ShString22::new("こんにちは").len(), 15);
        assert_eq!(ShString22::new("❤️🧡💛💚💙💜").len(), 26);
    }

    #[test]
    fn test_heap_allocated() {
        assert!(!ShString22::new("").heap_allocated());
        assert!(!ShString22::new("Hello").heap_allocated());
        assert!(!ShString22::new("Somethingfortheweekend").heap_allocated());
        assert!(!ShString22::new("こんにちは").heap_allocated());

        assert!(ShString22::new("Dichlorodifluoromethane").heap_allocated());
        assert!(ShString22::new("Squishedbuginsidethescreen").heap_allocated());
        assert!(ShString22::new("❤️🧡💛💚💙💜").heap_allocated());
    }

    #[test]
    fn test_zero_capacity() {
        assert_eq!(ShString::<0>::new("").as_str(), "");
        assert!(!ShString::<0>::new("").heap_allocated());
        assert_eq!(ShString::<0>::new("a").as_str(), "a");
        assert!(ShString::<0>::new("a").heap_allocated());
        assert_eq!(ShString::<0>::new("Hello").as_str(), "Hello");
        assert!(ShString::<0>::new("Hello").heap_allocated());
    }
}
