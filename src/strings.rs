use std::{
    borrow::{self, Cow},
    cmp::Ordering,
    convert::Infallible,
    fmt,
    hash::{Hash, Hasher},
    ops,
    str::FromStr,
};

#[cfg(feature = "sqlx")]
use sqlx::{
    Database,
    database::{HasArguments, HasValueRef},
    Decode,
    Encode,
    Type,
    encode::IsNull,
    error::BoxDynError,
};

use buf::{StackString, HeapString};

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
/// allocated on the heap.
#[derive(Clone)]
pub struct ShString<const N: usize>(Repr<N>);

impl<const N: usize> ShString<N> {
    /// Creates a new `ShString` from the given string slice, putting it on the stack if possible
    /// or creating a new heap allocation otherwise.
    pub fn new_from_str(s: &str) -> Self {
        match StackString::from_str(s) {
            Some(stack_buf) => Self(Repr::Stack(stack_buf)),
            None => Self(Repr::Heap(HeapString::from_str(s))),
        }
    }

    /// Creates a new `ShString` from the given owned `String`, moving the string data onto the
    /// stack if possible or reusing the `String`'s heap allocation otherwise.
    pub fn new_from_string(s: String) -> Self {
        match StackString::from_str(&s) {
            Some(stack_buf) => Self(Repr::Stack(stack_buf)),
            None => Self(Repr::Heap(HeapString::from_string(s))),
        }
    }

    /// Creates a new `ShString` from the given `Cow<str>`.
    pub fn new_from_cow_str(s: Cow<str>) -> Self {
        match s {
            Cow::Borrowed(s) => Self::new_from_str(s),
            Cow::Owned(s) => Self::new_from_string(s),
        }
    }

    /// Returns a string slice for the underlying string data.
    pub fn as_str(&self) -> &str {
        match self {
            Self(Repr::Stack(buf)) => buf.as_str(),
            Self(Repr::Heap(buf)) => buf.as_str(),
        }
    }

    /// Returns a mutable string slice for the underlying string data.
    pub fn as_str_mut(&mut self) -> &mut str {
        match self {
            Self(Repr::Stack(buf)) => buf.as_str_mut(),
            Self(Repr::Heap(buf)) => buf.as_str_mut(),
        }
    }

    /// Consumes the `ShString` and converts it to a heap-allocated `String`.
    pub fn into_string(self) -> String {
        match self {
            Self(Repr::Stack(buf)) => buf.into_string(),
            Self(Repr::Heap(buf)) => buf.into_string(),
        }
    }

    /// Returns the length of the string in bytes.
    pub fn len(&self) -> usize {
        match self {
            Self(Repr::Stack(buf)) => buf.len(),
            Self(Repr::Heap(buf)) => buf.len(),
        }
    }

    /// Returns `true` if the string has length 0.
    pub fn is_empty(&self) -> bool {
        match self {
            Self(Repr::Stack(buf)) => buf.is_empty(),
            Self(Repr::Heap(buf)) => buf.is_empty(),
        }
    }

    /// Returns `true` if the string data is stored on the heap, and `false` otherwise.
    pub fn heap_allocated(&self) -> bool {
        match self {
            Self(Repr::Stack(_)) => false,
            Self(Repr::Heap(_)) => true,
        }
    }
}

impl<const N: usize> ops::Deref for ShString<N> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> ops::DerefMut for ShString<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_str_mut()
    }
}

impl<const N: usize> AsRef<str> for ShString<N> {
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> borrow::Borrow<str> for ShString<N> {
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> borrow::BorrowMut<str> for ShString<N> {
    fn borrow_mut(&mut self) -> &mut str {
        self
    }
}

impl<'a, const N: usize> From<&'a str> for ShString<N> {
    fn from(s: &'a str) -> Self {
        Self::new_from_str(s)
    }
}

impl<const N: usize> From<String> for ShString<N> {
    fn from(s: String) -> Self {
        Self::new_from_string(s)
    }
}

impl<'a, const N: usize> From<Cow<'a, str>> for ShString<N> {
    fn from(s: Cow<'a, str>) -> Self {
        Self::new_from_cow_str(s)
    }
}

impl<const N: usize> From<ShString<N>> for String {
    fn from(s: ShString<N>) -> Self {
        s.into_string()
    }
}

impl<const N: usize, const M: usize> PartialEq<ShString<M>> for ShString<N> {
    fn eq(&self, other: &ShString<M>) -> bool {
        **self == **other
    }
}

impl<const N: usize> Eq for ShString<N> {}

impl<const N: usize, const M: usize> PartialOrd<ShString<M>> for ShString<N> {
    fn partial_cmp(&self, other: &ShString<M>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<const N: usize> Ord for ShString<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<const N: usize> Hash for ShString<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<const N: usize> FromStr for ShString<N> {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new_from_str(s))
    }
}

impl<const N: usize> fmt::Debug for ShString<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for ShString<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[cfg(feature = "sqlx")]
impl<'r, DB, const N: usize> Decode<'r, DB> for ShString<N>
where
    DB: Database,
    &'r str: Decode<'r, DB>,
{
    fn decode(value: <DB as HasValueRef<'r>>::ValueRef) -> Result<Self, BoxDynError> {
        <&'r str as Decode<'r, DB>>::decode(value).map(Self::new_from_str)
    }
}

#[cfg(feature = "sqlx")]
impl<'q, DB, const N: usize> Encode<'q, DB> for ShString<N>
where
    DB: Database,
    for<'a> &'a str: Encode<'q, DB>,
{
    fn encode_by_ref(&self, buf: &mut <DB as HasArguments<'q>>::ArgumentBuffer) -> IsNull {
        <&str as Encode<'q, DB>>::encode(self.as_str(), buf)
    }
}

#[cfg(feature = "sqlx")]
impl<DB, const N: usize> Type<DB> for ShString<N>
where
    DB: Database,
    for<'a> &'a str: Type<DB>,
{
    fn type_info() -> <DB as Database>::TypeInfo {
        <&str as Type<DB>>::type_info()
    }

    fn compatible(ty: &<DB as Database>::TypeInfo) -> bool {
        <&str as Type<DB>>::compatible(ty)
    }
}

#[derive(Clone)]
enum Repr<const N: usize> {
    Stack(StackString<N>),
    Heap(HeapString),
}

mod buf {
    use std::str;

    /// A stack-allocated string with a capacity of `N` bytes. `len` must be less than or equal to
    /// `N`, and the first `len` bytes of `buf` must be valid UTF-8.
    #[derive(Clone)]
    pub(super) struct StackString<const N: usize> {
        buf: [u8; N],
        len: u8,
    }

    impl<const N: usize> StackString<N> {
        const MAX_LEN: u8 = {
            #[allow(clippy::cast_possible_truncation, clippy::checked_conversions)]
            if N <= u8::MAX as usize {
                N as u8
            } else {
                panic!("`N` must be within the bounds of `u8`")
            }
        };

        pub(super) fn from_str(s: &str) -> Option<Self> {
            let s = s.as_bytes();

            // If the length of the string is greater than `Self::MAX_LEN`, it will not fit in the
            // stack buffer so return `None`.
            let len = u8::try_from(s.len()).ok()?;
            if len > Self::MAX_LEN {
                return None;
            }

            let mut buf = [0; N];
            buf[..usize::from(len)].copy_from_slice(s);
            Some(Self { buf, len })
        }

        pub(super) fn as_str(&self) -> &str {
            // SAFETY:
            // `len` being less than or equal to `N` is an invariant of `StackString`, so it is
            // always within the bounds of `buf`.
            let slice = unsafe { self.buf.get_unchecked(..usize::from(self.len)) };

            // SAFETY:
            // The first `len` bytes of `buf` being valid UTF-8 is an invariant of `StackString`.
            unsafe { str::from_utf8_unchecked(slice) }
        }

        pub(super) fn as_str_mut(&mut self) -> &mut str {
            // SAFETY:
            // `len` being less than or equal to `N` is an invariant of `StackString`, so it is
            // always within the bounds of `buf`.
            let slice = unsafe { self.buf.get_unchecked_mut(..usize::from(self.len)) };

            // SAFETY:
            // The first `len` bytes of `buf` being valid UTF-8 is an invariant of `StackString`.
            unsafe { str::from_utf8_unchecked_mut(slice) }
        }

        pub(super) fn into_string(self) -> String {
            self.as_str().to_owned()
        }

        pub(super) fn len(&self) -> usize {
            usize::from(self.len)
        }

        pub(super) fn is_empty(&self) -> bool {
            self.len == 0
        }
    }

    /// A heap-allocated non-growable string. `buf` must be valid UTF-8.
    #[derive(Clone)]
    pub(super) struct HeapString {
        buf: Box<[u8]>,
    }

    impl HeapString {
        pub(super) fn from_str(s: &str) -> Self {
            Self {
                buf: s.as_bytes().into(),
            }
        }

        pub(super) fn from_string(s: String) -> Self {
            Self {
                buf: s.into_boxed_str().into_boxed_bytes(),
            }
        }

        pub(super) fn as_str(&self) -> &str {
            // SAFETY:
            // `buf` being valid UTF-8 is an invariant of `HeapString`.
            unsafe { str::from_utf8_unchecked(&self.buf) }
        }

        pub(super) fn as_str_mut(&mut self) -> &mut str {
            // SAFETY:
            // `buf` being valid UTF-8 is an invariant of `HeapString`.
            unsafe { str::from_utf8_unchecked_mut(&mut self.buf) }
        }

        pub(super) fn into_string(self) -> String {
            // SAFETY:
            // `buf` being valid UTF-8 is an invariant of `HeapString`.
            unsafe { String::from_utf8_unchecked(self.buf.into_vec()) }
        }

        pub(super) fn len(&self) -> usize {
            self.buf.len()
        }

        pub(super) fn is_empty(&self) -> bool {
            self.buf.is_empty()
        }
    }
}
