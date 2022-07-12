use std::{
    borrow::{self, Cow},
    cmp::Ordering,
    error,
    fmt,
    hash::{Hash, Hasher},
    ops,
    str,
};

#[derive(Clone)]
pub struct StackString<const N: usize> {
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

    /// Creates a new `StackString` from a given byte buffer and length.
    ///
    /// # Safety
    ///
    /// The first `len` bytes of `buf` (i.e. `buf[..len]`) must be valid UTF-8.
    #[inline]
    #[must_use]
    pub const unsafe fn from_raw_parts(buf: [u8; N], len: u8) -> Self {
        Self { buf, len }
    }

    /// Returns a new empty `StackString`.
    #[inline]
    #[must_use]
    pub const fn empty() -> Self {
        // SAFETY:
        // The first zero bytes of the buffer are valid UTF-8, because an empty byte slice is
        // valid UTF-8.
        unsafe { Self::from_raw_parts([0; N], 0) }
    }

    #[inline]
    pub fn new<S>(s: &S) -> Result<Self, StackStringError>
    where
        S: AsRef<str> + ?Sized,
    {
        // Convert the string to a byte slice, which is guaranteed to be valid UTF-8 since this is
        // an invariant of `str`.
        let s = <S as AsRef<str>>::as_ref(s).as_bytes();

        // If the length of the string is greater than `Self::MAX_LEN`, it will not fit in the
        // stack buffer so return `None`.
        let len = u8::try_from(s.len())
            .ok()
            .and_then(|len| (len <= Self::MAX_LEN).then_some(len))
            .ok_or(StackStringError {
                max_len: N,
                actual_len: s.len(),
            })?;

        let mut buf = [0; N];
        buf[..usize::from(len)].copy_from_slice(s);

        // SAFETY:
        // The first `len` bytes of the buffer are valid UTF-8 because the first `len` bytes of
        // the buffer contain data copied from a `&str`, and `&str` is always valid UTF-8.
        unsafe { Ok(Self::from_raw_parts(buf, len)) }
    }

    /// Returns a string slice pointing to the underlying string data.
    pub fn as_str(&self) -> &str {
        // SAFETY:
        // `len` being less than or equal to `N` is an invariant of `StackString`, so it is
        // always within the bounds of `buf`.
        let slice = unsafe { self.buf.get_unchecked(..usize::from(self.len)) };

        // SAFETY:
        // The first `len` bytes of `buf` being valid UTF-8 is an invariant of `StackString`.
        unsafe { str::from_utf8_unchecked(slice) }
    }

    /// Returns a mutable string slice pointing to the underlying string data.
    pub fn as_str_mut(&mut self) -> &mut str {
        // SAFETY:
        // `len` being less than or equal to `N` is an invariant of `StackString`, so it is
        // always within the bounds of `buf`.
        let slice = unsafe { self.buf.get_unchecked_mut(..usize::from(self.len)) };

        // SAFETY:
        // The first `len` bytes of `buf` being valid UTF-8 is an invariant of `StackString`.
        unsafe { str::from_utf8_unchecked_mut(slice) }
    }

    pub fn into_string(self) -> String {
        self.as_str().to_owned()
    }

    pub fn len(&self) -> usize {
        usize::from(self.len)
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<const N: usize> Default for StackString<N> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

impl<const N: usize> ops::Deref for StackString<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> ops::DerefMut for StackString<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_str_mut()
    }
}

impl<const N: usize> AsRef<str> for StackString<N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> AsMut<str> for StackString<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> borrow::Borrow<str> for StackString<N> {
    #[inline]
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> borrow::BorrowMut<str> for StackString<N> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        self
    }
}

impl<'a, const N: usize> TryFrom<&'a str> for StackString<N> {
    type Error = StackStringError;

    #[inline]
    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        Self::new(s)
    }
}

impl<const N: usize> TryFrom<String> for StackString<N> {
    type Error = StackStringError;

    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::new(&s)
    }
}

impl<'a, const N: usize> TryFrom<Cow<'a, str>> for StackString<N> {
    type Error = StackStringError;

    #[inline]
    fn try_from(s: Cow<'a, str>) -> Result<Self, Self::Error> {
        Self::new(&s)
    }
}

impl<const N: usize> From<StackString<N>> for String {
    #[inline]
    fn from(s: StackString<N>) -> Self {
        s.into_string()
    }
}

impl<const N: usize, const M: usize> PartialEq<StackString<M>> for StackString<N> {
    #[inline]
    fn eq(&self, other: &StackString<M>) -> bool {
        **self == **other
    }
}

impl<const N: usize> Eq for StackString<N> {}

impl<const N: usize, const M: usize> PartialOrd<StackString<M>> for StackString<N> {
    #[inline]
    fn partial_cmp(&self, other: &StackString<M>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<const N: usize> Ord for StackString<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<const N: usize> Hash for StackString<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<const N: usize> str::FromStr for StackString<N> {
    type Err = StackStringError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(s)
    }
}

impl<const N: usize> fmt::Debug for StackString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for StackString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[derive(Debug)]
pub struct StackStringError {
    max_len: usize,
    actual_len: usize,
}

impl StackStringError {
    pub fn max_len(&self) -> usize {
        self.max_len
    }

    pub fn actual_len(&self) -> usize {
        self.actual_len
    }
}

impl fmt::Display for StackStringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "string of length {} exceeds limit for `StackString<{}>`",
            self.actual_len,
            self.max_len
        )
    }
}

impl error::Error for StackStringError {}
