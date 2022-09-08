use core::{
    borrow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    mem::MaybeUninit,
    ops, ptr, str,
};

#[cfg(not(feature = "std"))]
use core::convert::TryFrom;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{
    borrow::{Cow, ToOwned},
    boxed::Box,
    string::String,
};

#[cfg(feature = "std")]
use std::borrow::Cow;

/// A string type which stores at most `N` bytes of string data. The string data is stored inline
/// rather than using a heap allocation.
///
/// ```
/// # use libshire::strings::CappedString;
/// # fn main() -> Result<(), libshire::strings::capped::Error> {
/// let s = CappedString::<16>::new("hello world")?;
/// assert_eq!(&*s, "hello world");
/// # Ok(())
/// # }
/// ```
#[derive(Clone)]
pub struct CappedString<const N: usize> {
    buf: [MaybeUninit<u8>; N],
    len: u8,
}

impl<const N: usize> CappedString<N> {
    const MAX_LEN: u8 = {
        #[allow(clippy::cast_possible_truncation, clippy::checked_conversions)]
        if N <= u8::MAX as usize {
            N as u8
        } else {
            panic!("`N` must be within the bounds of `u8`")
        }
    };

    /// Creates a new `CappedString` from a given byte buffer and length.
    ///
    /// # Safety
    ///
    /// The first `len` bytes of `buf` (i.e. `buf[..len]`) must be initialised and valid UTF-8.
    #[inline]
    #[must_use]
    pub const unsafe fn from_raw_parts(buf: [MaybeUninit<u8>; N], len: u8) -> Self {
        Self { buf, len }
    }

    #[inline]
    #[must_use]
    pub fn into_raw_parts(self) -> ([MaybeUninit<u8>; N], u8) {
        (self.buf, self.len)
    }

    /// Returns a new empty `CappedString`.
    ///
    /// ```
    /// # use libshire::strings::CappedString;
    /// let s = CappedString::<8>::empty();
    /// assert!(s.is_empty());
    /// assert_eq!(s.len(), 0);
    /// assert_eq!(&*s, "");
    /// ```
    #[inline]
    #[must_use]
    pub const fn empty() -> Self {
        // SAFETY:
        // `MaybeUninit::uninit()` is a valid value for `[MaybeUninit<u8>; N]`, since each element
        // of the array is allowed to be uninitialised.
        let buf = unsafe { MaybeUninit::<[MaybeUninit<u8>; N]>::uninit().assume_init() };

        // SAFETY:
        // It is vacuously true that the first 0 bytes of the buffer are initialised and valid
        // UTF-8.
        unsafe { Self::from_raw_parts(buf, 0) }
    }

    /// Returns a new `CappedString` containing the given string data. The string data will be
    /// stored inline; no heap allocation is used. An error will be returned if the length of the
    /// provided string exceeds the `CappedString`'s maximum length, `N`.
    ///
    /// ```
    /// # use libshire::strings::CappedString;
    /// # fn main() -> Result<(), libshire::strings::capped::Error> {
    /// let s = CappedString::<16>::new("hello world")?;
    /// assert_eq!(&*s, "hello world");
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn new<S>(s: &S) -> Result<Self, Error>
    where
        S: AsRef<str> + ?Sized,
    {
        // Convert the string to a byte slice, which is guaranteed to be valid UTF-8 since this is
        // an invariant of `str`.
        let src = <S as AsRef<str>>::as_ref(s).as_bytes();

        // If the length of the string is greater than `Self::MAX_LEN`, it will not fit in the
        // buffer so return `None`.
        let len = u8::try_from(src.len())
            .ok()
            .and_then(|len| (len <= Self::MAX_LEN).then_some(len))
            .ok_or(Error {
                max_len: N,
                actual_len: src.len(),
            })?;

        // SAFETY:
        // `MaybeUninit::uninit()` is a valid value for `[MaybeUninit<u8>; N]`, since each element
        // of the array is allowed to be uninitialised.
        let mut buf = unsafe { MaybeUninit::<[MaybeUninit<u8>; N]>::uninit().assume_init() };

        let src_ptr = src.as_ptr() as *const MaybeUninit<u8>;

        // SAFETY:
        // The source and destination to not overlap, since `buf` is a new local variable which is
        // completely separate from the provided source string `s`. The source is valid for reads of
        // `len` bytes since `len == src.len()`, and the destination is valid for writes of `len`
        // bytes since `len <= N`. The source and destination are both trivially properly aligned,
        // since they both have an alignment of 1.
        unsafe { ptr::copy_nonoverlapping(src_ptr, buf.as_mut_ptr(), usize::from(len)) }

        // SAFETY:
        // The first `len` bytes of the buffer are valid UTF-8 because the first `len` bytes of
        // the buffer contain data copied from a `&str`, and `&str` is always valid UTF-8.
        unsafe { Ok(Self::from_raw_parts(buf, len)) }
    }

    /// Returns a string slice pointing to the underlying string data.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        // SAFETY:
        // The first `self.len` bytes of `self.buf` (which is returned by `Self::as_bytes`) being
        // valid UTF-8 is an invariant of `CappedString`.
        unsafe { str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// Returns a mutable string slice pointing to the underlying string data.
    #[inline]
    #[must_use]
    pub fn as_str_mut(&mut self) -> &mut str {
        // SAFETY:
        // The first `self.len` bytes of `self.buf` (which is returned by `Self::as_bytes_mut`)
        // being valid UTF-8 is an invariant of `CappedString`.
        unsafe { str::from_utf8_unchecked_mut(self.as_bytes_mut()) }
    }

    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        // Get the slice of the buffer containing initialised string data.
        // SAFETY:
        // It is an invariant of `CappedString` that `self.len <= N`, so `..self.len` is a valid
        // range over `self.buf`.
        let data_slice = unsafe { self.buf.get_unchecked(..usize::from(self.len)) };

        // Convert the `&[MaybeUninit<u8>]` to a `&[u8]`.
        // SAFETY:
        // `MaybeUninit<u8>` has the same memory layout as `u8`, and the first `self.len` bytes of
        // the buffer are initialised, so this conversion is valid.
        unsafe { &*(data_slice as *const [MaybeUninit<u8>] as *const [u8]) }
    }

    /// # Safety
    /// The caller is responsible for ensuring that the slice is valid UTF-8 when the mutable
    /// borrow ends.
    #[inline]
    #[must_use]
    pub unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        // Get the slice of the buffer containing initialised string data.
        // SAFETY:
        // It is an invariant of `CappedString` that `self.len <= N`, so `..self.len` is a valid
        // range over `self.buf`.
        let data_slice = unsafe { self.buf.get_unchecked_mut(..usize::from(self.len)) };

        // Convert the `&[MaybeUninit<u8>]` to a `&[u8]`.
        // SAFETY:
        // `MaybeUninit<u8>` has the same memory layout as `u8`, and the first `self.len` bytes of
        // the buffer are initialised, so this conversion is valid.
        unsafe { &mut *(data_slice as *mut [MaybeUninit<u8>] as *mut [u8]) }
    }

    pub fn len(&self) -> usize {
        usize::from(self.len)
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

#[cfg(feature = "alloc")]
impl<const N: usize> CappedString<N> {
    pub fn into_boxed_str(self) -> Box<str> {
        self.as_str().into()
    }

    pub fn into_string(self) -> String {
        self.as_str().to_owned()
    }
}

impl<const N: usize> Default for CappedString<N> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

impl<const N: usize> ops::Deref for CappedString<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> ops::DerefMut for CappedString<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_str_mut()
    }
}

impl<const N: usize> AsRef<str> for CappedString<N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> AsMut<str> for CappedString<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> borrow::Borrow<str> for CappedString<N> {
    #[inline]
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> borrow::BorrowMut<str> for CappedString<N> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        self
    }
}

impl<'a, const N: usize> TryFrom<&'a str> for CappedString<N> {
    type Error = Error;

    #[inline]
    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        Self::new(s)
    }
}

#[cfg(feature = "alloc")]
impl<const N: usize> TryFrom<String> for CappedString<N> {
    type Error = Error;

    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::new(&s)
    }
}

#[cfg(feature = "alloc")]
impl<const N: usize> TryFrom<Box<str>> for CappedString<N> {
    type Error = Error;

    #[inline]
    fn try_from(s: Box<str>) -> Result<Self, Self::Error> {
        Self::new(&s)
    }
}

#[cfg(feature = "alloc")]
impl<'a, const N: usize> TryFrom<Cow<'a, str>> for CappedString<N> {
    type Error = Error;

    #[inline]
    fn try_from(s: Cow<'a, str>) -> Result<Self, Self::Error> {
        Self::new(&s)
    }
}

#[cfg(feature = "alloc")]
impl<const N: usize> From<CappedString<N>> for String {
    #[inline]
    fn from(s: CappedString<N>) -> Self {
        s.into_string()
    }
}

#[cfg(feature = "alloc")]
impl<const N: usize> From<CappedString<N>> for Box<str> {
    #[inline]
    fn from(s: CappedString<N>) -> Self {
        s.into_boxed_str()
    }
}

impl<const N: usize, const M: usize> PartialEq<CappedString<M>> for CappedString<N> {
    #[inline]
    fn eq(&self, other: &CappedString<M>) -> bool {
        **self == **other
    }
}

impl<const N: usize> Eq for CappedString<N> {}

impl<const N: usize, const M: usize> PartialOrd<CappedString<M>> for CappedString<N> {
    #[inline]
    fn partial_cmp(&self, other: &CappedString<M>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<const N: usize> Ord for CappedString<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<const N: usize> Hash for CappedString<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<const N: usize> str::FromStr for CappedString<N> {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(s)
    }
}

impl<const N: usize> fmt::Debug for CappedString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for CappedString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[derive(Debug)]
pub struct Error {
    max_len: usize,
    actual_len: usize,
}

impl Error {
    pub fn max_len(&self) -> usize {
        self.max_len
    }

    pub fn actual_len(&self) -> usize {
        self.actual_len
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "string of length {} exceeds limit for `CappedString<{}>`",
            self.actual_len,
            self.max_len
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}
