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

use super::fixed::{FixedString, LengthError};

#[derive(Debug)]
pub struct CapacityError;

impl fmt::Display for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`CappedString` capacity exceeded")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for CapacityError {}

/// A string type which stores at most `N` bytes of string data. The string data is stored inline
/// rather than using a heap allocation.
///
/// ```
/// # use libshire::strings::CappedString;
/// # fn main() -> Result<(), libshire::strings::capped::CapacityError> {
/// let s = CappedString::<16>::new("hello world")?;
/// assert_eq!(&*s, "hello world");
/// # Ok(())
/// # }
/// ```
#[derive(Clone)]
pub struct CappedString<const N: usize> {
    /// The buffer storing the string data. It is an invariant of this type that the first `len`
    /// elements of this buffer is initialised, valid UTF-8 string data.
    buf: [MaybeUninit<u8>; N],

    /// The length of the string stored in `buf`.
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
    /// The first `len` bytes of `buf` (i.e. `buf[..len]`) must be initialised and valid UTF-8. 
    /// `len` must be less than or equal to `N`.
    #[inline]
    #[must_use]
    pub const unsafe fn from_raw_parts(buf: [MaybeUninit<u8>; N], len: u8) -> Self {
        Self { buf, len }
    }

    /// Returns the raw buffer and length backing this `CappedString`; the first element of the
    /// tuple is the buffer `buf` and the second is the length `len`. The first `len` elements of
    /// `buf` (i.e. `&buf[..usize::from(len)]`) is guaranteed to be initialised, valid UTF-8 string
    /// data.
    #[inline]
    #[must_use]
    pub const fn into_raw_parts(self) -> ([MaybeUninit<u8>; N], u8) {
        (self.buf, self.len)
    }

    /// # Safety
    /// `src` must point to `len` bytes of valid, UTF-8 string data. `len` must be less than or
    /// equal to `N`.
    #[inline]
    unsafe fn from_raw_ptr(src: *const u8, len: u8) -> Self {
        // `u8` has the same memory layout as `MaybeUninit<u8>`, so this cast is valid.
        let src = src as *const MaybeUninit<u8>;

        // SAFETY:
        // `MaybeUninit::uninit()` is a valid value for `[MaybeUninit<u8>; N]`, since each element
        // of the array is allowed to be uninitialised.
        let mut buf = unsafe { MaybeUninit::<[MaybeUninit<u8>; N]>::uninit().assume_init() };

        // SAFETY:
        // The caller is responsible for ensuring that `src` points to a valid string, which means
        // that it must not overlap with the new local variable `buf`. The caller is responsible
        // for ensuring that `src` is valid for reads of `len` bytes. The caller is responsible for
        // ensuring that `len <= N`, so `buf` is valid for writes of `len` bytes. `src` and `buf`
        // are both trivially properly aligned, since they both have an alignment of 1.
        unsafe { ptr::copy_nonoverlapping(src, buf.as_mut_ptr(), usize::from(len)); }

        // SAFETY:
        // The caller is responsible for ensuring that `src` points to `len` bytes of valid UTF-8
        // data. `src` is copied into the start of `buf`, so the first `len` bytes of `buf` are
        // valid UTF-8. The caller is responsible for ensuring that `len <= N`.
        unsafe { Self::from_raw_parts(buf, len) }
    }

    /// # Safety
    /// `self.len` must be less than `N`, so that there is space in the buffer to append the byte.
    /// The byte must be a valid UTF-8 codepoint; it must be in the range `0..=127`.
    #[inline]
    unsafe fn append_byte(&mut self, byte: u8) {
        // SAFETY:
        // The caller is responsible for ensuring that `self.len < N`.
        let dst = unsafe { self.buf.get_unchecked_mut(usize::from(self.len)) };
        
        *dst = MaybeUninit::new(byte);
        self.len += 1;
    }

    /// # Safety
    /// `src` must point to `len` bytes of valid UTF-8 string data. `len` must be less than or equal
    /// to `N - self.len`.
    #[inline]
    unsafe fn append_bytes(&mut self, src: *const u8, len: u8) {
        // `u8` has the same memory layout as `MaybeUninit<u8>`, so this cast is valid.
        let src = src as *const MaybeUninit<u8>;

        // SAFETY:
        // `self.len <= N` is an invariant of `CappedString`, so `self.len..` is a valid range over
        // `self.buf`.
        let dst = unsafe { self.buf.get_unchecked_mut(usize::from(self.len)..) };

        // SAFETY:
        // The caller is responsible for ensuring that `src` points to a valid string, which means
        // that it cannot overlap with the new local variable `buf`. The caller is responsible for
        // ensuring that `src` is valid for reads of `len` bytes. The caller is responsible for
        // ensuring that `len <= N - self.len`, so the destination `dst = self.buf[self.len..]` is
        // valid for writes of `len` bytes. `src` and `dst` are both trivially properly aligned,
        // since they both have an alignment of 1.
        unsafe { ptr::copy_nonoverlapping(src, dst.as_mut_ptr(), usize::from(len)); }

        self.len += len;
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
    /// If you would like a version which never returns an error, see [`Self::new_truncating`].
    ///
    /// ```
    /// # use libshire::strings::CappedString;
    /// # fn main() -> Result<(), libshire::strings::capped::CapacityError> {
    /// let s = CappedString::<16>::new("hello world")?;
    /// assert_eq!(&*s, "hello world");
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn new<S>(src: &S) -> Result<Self, CapacityError>
    where
        S: AsRef<str> + ?Sized,
    {
        // Convert the string to a byte slice, which is guaranteed to be valid UTF-8 since this is
        // an invariant of `str`.
        let src = <S as AsRef<str>>::as_ref(src);

        // If the length of the `src` string does not fit into a `u8` or is greater than 
        // `Self::MAX_LEN`, we can't fit it into the new `CappedString` so return an error.
        let len = match u8::try_from(src.len()) {
            Ok(len) if len <= Self::MAX_LEN => len,
            _ => return Err(CapacityError),
        };

        // SAFETY:
        // `src.as_ptr()` points to `len` bytes of valid UTF-8 string data since `src` is a `&str`
        // and `len` is its length. `len` is less than or equal to `Self::MAX_LEN`, which is equal
        // to `N`.
        unsafe { Ok(Self::from_raw_ptr(src.as_ptr(), len)) }
    }

    /// Returns a new `CappedString` containing the given string data. The string data will be
    /// stored inline; no heap allocation is used. If the length of the provided string exceeds the
    /// `CappedString`'s maximum length, `N`, it will be truncated to fit.
    /// 
    /// If you would like a version which returns an error rather than truncating the string, see
    /// [`Self::new`].
    /// 
    /// ```
    /// # use libshire::strings::CappedString;
    /// let s1 = CappedString::<15>::new_truncating("こんにちは");
    /// assert_eq!(&*s1, "こんにちは");
    /// 
    /// let s2 = CappedString::<10>::new_truncating("こんにちは");
    /// assert_eq!(&*s2, "こんに");
    /// ```
    #[inline]
    #[must_use]
    pub fn new_truncating<S>(src: &S) -> Self
    where
        S: AsRef<str> + ?Sized,
    {
        let src = <S as AsRef<str>>::as_ref(src);

        let (src, len) = truncate_str(src, Self::MAX_LEN);

        // SAFETY:
        // It is part of the contract of `truncate_str` that it returns a pointer to a valid UTF-8
        // string of length `len`, and that `len` is less than or equal to the provided maximum
        // length, which is `Self::MAX_LEN` (which is equal to `N`) in this case.
        unsafe { Self::from_raw_ptr(src, len) }
    }

    /// Appends the given character to the end of this `CappedString`, returning an error if there
    /// is insufficient capacity remaining to do so.
    /// 
    /// If you do not care whether or not the append succeeds, see [`Self::push_truncating`].
    #[inline]
    pub fn push(&mut self, c: char) -> Result<(), CapacityError> {
        let mut char_buf = [0u8; 4];
        let encoded = c.encode_utf8(&mut char_buf);

        match encoded.len() {
            1 => {
                if self.len == Self::MAX_LEN {
                    return Err(CapacityError);
                }

                // SAFETY:
                // We have checked that `self.len != N` (`Self::MAX_LEN == N`). Since it is an
                // invariant of `CappedString` that `self.len <= N`, it must hold that 
                // `self.len < N`. The first byte of a `str` of length 1 must be a valid UTF-8
                // codepoint; it must be in the range `0..=127`, since anything outside this range
                // implies the presence of further bytes.
                unsafe { self.append_byte(encoded.as_bytes()[0]) }

                Ok(())
            },

            _ => self.push_str(encoded),
        }
    }

    /// Appends the given character to the end of this `CappedString`, failing silently if there is
    /// insufficient capacity remaining to do so.
    /// 
    /// If you would like to know whether or not the append succeeds, see [`Self::push`].
    #[inline]
    pub fn push_truncating(&mut self, c: char) {
        // Unlike `Self::push_str_truncating`, we can just use `Self::push` and swallow the error
        // because a single character will never be partially pushed; it is either pushed or it
        // isn't.
        self.push(c).ok();
    }

    /// Appends the given string slice to the end of this `CappedString`, returning an error if
    /// there is insufficient capacity remaining to do so.
    /// 
    /// If you would like a version which cannot fail, see [`Self::push_str_truncating`].
    /// 
    /// ```
    /// # use libshire::strings::CappedString;
    /// let mut s = CappedString::<8>::empty();
    /// 
    /// assert!(s.push_str("hello").is_ok());
    /// assert_eq!(&*s, "hello");
    /// 
    /// assert!(s.push_str(" world").is_err());
    /// assert_eq!(&*s, "hello");
    /// 
    /// assert!(s.push_str("!!!").is_ok());
    /// assert_eq!(&*s, "hello!!!");
    /// ```
    #[inline]
    pub fn push_str<S>(&mut self, src: &S) -> Result<(), CapacityError>
    where
        S: AsRef<str> + ?Sized,
    {
        let src = <S as AsRef<str>>::as_ref(src);

        let len = match u8::try_from(src.len()) {
            Ok(len) if len <= Self::MAX_LEN - self.len => len,
            _ => return Err(CapacityError),
        };

        // SAFETY:
        // `src` is a valid string slice with length `len`. We have checked that
        // `len <= N - self.len` holds above (note that `Self::MAX_LEN == N`).
        unsafe { self.append_bytes(src.as_ptr(), len); }

        Ok(())
    }

    /// Appends as many of the characters of the given string slice to the end of this 
    /// `CappedString` as can fit. Any remaining characters will not be added.
    /// 
    /// If you would like a version which returns an error if there is not enough capacity remaining
    /// to append the entire string slice, see [`Self::push_str`].
    /// 
    /// ```
    /// # use libshire::strings::CappedString;
    /// let mut s = CappedString::<10>::empty();
    /// 
    /// s.push_str_truncating("hello");
    /// assert_eq!(&*s, "hello");
    /// 
    /// s.push_str_truncating(" 世界");
    /// assert_eq!(&*s, "hello 世");
    /// 
    /// s.push_str_truncating("!!!");
    /// assert_eq!(&*s, "hello 世!");
    /// ```
    #[inline]
    pub fn push_str_truncating<S>(&mut self, src: &S)
    where
        S: AsRef<str> + ?Sized,
    {
        let remaining_cap = Self::MAX_LEN - self.len;

        // Short-circuit if we have no space left to copy into.
        if remaining_cap == 0 {
            return;
        }

        let src = <S as AsRef<str>>::as_ref(src);

        // Find the longest valid UTF-8 prefix which fits into the remaining space.
        let (src, len) = truncate_str(src, remaining_cap);

        // SAFETY:
        // `truncate_str` returns a pointer to `len` bytes of valid UTF-8 string data. The returned
        // `len` will always be less than or equal to `remaining_cap`, which is equal to
        // `N - self.len` (note that `Self::MAX_LEN == N`).
        unsafe { self.append_bytes(src, len); }
    }

    /// Empties the contents of this `CappedString`.
    /// 
    /// ```
    /// # use libshire::strings::CappedString;
    /// # fn main() -> Result<(), libshire::strings::capped::CapacityError> {
    /// let mut s = CappedString::<16>::new("hello")?;
    /// 
    /// assert!(!s.is_empty());
    /// assert_eq!(&*s, "hello");
    /// 
    /// s.clear();
    /// 
    /// assert!(s.is_empty());
    /// assert_eq!(&*s, "");
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        // Setting the length to 0 is enough to clear the `CappedString`; we don't need to replace
        // any of the old bytes in the buffer, as setting the length to 0 makes all of the old bytes
        // inaccessible via safe methods, and means that any future calls to `Self::push` and
        // friends will write over the old bytes.
        // 
        // It may be desirable for security-critical code to zero the old buffer to prevent cleared
        // data from being exposed via buffer-overflow exploits or similar. However, this should be
        // implemented in a separate function so that regular users don't have to pay the cost of
        // zeroing the buffer.
        self.len = 0;
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
    /// 
    /// ```
    /// # use libshire::strings::CappedString;
    /// # fn main() -> Result<(), libshire::strings::capped::CapacityError> {
    /// let mut s = CappedString::<16>::new("hello!")?;
    /// s.as_str_mut().make_ascii_uppercase();
    /// assert_eq!(&*s, "HELLO!");
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str_mut(&mut self) -> &mut str {
        // SAFETY:
        // The first `self.len` bytes of `self.buf` (which is returned by `Self::as_bytes_mut`)
        // being valid UTF-8 is an invariant of `CappedString`. Since we are returning a `&mut str`
        // to the caller, the caller cannot safely use it to mutate this `CappedString`'s buffer in
        // a way that violates the UTF-8 property.
        unsafe { str::from_utf8_unchecked_mut(self.as_bytes_mut()) }
    }

    /// Returns a byte slice containing the UTF-8 bytes representing the string.
    /// 
    /// ```
    /// # use libshire::strings::CappedString;
    /// # fn main() -> Result<(), libshire::strings::capped::CapacityError> {
    /// let s = CappedString::<16>::new("hello!")?;
    /// assert_eq!(s.as_bytes(), &[0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x21]);
    /// # Ok(())
    /// # }
    /// ```
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
    /// The slice must be valid UTF-8 when the mutable borrow ends and this `CappedString` is used
    /// again.
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

    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        usize::from(self.len)
    }

    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn into_fixed<const M: usize>(self) -> Result<FixedString<M>, LengthError> {
        let buf: [u8; M] = self
            .as_bytes()
            .try_into()
            .map_err(|_| LengthError)?;
        
        // SAFETY:
        // It is an invariant of `CappedString` that the first `self.len` bytes of `self.buf` is
        // valid UTF-8, so the bytes returned by `Self::as_bytes` are valid UTF-8.
        unsafe { Ok(FixedString::from_raw_array(buf)) }
    }

    #[inline]
    pub fn into_fixed_max_capacity(self) -> Result<FixedString<N>, LengthError> {
        self.into_fixed()
    }
}

#[cfg(feature = "alloc")]
impl<const N: usize> CappedString<N> {
    #[inline]
    #[must_use]
    pub fn into_boxed_str(self) -> Box<str> {
        self.as_str().into()
    }

    #[inline]
    #[must_use]
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
    type Error = CapacityError;

    #[inline]
    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        Self::new(s)
    }
}

#[cfg(feature = "alloc")]
impl<const N: usize> TryFrom<String> for CappedString<N> {
    type Error = CapacityError;

    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::new(&s)
    }
}

#[cfg(feature = "alloc")]
impl<const N: usize> TryFrom<Box<str>> for CappedString<N> {
    type Error = CapacityError;

    #[inline]
    fn try_from(s: Box<str>) -> Result<Self, Self::Error> {
        Self::new(&s)
    }
}

#[cfg(feature = "alloc")]
impl<'a, const N: usize> TryFrom<Cow<'a, str>> for CappedString<N> {
    type Error = CapacityError;

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
    type Err = CapacityError;

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

/// Returns a pointer to the longest prefix of `src` which is valid UTF-8 and whose length is
/// less than or equal to `max_len`, and returns the length of this prefix.
#[inline]
fn truncate_str(src: &str, max_len: u8) -> (*const u8, u8) {
    match u8::try_from(src.len()) {
        // If the length of the `src` string is less than or equal to `max_len`, there is no need to
        // truncate it.
        Ok(src_len) if src_len <= max_len => (src.as_ptr(), src_len),

        // If the length of `src` is greater than `max_len`, we need to truncate it. Note that
        // `u8::try_from` returning an error means that `src.len() > max_len`, since `max_len` is a
        // `u8` and `src.len()` is a `usize`.
        _ => {
            let src = src.as_bytes();

            let mut i = max_len;

            // Find the rightmost codepoint which starts at an index less than or equal to
            // `max_len`. Everything to the left of this will be valid UTF-8 with a length less
            // than or equal to `max_len`. We only need to do 3 iterations because codepoints have
            // a maximum length of 4 bytes.
            for _ in 0..3 {
                // The first byte in the string must always be the start of a codepoint.
                if i == 0 {
                    break;
                }

                // SAFETY:
                // `i <= max_len`, since it is never incremented. If this branch is run, then either
                // `src.len(): usize` does not fit into a `u8`, in which case it must be greater
                // than `max_len: u8`, or it does fit into a `u8` but it is greater than `max_len`.
                // Therefore, `src.len() > max_len` must hold. Substitution gives `i < src.len()`,
                // so `i` is a valid index into `src`.
                let byte = unsafe { *src.get_unchecked(usize::from(i)) };

                // If the byte is not of the form 0b10xxxxxx, then it is the start of a codepoint.
                if byte & 0xc0 != 0x80 {
                    break;
                }

                i -= 1;
            }

            // `i < src.len()` always holds as discussed above, so the pointer `src.as_ptr()` is
            // valid for reads of `i` bytes. `i` is the index of the start of a codepoint, and
            // codepoints are contiguous, so the `i` bytes being pointed to must be valid UTF-8.
            (src.as_ptr(), i)
        },
    }
}

#[cfg(test)]
mod tests {
    use super::CappedString;

    #[test]
    fn test_truncate_str() {
        use super::truncate_str;

        let s1 = "hello";
        assert_eq!(truncate_str(s1, 0), (s1.as_ptr(), 0));
        assert_eq!(truncate_str(s1, 1), (s1.as_ptr(), 1));
        assert_eq!(truncate_str(s1, 5), (s1.as_ptr(), 5));
        assert_eq!(truncate_str(s1, 6), (s1.as_ptr(), 5));

        let s2 = "こんにちは";
        assert_eq!(truncate_str(s2, 0), (s2.as_ptr(), 0));
        assert_eq!(truncate_str(s2, 1), (s2.as_ptr(), 0));
        assert_eq!(truncate_str(s2, 2), (s2.as_ptr(), 0));
        assert_eq!(truncate_str(s2, 3), (s2.as_ptr(), 3));
        assert_eq!(truncate_str(s2, 4), (s2.as_ptr(), 3));
        assert_eq!(truncate_str(s2, 5), (s2.as_ptr(), 3));
        assert_eq!(truncate_str(s2, 6), (s2.as_ptr(), 6));
        assert_eq!(truncate_str(s2, 14), (s2.as_ptr(), 12));
        assert_eq!(truncate_str(s2, 15), (s2.as_ptr(), 15));
        assert_eq!(truncate_str(s2, 16), (s2.as_ptr(), 15));
        assert_eq!(truncate_str(s2, 18), (s2.as_ptr(), 15));

        let s3 = "🤖 こんにちは, world 🤖";
        assert_eq!(truncate_str(s3, 0), (s3.as_ptr(), 0));
        assert_eq!(truncate_str(s3, 1), (s3.as_ptr(), 0));
        assert_eq!(truncate_str(s3, 2), (s3.as_ptr(), 0));
        assert_eq!(truncate_str(s3, 3), (s3.as_ptr(), 0));
        assert_eq!(truncate_str(s3, 4), (s3.as_ptr(), 4));
        assert_eq!(truncate_str(s3, 5), (s3.as_ptr(), 5));
        assert_eq!(truncate_str(s3, 6), (s3.as_ptr(), 5));
        assert_eq!(truncate_str(s3, 7), (s3.as_ptr(), 5));
        assert_eq!(truncate_str(s3, 8), (s3.as_ptr(), 8));
        assert_eq!(truncate_str(s3, 28), (s3.as_ptr(), 28));
        assert_eq!(truncate_str(s3, 29), (s3.as_ptr(), 28));
        assert_eq!(truncate_str(s3, 30), (s3.as_ptr(), 28));
        assert_eq!(truncate_str(s3, 31), (s3.as_ptr(), 28));
        assert_eq!(truncate_str(s3, 32), (s3.as_ptr(), 32));
        assert_eq!(truncate_str(s3, 33), (s3.as_ptr(), 32));
        assert_eq!(truncate_str(s3, 36), (s3.as_ptr(), 32));

        let s4 = "a";
        assert_eq!(truncate_str(s4, 0), (s4.as_ptr(), 0));
        assert_eq!(truncate_str(s4, 1), (s4.as_ptr(), 1));
        assert_eq!(truncate_str(s4, 2), (s4.as_ptr(), 1));
        assert_eq!(truncate_str(s4, 3), (s4.as_ptr(), 1));
        assert_eq!(truncate_str(s4, 4), (s4.as_ptr(), 1));

        let s5 = "";
        assert_eq!(truncate_str(s5, 0), (s5.as_ptr(), 0));
        assert_eq!(truncate_str(s5, 1), (s5.as_ptr(), 0));
        assert_eq!(truncate_str(s5, 2), (s5.as_ptr(), 0));
        assert_eq!(truncate_str(s5, 3), (s5.as_ptr(), 0));
        assert_eq!(truncate_str(s5, 4), (s5.as_ptr(), 0));

        let s6 = "На берегу пустынных волн\n\
                  Стоял он, дум великих полн,\n\
                  И вдаль глядел. Пред ним широко\n\
                  Река неслася; бедный чёлн\n\
                  По ней стремился одиноко.\n\
                  По мшистым, топким берегам\n\
                  Чернели избы здесь и там,\n\
                  Приют убогого чухонца;\n\
                  И лес, неведомый лучам\n\
                  В тумане спрятанного солнца,\n\
                  Кругом шумел.";
        assert_eq!(truncate_str(s6, 0), (s6.as_ptr(), 0));
        assert_eq!(truncate_str(s6, 1), (s6.as_ptr(), 0));
        assert_eq!(truncate_str(s6, 2), (s6.as_ptr(), 2));
        assert_eq!(truncate_str(s6, 3), (s6.as_ptr(), 2));
        assert_eq!(truncate_str(s6, 4), (s6.as_ptr(), 4));
        assert_eq!(truncate_str(s6, 254), (s6.as_ptr(), 253));
        assert_eq!(truncate_str(s6, 255), (s6.as_ptr(), 255));
    }

    #[test]
    fn test_new() {
        assert_eq!(&*CappedString::<5>::new("").unwrap(), "");
        assert_eq!(&*CappedString::<5>::new("a").unwrap(), "a");
        assert_eq!(&*CappedString::<5>::new("hello").unwrap(), "hello");
        assert_eq!(&*CappedString::<6>::new("hello").unwrap(), "hello");
        assert!(CappedString::<5>::new("hello!").is_err());
        assert_eq!(&*CappedString::<6>::new("hello!").unwrap(), "hello!");
        assert_eq!(&*CappedString::<5>::new("こ").unwrap(), "こ");
        assert!(CappedString::<5>::new("こん").is_err());
        assert_eq!(&*CappedString::<6>::new("こん").unwrap(), "こん");
        assert!(CappedString::<6>::new("こんにちは").is_err());
        assert_eq!(&*CappedString::<0>::new("").unwrap(), "");
        assert!(CappedString::<0>::new("a").is_err());
    }

    #[test]
    fn test_new_truncating() {
        assert_eq!(&*CappedString::<5>::new_truncating(""), "");
        assert_eq!(&*CappedString::<5>::new_truncating("a"), "a");
        assert_eq!(&*CappedString::<5>::new_truncating("hello"), "hello");
        assert_eq!(&*CappedString::<6>::new_truncating("hello"), "hello");
        assert_eq!(&*CappedString::<5>::new_truncating("hello!"), "hello");
        assert_eq!(&*CappedString::<6>::new_truncating("hello!"), "hello!");
        assert_eq!(&*CappedString::<5>::new_truncating("こ"), "こ");
        assert_eq!(&*CappedString::<5>::new_truncating("こん"), "こ");
        assert_eq!(&*CappedString::<6>::new_truncating("こん"), "こん");
        assert_eq!(&*CappedString::<6>::new_truncating("こんにちは"), "こん");
        assert_eq!(&*CappedString::<7>::new_truncating("こんにちは"), "こん");
        assert_eq!(&*CappedString::<8>::new_truncating("こんにちは"), "こん");
        assert_eq!(&*CappedString::<9>::new_truncating("こんにちは"), "こんに");
        assert_eq!(&*CappedString::<3>::new_truncating("🤖 hello 🤖"), "");
        assert_eq!(&*CappedString::<4>::new_truncating("🤖 hello 🤖"), "🤖");
        assert_eq!(&*CappedString::<14>::new_truncating("🤖 hello 🤖"), "🤖 hello ");
        assert_eq!(&*CappedString::<15>::new_truncating("🤖 hello 🤖"), "🤖 hello 🤖");
        assert_eq!(&*CappedString::<20>::new_truncating("🤖 hello 🤖"), "🤖 hello 🤖");
        assert_eq!(&*CappedString::<0>::new_truncating(""), "");
        assert_eq!(&*CappedString::<0>::new_truncating("a"), "");
    }

    #[test]
    fn test_push() {
        let mut s = CappedString::<6>::empty();
        s.push_str("").unwrap();
        assert_eq!(&*s, "");
        s.push('h').unwrap();
        assert_eq!(&*s, "h");
        s.push_str("ello").unwrap();
        assert_eq!(&*s, "hello");
        assert!(s.push_str(", world").is_err());
        assert_eq!(&*s, "hello");
    }

    #[test]
    fn test_push_truncating() {
        let mut s = CappedString::<6>::empty();

        s.push_str_truncating("");
        assert_eq!(&*s, "");
        s.push_truncating('h');
        assert_eq!(&*s, "h");
        s.push_str_truncating("ello");
        assert_eq!(&*s, "hello");
        s.push_str_truncating(", world");
        assert_eq!(&*s, "hello,");
        
        s.clear();
        
        s.push_truncating('こ');
        assert_eq!(&*s, "こ");
        s.push_truncating('ん');
        assert_eq!(&*s, "こん");
        s.push_truncating('に');
        assert_eq!(&*s, "こん");

        s.clear();

        s.push_truncating('🤖');
        assert_eq!(&*s, "🤖");
        s.push_truncating('🤖');
        assert_eq!(&*s, "🤖");
        s.push_str_truncating("!!!");
        assert_eq!(&*s, "🤖!!");

        s.clear();

        s.push_str_truncating("🤖 ");
        assert_eq!(&*s, "🤖 ");
        s.push_truncating('🤖');
        assert_eq!(&*s, "🤖 ");

        s.clear();

        s.push_str_truncating("  ");
        assert_eq!(&*s, "  ");
        s.push_str_truncating("🤖🤖🤖");
        assert_eq!(&*s, "  🤖");
        s.push_truncating('!');
        assert_eq!(&*s, "  🤖");

        s.clear();

        s.push_str_truncating("   ");
        assert_eq!(&*s, "   ");
        s.push_truncating('🤖');
        assert_eq!(&*s, "   ");
        s.push_str_truncating("こんにちは");
        assert_eq!(&*s, "   こ");
    }
}
