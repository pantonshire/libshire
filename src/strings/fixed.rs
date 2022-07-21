use core::{
    borrow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops,
    str,
};

pub struct FixedString<const N: usize> {
    buf: [u8; N],
}

impl<const N: usize> FixedString<N> {
    #[inline]
    pub fn new(s: &str) -> Result<Self, Error> {
        // SAFETY:
        // A `&str` is always valid UTF-8.
        unsafe { Self::from_raw_slice(s.as_bytes()) }
    }

    /// # Safety
    /// The provided byte slice must be valid UTF-8.
    #[inline]
    pub unsafe fn from_raw_slice(bytes: &[u8]) -> Result<Self, Error> {
        match bytes.try_into() {
            Ok(bytes) => Ok(Self::from_raw_array(bytes)),
            Err(_) => Err(Error {
                expected_len: N,
                actual_len: bytes.len(),
            }),
        }
    }

    /// # Safety
    /// The provided byte array must be valid UTF-8.
    #[inline]
    #[must_use]
    pub unsafe fn from_raw_array(bytes: [u8; N]) -> Self {
        Self { buf: bytes }
    }

    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        // SAFETY:
        // `buf` is always valid UTF-8 since that is an invariant `FixedString`.
        unsafe { str::from_utf8_unchecked(&self.buf) }
    }

    #[inline]
    #[must_use]
    pub fn as_str_mut(&mut self) -> &mut str {
        // SAFETY:
        // `buf` is always valid UTF-8 since that is an invariant `FixedString`.
        unsafe { str::from_utf8_unchecked_mut(&mut self.buf) }
    }

    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; N] {
        &self.buf
    }

    #[inline]
    #[must_use]
    pub fn into_raw(self) -> [u8; N] {
        self.buf
    }
}

impl<const N: usize> ops::Deref for FixedString<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> ops::DerefMut for FixedString<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_str_mut()
    }
}

impl<const N: usize> AsRef<str> for FixedString<N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> AsMut<str> for FixedString<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> borrow::Borrow<str> for FixedString<N> {
    #[inline]
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> borrow::BorrowMut<str> for FixedString<N> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> str::FromStr for FixedString<N> {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(s)
    }
}

impl<'a, const N: usize> TryFrom<&'a str> for FixedString<N> {
    type Error = Error;

    #[inline]
    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl<const N: usize> PartialEq for FixedString<N> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<const N: usize> Eq for FixedString<N> {}

impl<const N: usize> PartialOrd for FixedString<N> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for FixedString<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<const N: usize> Hash for FixedString<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<const N: usize> fmt::Debug for FixedString<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for FixedString<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[derive(Debug)]
pub struct Error {
    expected_len: usize,
    actual_len: usize,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "expected {} bytes of string data, found {} bytes",
            self.expected_len,
            self.actual_len
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

#[cfg(test)]
mod tests {
    use super::FixedString;

    #[test]
    fn test_fixed_string() {
        assert!(FixedString::<5>::new("hello").is_ok());
        assert!(FixedString::<5>::new("hello!").is_err());
        assert!(FixedString::<5>::new("helo").is_err());
        assert!(FixedString::<5>::new("").is_err());
        assert_eq!(FixedString::<5>::new("hello").unwrap().as_bytes(), "hello".as_bytes());
    }

    #[test]
    fn test_fixed_string_zero() {
        assert!(FixedString::<0>::new("").is_ok());
        assert!(FixedString::<0>::new("a").is_err());
        assert!(FixedString::<0>::new("abc").is_err());
        assert_eq!(FixedString::<0>::new("").unwrap().as_bytes(), &[]);
    }
}
