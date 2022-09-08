use core::{
    borrow,
    cmp::Ordering,
    convert::Infallible,
    fmt,
    hash::{Hash, Hasher},
    mem::{self, ManuallyDrop, MaybeUninit},
    num::NonZeroU8,
    ops,
    ptr::{self, addr_of, addr_of_mut},
    slice,
    str,
};

#[cfg(not(feature = "std"))]
use alloc::{
    borrow::Cow,
    boxed::Box,
    rc::Rc,
    string::String,
    sync::Arc,
};

#[cfg(feature = "std")]
use std::{
    borrow::Cow,
    rc::Rc,
    sync::Arc,
};

/// A non-growable string where strings 23 bytes or shorter are stored inline and longer strings
/// use a separate heap allocation. If maximum inline lengths other than 23 are desired, see the
/// more general [InliningString].
/// 
/// 23 bytes is chosen because it is optimal for 64-bit architectures; the minimum possible size
/// of the data structure on 64-bit architectures which always keeps the data properly aligned is
/// 24 bytes (because, when heap-allocated, the data structure contains a 16-byte `Box<[u8]>` with
/// 8-byte alignment and a 1-byte discriminant, and the greatest multiple of 8 which is ≥17 is 24),
/// so there is space for 23 bytes of string data plus the 1-byte discriminant.
pub type InliningString23 = InliningString<23>;

/// A non-growable string which stores small strings inline; strings of length less than or equal
/// to `N` are stored inside the data structure itself, whereas strings of length greater than `N`
/// use a separate heap allocation.
/// 
/// This type is intended to be used when lots of small strings need to be stored, and these
/// strings do not need to grow.
/// 
/// For 64-bit targets, `N = 23` allows the greatest amount of inline string data to be stored
/// without exceeding the size of a regular [String]. Therefore, [InliningString23] is provided as
/// a type alias for `InliningString<23>`.
/// 
/// Although `N` is a `usize`, it may be no greater than `u8::MAX`; larger values will result in a
/// compile-time error.
/// 
/// ```
/// # use libshire::strings::InliningString;
/// let s1 = InliningString::<23>::new("This string is 23 bytes");
/// assert_eq!(&*s1, "This string is 23 bytes");
/// assert!(!s1.heap_allocated());
/// 
/// let s2 = InliningString::<23>::new("and this one is 24 bytes");
/// assert_eq!(&*s2, "and this one is 24 bytes");
/// assert!(s2.heap_allocated());
/// ```
#[repr(C)]
pub struct InliningString<const N: usize> {
    repr: Repr<N>,
    // When `discrim - 1` is less than or equal to `MAX_LEN`, `repr.inline` is active and the first
    // `discrim - 1` bytes of `repr.inline` contains initialised, valid UTF-8 data. When
    // `discrim - 1` is greater than `MAX_LEN`, `repr.boxed` is active. `NonZeroU8` is used to
    // allow for the niche optimisation
    // (https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#niche).
    discrim: NonZeroU8,
    // A zero-sized field to ensure that `InliningString` has an alignment equal to the alignment
    // of `Box<str>`, to ensure that `repr.boxed` is properly aligned when it is active.
    _align: [Box<str>; 0],
}

// `repr(C)` is necessary to ensure that both of the fields start at offset 0. `repr(packed)`
// reduces the alignment to 1, which allows `InliningString` to be more compact.
#[repr(C, packed)]
union Repr<const N: usize> {
    inline: [MaybeUninit<u8>; N],
    boxed: ManuallyDrop<MaybeUninit<Box<str>>>,
}

impl<const N: usize> InliningString<N> {
    const MAX_LEN: u8 = {
        #[allow(clippy::cast_possible_truncation, clippy::checked_conversions)]
        // `MAX_LEN` may be no larger than `u8::MAX - 2` to leave at least one bit pattern to
        // represent the "boxed" case and at least one bit pattern for the niche optimisation.
        if N <= (u8::MAX - 2) as usize {
            N as u8
        } else {
            panic!("`N` must be no greater than `u8::MAX - 2`")
        }
    };

    /// Creates a new `InliningString` from the given string, storing the string data inline if
    /// possible or creating a new heap allocation otherwise.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s = InliningString::<23>::new("Hello, InliningString!");
    /// assert_eq!(&*s, "Hello, InliningString!");
    /// ```
    #[must_use]
    pub fn new<S>(s: S) -> Self
    where
        S: AsRef<str>,
        Box<str>: From<S>,
    {
        let src = s.as_ref().as_bytes();

        match u8::try_from(src.len()) {
            Ok(len) if len <= Self::MAX_LEN => {
                unsafe {
                    // SAFETY:
                    // `MaybeUninit::uninit()` is a valid value for `[MaybeUninit<u8>; N]`, since
                    // each element of the array is allowed to be uninitialised.
                    let mut buf = MaybeUninit::<[MaybeUninit<u8>; N]>::uninit()
                        .assume_init();

                    // Cast the byte slice to a `MaybeUninit<u8>` pointer. This is valid because
                    // `u8` has the same memory layout as `MaybeUninit<u8>`.
                    let src_ptr = src.as_ptr() as *const MaybeUninit<u8>;

                    // Copy the string data provided by the caller into the buffer.
                    // SAFETY:
                    // The source is valid because the source and length are both taken from a
                    // valid `&[u8]`. We have already checked in the match statement that there is
                    // enough space in the buffer to fit the string data (i.e. `len` is less than
                    // or equal to `MAX_LEN`, which is equal to `N`), so the destination is valid.
                    // The source and destination are trivially properly aligned because the
                    // alignment of `MaybeUninit<u8>` is 1. The source and destination do not
                    // overlap; the destination buffer is a new variable completely separate from
                    // the source data.
                    ptr::copy_nonoverlapping(src_ptr, buf.as_mut_ptr(), usize::from(len));

                    // SAFETY:
                    // The first `len` bytes of `buf` are copied from a `&str`, so the first `len`
                    // bytes are valid UTF-8. We have already checked that `len` is thess than or
                    // equal to `Self::MAX_LEN`.
                    Self::inline_from_raw_parts(buf, len)
                }
            },

            _ => Self::new_boxed(s),
        }
    }

    /// Returns a new empty `InliningString`.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s = InliningString::<23>::empty();
    /// assert_eq!(&*s, "");
    /// ```
    #[inline]
    #[must_use]
    pub fn empty() -> Self {
        unsafe {
            // SAFETY:
            // `MaybeUninit::uninit()` is a valid value for `[MaybeUninit<u8>; N]`, since each
            // element of the array is allowed to be uninitialised.
            let buf = MaybeUninit::<[MaybeUninit<u8>; N]>::uninit()
                .assume_init();

            // SAFETY:
            // `len` is 0, so the contract that the first `len` bytes of `buf` are initialised and
            // valid UTF-8 is trivially upheld.
            Self::inline_from_raw_parts(buf, 0)
        }
    }

    /// # Safety
    /// The first `len` bytes of `buf` must be initialised and valid UTF-8. `len` must be less than
    /// or equal to `Self::MAX_LEN` (which is equal to `N`).
    #[inline]
    unsafe fn inline_from_raw_parts(buf: [MaybeUninit<u8>; N], len: u8) -> Self {
        // SAFETY:
        // The caller is responsible for ensuring that `len` is less than or equal to
        // `Self::MAX_LEN`, which is no greater than `u8::MAX - 2`. If this contract is upheld,
        // `len + 1` can never overflow, so `len + 1` can never be zero.
        let discrim = unsafe { NonZeroU8::new_unchecked(len + 1) };

        Self {
            repr: Repr { inline: buf },
            discrim,
            _align: [],
        }
    }

    #[inline]
    fn new_boxed<S>(s: S) -> Self
    where
        Box<str>: From<S>,
    {
        const U8_NONZERO_MAX: NonZeroU8 = unsafe { NonZeroU8::new_unchecked(u8::MAX) };

        Self {
            repr: Repr {
                boxed: ManuallyDrop::new(MaybeUninit::new(Box::from(s))),
            },
            discrim: U8_NONZERO_MAX,
            _align: [],
        }
    }

    /// If the `inline` field is active, returns the length of the inline string data. If the
    /// `boxed` field is active, returns `None`.
    #[inline(always)]
    fn inline_string_len(&self) -> Option<u8> {
        let len = self.discrim.get() - 1;
        if len <= Self::MAX_LEN {
            Some(len)
        } else {
            None
        }
    }

    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self.inline_string_len() {
            Some(len) => {
                // Get a pointer to the `inline` field of the union.
                // SAFETY:
                // Since `inline_string_len` returned `Some`, the `inline` field must be active.
                let inline_buf_ptr = unsafe { addr_of!(self.repr.inline) }
                    as *const MaybeUninit<u8>
                    as *const u8;

                // Construct a byte slice from the pointer to the string data and the length.
                // SAFETY:
                // The first `len` bytes of `inline` are always initialised, as this is an
                // invariant of `InliningString`.
                let inline_buf_slice = unsafe { slice::from_raw_parts(inline_buf_ptr, usize::from(len)) };

                // Perform an unchecked conversion from the byte slice to a string slice.
                // SAFETY:
                // The first `len` bytes of `inline` is always valid UTF-8, as this is an invariant
                // of `InliningString`.
                unsafe { str::from_utf8_unchecked(inline_buf_slice) }
            },

            None => {
                // SAFETY:
                // `inline_string_len` returned `None`, which means that the `boxed` field is
                // active. `boxed` is properly aligned because it is stored at offset 0 of
                // `InliningString` (since both `InliningString` and `Repr` use `repr(C)`), and the
                // alignment of `InliningString` is equal to the alignment of `Box<str>`.
                let maybe_boxed_buf = unsafe { &*addr_of!(self.repr.boxed) };

                // SAFETY:
                // `repr.boxed` is initialised, as the only time it's uninitialised is when it is
                // briefly replaced with a temporary value before the `InliningString` is dropped
                // in the `into_string` function.
                unsafe { maybe_boxed_buf.assume_init_ref() }
            },
        }
    }

    #[inline]
    #[must_use]
    pub fn as_str_mut(&mut self) -> &mut str {
        match self.inline_string_len() {
            Some(len) => {
                // Get a pointer to the `inline` field of the union.
                // SAFETY:
                // Since `inline_string_len` returned `Some`, the `inline` field must be active.
                let inline_buf_ptr = unsafe { addr_of_mut!(self.repr.inline) }
                    as *mut MaybeUninit<u8>
                    as *mut u8;

                // Construct a byte slice from the pointer to the string data and the length.
                // SAFETY:
                // The first `len` bytes of `inline` are always initialised, as this is an
                // invariant of `InliningString`.
                let inline_buf_slice = unsafe { slice::from_raw_parts_mut(inline_buf_ptr, usize::from(len)) };

                // Perform an unchecked conversion from the byte slice to a string slice.
                // SAFETY:
                // The first `len` bytes of `inline` is always valid UTF-8, as this is an invariant
                // of `InliningString`.
                unsafe { str::from_utf8_unchecked_mut(inline_buf_slice) }
            },

            None => {
                // SAFETY:
                // `inline_string_len` returned `None`, which means that the `boxed` field is
                // active. `boxed` is properly aligned because it is stored at offset 0 of
                // `InliningString` (since both `InliningString` and `Repr` use `repr(C)`), and the
                // alignment of `InliningString` is equal to the alignment of `Box<str>`.
                let maybe_boxed_buf = unsafe { &mut *addr_of_mut!(self.repr.boxed) };

                // SAFETY:
                // `repr.boxed` is initialised, as the only time it's uninitialised is when it is
                // briefly replaced with a temporary value before the `InliningString` is dropped
                // in the `into_string` function.
                unsafe { maybe_boxed_buf.assume_init_mut() }
            },
        }
    }

    #[inline]
    #[must_use]
    pub fn into_boxed_str(self) -> Box<str> {
        match self.inline_string_len() {
            Some(len) => {
                // Get a pointer to the `inline` field of the union.
                // SAFETY:
                // Since `inline_string_len` returned `Some`, the `inline` field must be active.
                let inline_buf_ptr = unsafe { addr_of!(self.repr.inline) }
                    as *const MaybeUninit<u8>
                    as *const u8;

                // Construct a byte slice from the pointer to the string data and the length.
                // SAFETY:
                // The first `len` bytes of `inline` are always initialised, as this is an
                // invariant of `InliningString`.
                let inline_buf_slice = unsafe { slice::from_raw_parts(inline_buf_ptr, usize::from(len)) };

                // Perform an unchecked conversion from the byte slice to a string slice.
                // SAFETY:
                // The first `len` bytes of `inline` is always valid UTF-8, as this is an invariant
                // of `InliningString`.
                let str_slice = unsafe { str::from_utf8_unchecked(inline_buf_slice) };

                Box::from(str_slice)
            },

            None => {
                let manual_boxed_buf = {
                    // Disable the destructor for `self`; we are transferring ownership of the
                    // allocated memory to the caller, so we don't want to run the destructor which
                    // would free the memory.
                    let mut this = ManuallyDrop::new(self);

                    // SAFETY:
                    // `inline_string_len` returned `None`, which means that the `boxed` field is
                    // active. `boxed` is properly aligned because it is stored at offset 0 of
                    // `InliningString` (since both `InliningString` and `Repr` use `repr(C)`), and
                    // the alignment of `InliningString` is equal to the alignment of `Box<str>`.
                    let field_ref = unsafe { &mut *addr_of_mut!(this.repr.boxed) };

                    // Move `repr.boxed` out of the `InliningString`, replacing it with
                    // uninitialised memory. This is sound because we have ownership of the
                    // `InliningString` and we will not be doing anything else with it after this
                    // which calls `assume_init` on `repr.boxed`; at the end of this block, the
                    // `InliningString` is dropped without calling its destructor.
                    mem::replace(field_ref, ManuallyDrop::new(MaybeUninit::uninit()))
                };

                // Re-enable the destructor for the boxed string.
                let maybe_boxed_buf = ManuallyDrop::into_inner(manual_boxed_buf);

                // SAFETY:
                // The boxed string is initialised, as we obtained it by moving `repr.boxed`, and
                // the only time `repr.boxed` is uninitialised is when it is briefly replaced with
                // a temporary value in the block above.
                unsafe { maybe_boxed_buf.assume_init() }
            },
        }
    }

    #[inline]
    #[must_use]
    pub fn into_string(self) -> String {
        self.into_boxed_str()
            .into_string()
    }

    /// Returns `true` if and only if the string data uses a separate heap allocation.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s1 = InliningString::<23>::new("This string is 23 bytes");
    /// assert!(!s1.heap_allocated());
    ///
    /// let s2 = InliningString::<23>::new("and this one is 24 bytes");
    /// assert!(s2.heap_allocated());
    /// ```
    #[inline]
    #[must_use]
    pub fn heap_allocated(&self) -> bool {
        self.inline_string_len().is_none()
    }

    /// Returns the length of the string in bytes.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s = InliningString::<23>::new("こんにちは");
    /// assert_eq!(s.len(), 15);
    /// ```
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.as_str().len()
    }

    /// Returns `true` if the string has length 0.
    ///
    /// ```
    /// # use libshire::strings::InliningString;
    /// let s1 = InliningString::<23>::new("");
    /// assert!(s1.is_empty());
    ///
    /// let s2 = InliningString::<23>::new("Hello");
    /// assert!(!s2.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }
}

impl<const N: usize> Drop for InliningString<N> {
    fn drop(&mut self) {
        if self.heap_allocated() {
            let boxed_buf = unsafe { &mut *addr_of_mut!(self.repr.boxed) };

            // SAFETY:
            // Since this is a drop implementation, `boxed` will not be used again after this.
            let _ = unsafe { ManuallyDrop::take(boxed_buf).assume_init() };
        }
    }
}

impl<const N: usize> Clone for InliningString<N> {
    fn clone(&self) -> Self {
        match self.inline_string_len() {
            Some(len) => {
                // SAFETY:
                // Since `inline_string_len` returned `Some`, the `inline` field must be active.
                let inline_buf_copy = unsafe { *addr_of!(self.repr.inline) };

                // SAFETY:
                // The first `len` bytes of the buffer are initialised and valid UTF-8, as this is
                // an invariant of the `InliningString` from which the buffer and length were 
                // copied.
                unsafe { Self::inline_from_raw_parts(inline_buf_copy, len) }
            },

            None => {
                // SAFETY:
                // `inline_string_len` returned `None`, which means that the `boxed` field is
                // active. `boxed` is properly aligned because it is stored at offset 0 of
                // `InliningString` (since both `InliningString` and `Repr` use `repr(C)`), and the
                // alignment of `InliningString` is equal to the alignment of `Box<str>`.
                let maybe_boxed_buf = unsafe { &*addr_of!(self.repr.boxed) };

                // SAFETY:
                // `repr.boxed` is initialised, as the only time it's uninitialised is when it is
                // briefly replaced with a temporary value before the `InliningString` is dropped
                // in the `into_string` function.
                let boxed_buf = unsafe { maybe_boxed_buf.assume_init_ref() };

                Self::new_boxed(boxed_buf.clone())
            },
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

impl<const N: usize> str::FromStr for InliningString<N> {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s))
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

impl<const N: usize> From<Box<str>> for InliningString<N> {
    #[inline]
    fn from(s: Box<str>) -> Self {
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

impl<const N: usize> From<InliningString<N>> for Box<str> {
    #[inline]
    fn from(s: InliningString<N>) -> Self {
        s.into_boxed_str()
    }
}

impl<const N: usize> From<InliningString<N>> for Rc<str> {
    #[inline]
    fn from(s: InliningString<N>) -> Self {
        Rc::from(s.into_boxed_str())
    }
}

impl<const N: usize> From<InliningString<N>> for Arc<str> {
    #[inline]
    fn from(s: InliningString<N>) -> Self {
        Arc::from(s.into_boxed_str())
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

impl<const N: usize> fmt::Debug for InliningString<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for InliningString<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[cfg(feature = "serde")]
impl<const N: usize> serde::Serialize for InliningString<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer
    {
        serde::Serialize::serialize(&**self, serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> serde::Deserialize<'de> for InliningString<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>
    {
        #[cfg(not(feature = "std"))]
        use alloc::vec::Vec;

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

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "std"))]
    use alloc::{
        borrow::{Cow, ToOwned},
        vec::Vec,
    };

    #[cfg(feature = "std")]
    use std::borrow::Cow;

    use super::*;

    #[test]
    fn test_align() {
        use core::mem::align_of;
        assert_eq!(align_of::<InliningString23>(), align_of::<Box<str>>());
    }

    #[test]
    fn test_niche() {
        use core::mem::size_of;
        assert_eq!(size_of::<InliningString23>(), size_of::<Option<InliningString23>>());
    }

    #[test]
    fn test_empty() {
        assert_eq!(InliningString23::empty().as_str(), "");
        assert_eq!(InliningString23::empty().len(), 0);
        assert!(!InliningString23::empty().heap_allocated());
    }

    #[test]
    fn test_new() {
        let test_strings = [
            "",
            "Hello",
            "Somethingfortheweekend",
            "Dichlorodifluoromethane",
            "Electrocardiographically",
            "こんにちは",
            "❤️🧡💛💚💙💜",
        ];

        for s in test_strings {
            let buf = s.to_owned();
            let borrowed = Cow::Borrowed(s);
            let owned = Cow::<'static, str>::Owned(buf.clone());

            assert_eq!(InliningString23::new(s).as_str(), s);
            assert_eq!(InliningString23::new(buf).as_str(), s);
            assert_eq!(InliningString23::new(borrowed).as_str(), s);
            assert_eq!(InliningString23::new(owned).as_str(), s);
        }
    }

    #[test]
    fn test_contiguous() {
        let test_strings = [
            "",
            "Hello",
            "Somethingfortheweekend",
            "Dichlorodifluoromethane",
            "Electrocardiographically",
            "こんにちは",
            "❤️🧡💛💚💙💜",
        ];

        #[allow(clippy::needless_collect)]
        let vec = test_strings
            .iter()
            .copied()
            .map(InliningString23::new)
            .collect::<Vec<_>>();

        for (i, s) in vec.into_iter().enumerate() {
            assert_eq!(s.as_str(), test_strings[i]);
        }
    }

    #[test]
    fn test_clone() {
        let s1 = InliningString23::new("hello");
        assert!(!s1.heap_allocated());
        let s1_clone = s1.clone();
        assert_eq!(s1, s1_clone);
        assert_eq!(s1.as_str(), "hello");
        assert_ne!(s1.as_str().as_ptr(), s1_clone.as_str().as_ptr());

        let s2 = InliningString23::new("the quick brown fox jumps over the lazy dog");
        assert!(s2.heap_allocated());
        let s2_clone = s2.clone();
        assert_eq!(s2, s2_clone);
        assert_ne!(s1, s2_clone);
        assert_ne!(s1_clone, s2_clone);
        assert_eq!(s2.as_str(), "the quick brown fox jumps over the lazy dog");
        assert_ne!(s2.as_str().as_ptr(), s2_clone.as_str().as_ptr());

        let s3 = InliningString23::empty();
        assert!(!s3.heap_allocated());
        let s3_clone = s3.clone();
        assert_eq!(s3, s3_clone);
        assert_eq!(s3.as_str(), "");
        assert_ne!(s3.as_str().as_ptr(), s3_clone.as_str().as_ptr());
    }

    #[test]
    fn test_as_str_mut() {
        let mut s1 = InliningString23::new("hello");
        assert!(!s1.heap_allocated());
        s1.as_str_mut().make_ascii_uppercase();
        assert_eq!(s1.as_str(), "HELLO");

        let mut s2 = InliningString23::new("the quick brown fox jumps over the lazy dog");
        assert!(s2.heap_allocated());
        s2.as_str_mut().make_ascii_uppercase();
        assert_eq!(s2.as_str(), "THE QUICK BROWN FOX JUMPS OVER THE LAZY DOG");
    }

    #[test]
    fn test_into_string() {
        let test_strings = [
            "".to_owned(),
            "Hello".to_owned(),
            "Somethingfortheweekend".to_owned(),
            "Dichlorodifluoromethane".to_owned(),
            "Electrocardiographically".to_owned(),
            "こんにちは".to_owned(),
            "❤️🧡💛💚💙💜".to_owned(),
        ];

        for s in test_strings {
            assert_eq!(InliningString23::new(&*s).into_string(), s);
        }
    }

    #[test]
    fn test_len() {
        assert_eq!(InliningString23::new("").len(), 0);
        assert_eq!(InliningString23::new("Hello").len(), 5);
        assert_eq!(InliningString23::new("Somethingfortheweekend").len(), 22);
        assert_eq!(InliningString23::new("Dichlorodifluoromethane").len(), 23);
        assert_eq!(InliningString23::new("Electrocardiographically").len(), 24);
        assert_eq!(InliningString23::new("こんにちは").len(), 15);
        assert_eq!(InliningString23::new("❤️🧡💛💚💙💜").len(), 26);
    }

    #[test]
    fn test_heap_allocated() {
        assert!(!InliningString23::new("").heap_allocated());
        assert!(!InliningString23::new("Hello").heap_allocated());
        assert!(!InliningString23::new("Somethingfortheweekend").heap_allocated());
        assert!(!InliningString23::new("Dichlorodifluoromethane").heap_allocated());
        assert!(!InliningString23::new("こんにちは").heap_allocated());

        assert!(InliningString23::new("Electrocardiographically").heap_allocated());
        assert!(InliningString23::new("Squishedbuginsidethescreen").heap_allocated());
        assert!(InliningString23::new("❤️🧡💛💚💙💜").heap_allocated());
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
