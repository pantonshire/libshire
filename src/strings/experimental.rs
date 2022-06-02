use std::{
    borrow,
    fmt,
    mem::ManuallyDrop,
    ops,
    ptr::{addr_of, addr_of_mut},
    slice,
    str,
};

use crate::either::Either::{self, Inl, Inr};

/// An experimental alternative to `libshire::strings::ShString`, which is able to store one extra
/// byte of string data on the stack in the same amount of space.
// `repr(C)` is necessary to ensure that `Repr` starts at offset zero, so that it's properly
// aligned within the struct.
#[repr(C)]
pub struct ShString<const N: usize> {
    repr: Repr<N>,
    len: u8,
    _align: [Box<str>; 0],
}

#[repr(C, packed)]
union Repr<const N: usize> {
    stack: [u8; N],
    heap: ManuallyDrop<Box<str>>,
}

impl<const N: usize> ShString<N> {
    const MAX_LEN: u8 = {
        #[allow(clippy::cast_possible_truncation, clippy::checked_conversions)]
        if N < u8::MAX as usize {
            N as u8
        } else {
            panic!("`N` must be less than `u8::MAX`")
        }
    };

    #[must_use]
    pub fn new<S>(s: S) -> Self
    where
        S: AsRef<str>,
        Box<str>: From<S>,
    {
        let bytes = s.as_ref().as_bytes();
        match u8::try_from(bytes.len()) {
            Ok(len) if len <= Self::MAX_LEN => {
                let mut buf = [0u8; N];
                buf[..usize::from(len)].copy_from_slice(bytes);
                // SAFETY:
                // The first `len` bytes of `buf` are copied from a `&str`, so the first `len`
                // bytes are valid UTF-8. We have already checked that `len` is thess than or equal
                // to `Self::MAX_LEN`.
                unsafe { Self::stack_from_raw_parts(buf, len) }
            },
            _ => Self::new_heap(s),
        }
    }

    /// # Safety
    /// The first `len` bytes of `buf` must be valid UTF-8. `len` must be less than or equal to
    /// `Self::MAX_LEN` (which is equal to `N`).
    unsafe fn stack_from_raw_parts(buf: [u8; N], len: u8) -> Self {
        Self {
            repr: Repr { stack: buf },
            len,
            _align: []
        }
    }

    fn new_heap<S>(s: S) -> Self
    where
        Box<str>: From<S>,
    {
        Self {
            repr: Repr { heap: ManuallyDrop::new(Box::<str>::from(s)) },
            len: u8::MAX,
            _align: [],
        }
    }

    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self.variant() {
            // SAFETY:
            // `stack` being valid UTF-8 when active is an invariant of `ShString`.
            Inl(stack) => unsafe { str::from_utf8_unchecked(stack) },
            Inr(heap) => heap,
        }
    }

    #[inline]
    #[must_use]
    pub fn as_str_mut(&mut self) -> &mut str {
        match self.variant_mut() {
            // SAFETY:
            // `stack` being valid UTF-8 when active is an invariant of `ShString`.
            Inl(stack) => unsafe { str::from_utf8_unchecked_mut(stack) },
            Inr(heap) => heap,
        }
    }

    #[inline(always)]
    #[must_use]
    fn variant(&self) -> Either<&[u8], &ManuallyDrop<Box<str>>> {
        if self.len <= Self::MAX_LEN {
            let slice = unsafe {
                // The preferred way to read the fields of a packed struct is with `addr_of`.
                let ptr = addr_of!(self.repr.stack) as *const u8;
                let len = usize::from(self.len);
                slice::from_raw_parts(ptr, len)
            };
            Inl(slice)
        } else {
            // SAFETY:
            // `len` is greater than `Self::MAX_LEN`, which means that the `heap` field is active.
            // `heap` is properly aligned because it is stored at offset 0 of `ShString` (since
            // both `ShString` and `Repr` use `repr(C)`), and the alignment of `ShString` is equal
            // to the alignment of `Box<str>`.
            let heap = unsafe { &*addr_of!(self.repr.heap) };
            Inr(heap)
        }
    }

    #[inline(always)]
    #[must_use]
    fn variant_mut(&mut self) -> Either<&mut [u8], &mut ManuallyDrop<Box<str>>> {
        if self.len <= Self::MAX_LEN {
            let slice = unsafe {
                let ptr = addr_of_mut!(self.repr.stack) as *mut u8;
                let len = usize::from(self.len);
                slice::from_raw_parts_mut(ptr, len)
            };
            Inl(slice)
        } else {
            let heap = unsafe { &mut *addr_of_mut!(self.repr.heap) };
            Inr(heap)
        }
    }
}

impl<const N: usize> Drop for ShString<N> {
    fn drop(&mut self) {
        if let Inr(heap) = self.variant_mut() {
            // SAFETY:
            // Since this is a drop implementation, `heap` will not be used again after this.
            unsafe {
                let _ = ManuallyDrop::take(heap);
            }
        }
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

impl<const N: usize> fmt::Debug for ShString<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for ShString<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

// TODO: ** lots of MIRI tests! **

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shstring_align() {
        use std::mem::align_of;
        assert_eq!(align_of::<ShString<23>>(), align_of::<Box<str>>());
    }
}
