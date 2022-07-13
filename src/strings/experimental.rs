use std::{
    borrow::{self, Cow},
    convert::Infallible,
    fmt,
    mem::{self, ManuallyDrop, MaybeUninit},
    ops,
    ptr::{self, addr_of, addr_of_mut},
    slice,
    str,
};

pub type ShString23 = ShString<23>;

/// An experimental alternative to `libshire::strings::ShString`, which is able to store one extra
/// byte of string data on the stack in the same amount of space.

// `repr(C)` is necessary to ensure that `Repr` starts at offset 0, so that it's properly aligned
// within the struct.
#[repr(C)]
pub struct ShString<const N: usize> {
    repr: Repr<N>,
    // When `len` is less than or equal to `MAX_LEN`, `repr.stack` is active and the first `len`
    // bytes of `repr.stack` contains initialised, valid UTF-8 data. When it is greater than
    // `MAX_LEN`, `repr.heap` is active.
    len: u8,
    // A zero-sized field to ensure that `ShString` has an alignment equal to the alignment of
    // `Box<str>`, to ensure that `repr.heap` is properly aligned when it is active.
    _align: [Box<str>; 0],
}

// `repr(C)` is necessary to ensure that both of the fields start at offset 0. `repr(packed)`
// reduces the alignment to 1, which allows `ShString` to be more compact.
#[repr(C, packed)]
union Repr<const N: usize> {
    stack: [MaybeUninit<u8>; N],
    heap: ManuallyDrop<MaybeUninit<Box<str>>>,
}

impl<const N: usize> ShString<N> {
    const MAX_LEN: u8 = {
        #[allow(clippy::cast_possible_truncation, clippy::checked_conversions)]
        // `MAX_LEN` may be no larger than `u8::MAX - 1` to leave at least one bit pattern to
        // represent the "stored on the heap" case.
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
        let src = s.as_ref().as_bytes();

        match u8::try_from(src.len()) {
            Ok(len) if len <= Self::MAX_LEN => {
                unsafe {
                    let mut buf = MaybeUninit::<[MaybeUninit<u8>; N]>::uninit()
                        .assume_init();

                    let src_ptr = src.as_ptr() as *const MaybeUninit<u8>;

                    ptr::copy_nonoverlapping(src_ptr, buf.as_mut_ptr(), usize::from(len));

                    // SAFETY:
                    // The first `len` bytes of `buf` are copied from a `&str`, so the first `len`
                    // bytes are valid UTF-8. We have already checked that `len` is thess than or
                    // equal to `Self::MAX_LEN`.
                    Self::stack_from_raw_parts(buf, len)
                }
            },

            _ => Self::new_heap(s),
        }
    }

    /// # Safety
    /// The first `len` bytes of `buf` must be valid UTF-8. `len` must be less than or equal to
    /// `Self::MAX_LEN` (which is equal to `N`).
    unsafe fn stack_from_raw_parts(buf: [MaybeUninit<u8>; N], len: u8) -> Self {
        Self {
            repr: Repr { stack: buf },
            len,
            _align: [],
        }
    }

    fn new_heap<S>(s: S) -> Self
    where
        Box<str>: From<S>,
    {
        Self {
            repr: Repr {
                heap: ManuallyDrop::new(MaybeUninit::new(Box::from(s))),
            },
            len: u8::MAX,
            _align: [],
        }
    }

    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        if self.heap_allocated() {
            // SAFETY:
            // `len` is greater than `Self::MAX_LEN`, which means that the `heap` field is
            // active. `heap` is properly aligned because it is stored at offset 0 of
            // `ShString` (since both `ShString` and `Repr` use `repr(C)`), and the alignment
            // of `ShString` is equal to the alignment of `Box<str>`.
            let box_str = unsafe { &*addr_of!(self.repr.heap) };

            unsafe { box_str.assume_init_ref() }
        } else {
            // Get a pointer to the `stack` field of the union.
            // SAFETY:
            // Since `len` is less no greater than `MAX_LEN`, the `stack` field must be
            // active.
            let ptr = unsafe { addr_of!(self.repr.stack) }
                as *const MaybeUninit<u8>
                as *const u8;

            // Construct a byte slice from the pointer to the string data and the length.
            // SAFETY:
            // The first `len` bytes of `stack` are always initialised, as this is an
            // invariant of `ShString`.
            let bytes = unsafe { slice::from_raw_parts(ptr, usize::from(self.len)) };

            // Perform an unchecked conversion from the byte slice to a string slice.
            // SAFETY:
            // The first `len` bytes of `stack` is always valid UTF-8, as this is an
            // invariant of `ShString`.
            unsafe { str::from_utf8_unchecked(bytes) }
        }
    }

    #[inline]
    #[must_use]
    pub fn as_str_mut(&mut self) -> &mut str {
        if self.heap_allocated() {
            // SAFETY:
            // `len` is greater than `Self::MAX_LEN`, which means that the `heap` field is
            // active. `heap` is properly aligned because it is stored at offset 0 of
            // `ShString` (since both `ShString` and `Repr` use `repr(C)`), and the alignment
            // of `ShString` is equal to the alignment of `Box<str>`.
            let box_str = unsafe { &mut *addr_of_mut!(self.repr.heap) };

            unsafe { box_str.assume_init_mut() }
        } else {
            // Get a pointer to the `stack` field of the union.
            // SAFETY:
            // Since `len` is less no greater than `MAX_LEN`, the `stack` field must be
            // active.
            let ptr = unsafe { addr_of_mut!(self.repr.stack) }
                as *mut MaybeUninit<u8>
                as *mut u8;

            // Construct a byte slice from the pointer to the string data and the length.
            // SAFETY:
            // The first `len` bytes of `stack` are always initialised, as this is an
            // invariant of `ShString`.
            let bytes = unsafe { slice::from_raw_parts_mut(ptr, usize::from(self.len)) };

            // Perform an unchecked conversion from the byte slice to a string slice.
            // SAFETY:
            // The first `len` bytes of `stack` is always valid UTF-8, as this is an
            // invariant of `ShString`.
            unsafe { str::from_utf8_unchecked_mut(bytes) }
        }
    }

    #[inline]
    #[must_use]
    pub fn into_string(self) -> String {
        if self.heap_allocated() {
            // Disable the destructor for `self`; we are transferring ownership of the allocated
            // memory to the caller, so we don't want to run the drop implementation which would
            // free the memory.
            let mut this = ManuallyDrop::new(self);

            // SAFETY:
            // `len` is greater than `Self::MAX_LEN`, which means that the `heap` field is
            // active. `heap` is properly aligned because it is stored at offset 0 of
            // `ShString` (since both `ShString` and `Repr` use `repr(C)`), and the alignment
            // of `ShString` is equal to the alignment of `Box<str>`.
            let field_ref = unsafe { &mut *addr_of_mut!(this.repr.heap) };

            let manual_box_str = mem::replace(field_ref, ManuallyDrop::new(MaybeUninit::uninit()));

            let maybe_box_str = ManuallyDrop::into_inner(manual_box_str);

            let box_str = unsafe { maybe_box_str.assume_init() };
            
            box_str.into_string()
        } else {
            // Get a pointer to the `stack` field of the union.
            // SAFETY:
            // Since `len` is less no greater than `MAX_LEN`, the `stack` field must be
            // active.
            let ptr = unsafe { addr_of!(self.repr.stack) }
                as *const MaybeUninit<u8>
                as *const u8;

            // Construct a byte slice from the pointer to the string data and the length.
            // SAFETY:
            // The first `len` bytes of `stack` are always initialised, as this is an
            // invariant of `ShString`.
            let bytes = unsafe { slice::from_raw_parts(ptr, usize::from(self.len)) };

            // Perform an unchecked conversion from the byte slice to a string slice.
            // SAFETY:
            // The first `len` bytes of `stack` is always valid UTF-8, as this is an
            // invariant of `ShString`.
            let str_slice = unsafe { str::from_utf8_unchecked(bytes) };

            str_slice.to_owned()
        }
    }

    #[inline]
    #[must_use]
    pub fn heap_allocated(&self) -> bool {
        self.len > Self::MAX_LEN
    }

    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.as_str().len()
    }

    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }
}

impl<const N: usize> Drop for ShString<N> {
    fn drop(&mut self) {
        if self.heap_allocated() {
            let heap = unsafe { &mut *addr_of_mut!(self.repr.heap) };

            // SAFETY:
            // Since this is a drop implementation, `heap` will not be used again after this.
            let _ = unsafe { ManuallyDrop::take(heap).assume_init() };
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

impl<const N: usize> str::FromStr for ShString<N> {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s))
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

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use super::*;

    #[test]
    fn test_align() {
        use std::mem::align_of;
        assert_eq!(align_of::<ShString<23>>(), align_of::<Box<str>>());
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

            assert_eq!(ShString23::new(s).as_str(), s);
            assert_eq!(ShString23::new(buf).as_str(), s);
            assert_eq!(ShString23::new(borrowed).as_str(), s);
            assert_eq!(ShString23::new(owned).as_str(), s);
        }
    }

    #[test]
    fn test_as_str_mut() {
        let mut s1 = ShString23::new("hello");
        s1.as_str_mut().make_ascii_uppercase();
        assert_eq!(s1.as_str(), "HELLO");

        let mut s2 = ShString23::new("the quick brown fox jumps over the lazy dog");
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
            assert_eq!(ShString23::new(&*s).into_string(), s);
        }
    }

    #[test]
    fn test_len() {
        assert_eq!(ShString23::new("").len(), 0);
        assert_eq!(ShString23::new("Hello").len(), 5);
        assert_eq!(ShString23::new("Somethingfortheweekend").len(), 22);
        assert_eq!(ShString23::new("Dichlorodifluoromethane").len(), 23);
        assert_eq!(ShString23::new("Electrocardiographically").len(), 24);
        assert_eq!(ShString23::new("こんにちは").len(), 15);
        assert_eq!(ShString23::new("❤️🧡💛💚💙💜").len(), 26);
    }

    #[test]
    fn test_heap_allocated() {
        assert!(!ShString23::new("").heap_allocated());
        assert!(!ShString23::new("Hello").heap_allocated());
        assert!(!ShString23::new("Somethingfortheweekend").heap_allocated());
        assert!(!ShString23::new("Dichlorodifluoromethane").heap_allocated());
        assert!(!ShString23::new("こんにちは").heap_allocated());

        assert!(ShString23::new("Electrocardiographically").heap_allocated());
        assert!(ShString23::new("Squishedbuginsidethescreen").heap_allocated());
        assert!(ShString23::new("❤️🧡💛💚💙💜").heap_allocated());
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
