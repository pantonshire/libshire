// Following:
// - RFC 3986 (https://www.rfc-editor.org/rfc/rfc3986#section-2.1)
// - URL standard (https://url.spec.whatwg.org/#application/x-www-form-urlencoded)

use core::str;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{borrow::Cow, boxed::Box, string::String, vec::Vec};

#[cfg(feature = "std")]
use std::borrow::Cow;

use crate::{sink::StrSink, strings::FixedString};

use super::hex;

/// Finds the first element of the slice which matches the given predicate and returns the sub-slice
/// preceding that element, the element itself, and the sub-slice following the element.
#[inline]
fn split_at<T, P>(xs: &[T], predicate: P) -> (&[T], Option<(T, &[T])>)
where
    T: Copy,
    P: Fn(T) -> bool,
{
    let mut i = 0;

    while i < xs.len() {
        // Since we required that `T: Copy`, we can copy the `i`th element from the slice.
        let x = xs[i];

        if predicate(x) {
            // `get_unchecked` is used here because the compiler currently seems to struggle to
            // reason about the correctness of the start and end indexes here, and can end up
            // leaving in unnecessary bound checks.
            // SAFETY:
            // We have already checked that `i < xs.len()`, so `..i` is in bounds for `xs`.
            let prefix = unsafe { xs.get_unchecked(..i) };

            // SAFETY:
            // We have already checked that `i < xs.len()`, so `i + 1 <= xs.len()` must hold.
            // Therefore, `(i + 1)..` is in bounds for `xs`.
            let suffix = unsafe { xs.get_unchecked((i + 1)..) };

            return (prefix, Some((x, suffix)));
        }

        i += 1;
    }

    (xs, None)
}

pub struct PercentEncoder<'a> {
    remaining: &'a [u8],
}

impl<'a> PercentEncoder<'a> {
    #[must_use]
    pub fn new<B>(bytes: &'a B) -> Self
    where
        B: AsRef<[u8]> + ?Sized,
    {
        Self {
            remaining: bytes.as_ref(),
        }
    }

    fn percent_encode_byte(byte: u8) -> FixedString<3> {
        let [msb, lsb] = hex::byte_to_hex_upper(byte).into_raw();
        // SAFETY:
        // The bytes obtained from `hex::byte_to_hex_upper` are valid UTF-8, and `b'%'` is a valid
        // UTF-8 codepoint, so the byte array is valid UTF-8.
        unsafe { FixedString::from_raw_array([b'%', msb, lsb]) }
    }
}

impl<'a> Iterator for PercentEncoder<'a> {
    type Item = (&'a str, Option<FixedString<3>>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining.is_empty() {
            return None;
        }

        // Split at the first character which does not belong to RFC 3986's "unreserved" set,
        // which is the set of characters which do not need to be percent-encoded. This will give us
        // a `prefix` consisting entirely of characters which do not need to be percent-encoded,
        // followed by a `suffix` which is either `None` or starts which a  character which needs
        // to be percent-encoded.
        let (prefix, suffix) = split_at(
            self.remaining,
            |b| !matches!(b, b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z' | b'-' | b'.' | b'_' | b'~'),
        );

        // SAFETY:
        // `prefix` only contains characters in the unreserved set, which are all valid ASCII
        // characters. Therefore, it is valid UTF-8.
        let prefix = unsafe { str::from_utf8_unchecked(prefix) };

        match suffix {
            // If there is a suffix, return the prefix and the percent-encoded first byte of the
            // suffix. Set the iterator's slice to the remainder of the suffix, ready to be
            // percent-encoded at the next call to `next`.
            Some((byte, suffix)) => {
                self.remaining = suffix;
                Some((prefix, Some(Self::percent_encode_byte(byte))))
            }

            // If there's no suffix, then we've reached the end of the input string. Therefore, we
            // set the length of the iterator's slice to 0 to indicate that we are done, and then
            // return the prefix.
            None => {
                self.remaining = &self.remaining[self.remaining.len()..];
                Some((prefix, None))
            }
        }
    }
}

#[cfg(feature = "alloc")]
#[must_use]
pub fn percent_encode<B>(bytes: &B) -> Cow<str>
where
    B: AsRef<[u8]> + ?Sized,
{
    let mut encoder = PercentEncoder::new(bytes);

    match encoder.next() {
        Some((prefix, Some(encoded_byte))) => {
            let mut buf = String::new();
            buf.push_str(prefix);
            buf.push_str(&encoded_byte);

            for (prefix, encoded_byte) in encoder {
                buf.push_str(prefix);
                if let Some(encoded_byte) = encoded_byte {
                    buf.push_str(&encoded_byte);
                }
            }

            Cow::Owned(buf)
        }

        Some((prefix, None)) => Cow::Borrowed(prefix),

        None => Cow::Borrowed(""),
    }
}

#[cfg(feature = "alloc")]
pub fn percent_encode_to_buf<B>(buf: &mut String, bytes: &B)
where
    B: AsRef<[u8]> + ?Sized,
{
    use crate::{convert::result_elim, sink::StringSink};

    let sink = StringSink::from_string_mut(buf);
    result_elim(percent_encode_to(sink, bytes))
}

pub fn percent_encode_to<S, B>(sink: &mut S, bytes: &B) -> Result<(), S::Error>
where
    S: StrSink + ?Sized,
    B: AsRef<[u8]> + ?Sized,
{
    for (prefix, encoded_byte) in PercentEncoder::new(bytes) {
        if !prefix.is_empty() {
            sink.sink_str(prefix)?;
        }
        if let Some(encoded_byte) = encoded_byte {
            sink.sink_str(&encoded_byte)?;
        }
    }

    Ok(())
}

pub struct PercentDecoder<'a, M> {
    remaining: &'a [u8],
    mode: M,
}

impl<'a, M> PercentDecoder<'a, M> {
    pub fn new<B>(bytes: &'a B, mode: M) -> Self
    where
        B: AsRef<[u8]> + ?Sized,
    {
        Self {
            remaining: bytes.as_ref(),
            mode,
        }
    }
}

impl<'a, M> Iterator for PercentDecoder<'a, M>
where
    M: PercentDecodeMode,
{
    type Item = (&'a [u8], Option<u8>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining.is_empty() {
            return None;
        }

        let mut i = 0;

        while i < self.remaining.len() {
            // The '+' character being decoded to a space does not appear in the URL standard
            // section on percent-encoding, but it does appear in the section on
            // application/x-www-form-urlencoded. We implement it here as an optional feature to
            // simplify things.
            if self.mode.plus_space() && self.remaining[i] == b'+' {
                // SAFETY:
                // `i < self.remaining.len()`, so `..i` is a valid range over the slice.
                let prefix = unsafe { self.remaining.get_unchecked(..i) };

                // SAFETY:
                // `i < self.remaining.len()`, so `i + 1 <= self.remaining.len()`. Therefore,
                // `(i + 1)..` is a valid range over the slice.
                self.remaining = unsafe { self.remaining.get_unchecked((i + 1)..) };

                return Some((prefix, Some(b' ')));
            }

            // According to the URL standard, the only special case we need to handle is when the
            // percent character '%' is followed immediately by two hex digits. We check that there
            // are at least two characters after the percent with `self.remaining.len() - i > 2`,
            // using a subtraction rather than an addition to avoid overflow in the (rather far-
            // fetched) case where `self.remaining.len() == usize::MAX` and `i == usize::MAX - 1`.
            if self.remaining[i] == b'%' && self.remaining.len() - i > 2 {
                // Get the next two bytes after the percent character. We use unchecked methods here
                // because the current compiler does not seem to be able to eliminate the bounds
                // checks on its own.
                // SAFETY:
                // We have just checked that `self.remaining.len() - i > 2` holds. Rearranging this
                // gives `i + 2 < self.remaining.len()`. Therefore, `i + 1` and `i + 2` are valid
                // indexes into the slice.
                let (msb, lsb) = unsafe {
                    (
                        *self.remaining.get_unchecked(i + 1),
                        *self.remaining.get_unchecked(i + 2),
                    )
                };

                // If the two bytes are valid hex digits, decode the hex number.
                if let Ok(decoded) = hex::hex_to_byte(msb, lsb) {
                    // SAFETY:
                    // `i < self.remaining.len()`, so `..i` is a valid range over the slice.
                    let prefix = unsafe { self.remaining.get_unchecked(..i) };

                    // SAFETY:
                    // As explained above, `i + 2 < self.remaining.len()` must hold at this point.
                    // Therefore, `i + 3 <= self.remaining.len()`, so `(i + 3)..` is a valid range
                    // over the slice.
                    self.remaining = unsafe { self.remaining.get_unchecked((i + 3)..) };

                    return Some((prefix, Some(decoded)));
                }
            }

            i += 1;
        }

        let bytes = self.remaining;
        self.remaining = &self.remaining[i..];

        Some((bytes, None))
    }
}

pub trait PercentDecodeMode: percent_decode_mode::PercentDecodeModeSealed {}

impl<T: PercentDecodeMode> PercentDecodeMode for &T {}

#[cfg(feature = "alloc")]
impl<T: PercentDecodeMode> PercentDecodeMode for Box<T> {}

pub struct StandardDecode;

impl PercentDecodeMode for StandardDecode {}

pub struct FormDecode;

impl PercentDecodeMode for FormDecode {}

mod percent_decode_mode {
    #[cfg(all(feature = "alloc", not(feature = "std")))]
    use alloc::boxed::Box;

    pub trait PercentDecodeModeSealed {
        fn plus_space(&self) -> bool;
    }

    impl<T: PercentDecodeModeSealed> PercentDecodeModeSealed for &T {
        #[inline]
        fn plus_space(&self) -> bool {
            T::plus_space(self)
        }
    }

    #[cfg(feature = "alloc")]
    impl<T: PercentDecodeModeSealed> PercentDecodeModeSealed for Box<T> {
        #[inline]
        fn plus_space(&self) -> bool {
            T::plus_space(&**self)
        }
    }

    impl PercentDecodeModeSealed for super::StandardDecode {
        #[inline]
        fn plus_space(&self) -> bool {
            false
        }
    }

    impl PercentDecodeModeSealed for super::FormDecode {
        #[inline]
        fn plus_space(&self) -> bool {
            true
        }
    }
}

#[cfg(feature = "alloc")]
pub fn percent_decode<B, M>(bytes: &B, mode: M) -> Cow<[u8]>
where
    B: AsRef<[u8]> + ?Sized,
    M: PercentDecodeMode,
{
    let mut decoder = PercentDecoder::new(bytes, mode);

    match decoder.next() {
        Some((prefix, Some(byte))) => {
            let mut buf = Vec::new();
            buf.extend(prefix);
            buf.push(byte);

            for (prefix, byte) in decoder {
                buf.extend(prefix);
                if let Some(byte) = byte {
                    buf.push(byte);
                }
            }

            Cow::Owned(buf)
        }

        Some((prefix, None)) => Cow::Borrowed(prefix),

        None => Cow::Borrowed(&[]),
    }
}

#[cfg(feature = "alloc")]
pub fn percent_decode_utf8<B, M>(bytes: &B, mode: M) -> Cow<str>
where
    B: AsRef<[u8]> + ?Sized,
    M: PercentDecodeMode,
{
    match percent_decode(bytes, mode) {
        Cow::Borrowed(decoded) => String::from_utf8_lossy(decoded),
        Cow::Owned(decoded) => match String::from_utf8_lossy(&decoded) {
            Cow::Borrowed(decoded_str) => {
                debug_assert_eq!(decoded_str.len(), decoded.len());
                debug_assert_eq!(
                    decoded_str.as_bytes().as_ptr() as *const u8,
                    decoded.as_ptr()
                );

                // SAFETY:
                // `String::from_utf8_lossy` returned a `Cow::Borrowed`, which means that
                // `decoded` is valid UTF-8.
                let decoded = unsafe { String::from_utf8_unchecked(decoded) };
                Cow::Owned(decoded)
            }
            Cow::Owned(decoded) => Cow::Owned(decoded),
        },
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    #[test]
    fn test_percent_encode() {
        #[cfg(all(feature = "alloc", not(feature = "std")))]
        use alloc::borrow::Cow;

        #[cfg(feature = "std")]
        use std::borrow::Cow;

        use super::percent_encode;

        assert!(matches!(percent_encode(""), Cow::Borrowed("")));
        assert!(matches!(percent_encode("foobar"), Cow::Borrowed("foobar")));

        assert_eq!(
            &*percent_encode("Ladies + Gentlemen"),
            "Ladies%20%2B%20Gentlemen"
        );
        assert_eq!(
            &*percent_encode("An encoded string!"),
            "An%20encoded%20string%21"
        );
        assert_eq!(
            &*percent_encode("Dogs, Cats & Mice"),
            "Dogs%2C%20Cats%20%26%20Mice"
        );
        assert_eq!(&*percent_encode("☃"), "%E2%98%83");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_percent_decode() {
        #[cfg(all(feature = "alloc", not(feature = "std")))]
        use alloc::borrow::Cow;

        #[cfg(feature = "std")]
        use std::borrow::Cow;

        use super::{percent_decode_utf8, FormDecode, StandardDecode};

        assert!(matches!(
            percent_decode_utf8("", StandardDecode),
            Cow::Borrowed("")
        ));
        assert!(matches!(
            percent_decode_utf8("foobar", StandardDecode),
            Cow::Borrowed("foobar")
        ));

        assert_eq!(
            &*percent_decode_utf8("Ladies%20%2B%20Gentlemen", StandardDecode),
            "Ladies + Gentlemen"
        );
        assert_eq!(
            &*percent_decode_utf8("An%20encoded%20string%21", StandardDecode),
            "An encoded string!"
        );
        assert_eq!(
            &*percent_decode_utf8("Dogs%2C%20Cats%20%26%20Mice", StandardDecode),
            "Dogs, Cats & Mice"
        );
        assert_eq!(
            &*percent_decode_utf8("%E2%98%83", StandardDecode),
            "☃"
        );

        assert_eq!(
            &*percent_decode_utf8("%e2%98%83", StandardDecode),
            "☃"
        );

        assert_eq!(
            &*percent_decode_utf8(
                "%41%6E%20%65%6E%63%6F%64%65%64%20%73%74%72%69%6E%67%21",
                StandardDecode
            ),
            "An encoded string!"
        );

        assert_eq!(&*percent_decode_utf8("hello!", StandardDecode), "hello!");
        assert_eq!(&*percent_decode_utf8("hello%", StandardDecode), "hello%");
        assert_eq!(&*percent_decode_utf8("%a", StandardDecode), "%a");
        assert_eq!(&*percent_decode_utf8("%za", StandardDecode), "%za");
        assert_eq!(&*percent_decode_utf8("%az", StandardDecode), "%az");

        assert_eq!(
            &*percent_decode_utf8("hello%FFworld", StandardDecode),
            "hello�world"
        );

        assert_eq!(
            &*percent_decode_utf8("hello+world", StandardDecode),
            "hello+world"
        );
        assert_eq!(
            &*percent_decode_utf8("hello+world", FormDecode),
            "hello world"
        );
        assert_eq!(
            &*percent_decode_utf8("hello++world", FormDecode),
            "hello  world"
        );
        assert_eq!(
            &*percent_decode_utf8("+hello+world+", FormDecode),
            " hello world "
        );
    }
}
