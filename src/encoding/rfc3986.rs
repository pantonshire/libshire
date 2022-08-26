// Following RFC3986 (https://www.rfc-editor.org/rfc/rfc3986#section-2.1)

use core::{
    fmt::{self, Write},
    str,
};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{borrow::Cow, string::String, vec::Vec};

#[cfg(feature = "std")]
use std::borrow::Cow;

use crate::{either::{Either, Inl, Inr}, strings::FixedString};

use super::hex;

/// Finds the first element of the slice which does not match the given predicate and returns the
/// sub-slice preceding that element, the element itself, and the sub-slice following the element.
#[inline]
fn split_at_non_matching<T, P>(xs: &[T], predicate: P) -> (&[T], Option<(T, &[T])>)
where
    T: Copy,
    P: Fn(T) -> bool,
{
    let mut i = 0;
    while i < xs.len() {
        let x = xs[i];
        if !predicate(x) {
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

fn byte_unreserved(byte: u8) -> bool {
    matches!(byte, b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z' | b'-' | b'.' | b'_' | b'~')
}

struct PercentEncoder<'a>(&'a [u8]);

impl<'a> PercentEncoder<'a> {
    pub fn partial_encode(&mut self) -> Option<(&'a str, Option<FixedString<3>>)> {
        if self.0.is_empty() {
            return None;
        }

        let (prefix, suffix) = split_at_non_matching(self.0, byte_unreserved);

        // SAFETY:
        // `prefix` only contains bytes which satisfy `byte_unreserved`, which are all valid ASCII
        // characters. Therefore, it is valid UTF-8.
        let prefix = unsafe { str::from_utf8_unchecked(prefix) };

        match suffix {
            Some((byte, suffix)) => {
                self.0 = suffix;
                Some((prefix, Some(Self::percent_encode_byte(byte))))
            },

            None => {
                self.0 = &self.0[self.0.len()..];
                Some((prefix, None))
            },
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

#[cfg(feature = "alloc")]
pub fn percent_encode<B>(bytes: &B) -> Cow<str>
where
    B: AsRef<[u8]> + ?Sized,
{
    let mut encoder = PercentEncoder(bytes.as_ref());

    match encoder.partial_encode().unwrap_or(("", None)) {
        (prefix, Some(encoded_byte)) => {
            let mut buf = String::new();
            buf.push_str(prefix);
            buf.push_str(&encoded_byte);

            while let Some((prefix, encoded_byte)) = encoder.partial_encode() {
                buf.push_str(prefix);
                if let Some(encoded_byte) = encoded_byte {
                    buf.push_str(&encoded_byte);
                }
            }

            Cow::Owned(buf)
        },

        (prefix, None) => Cow::Borrowed(prefix),
    }
}

pub fn percent_encode_to_fmt_writer<W, B>(writer: &mut W, bytes: &B) -> fmt::Result
where
    W: Write + ?Sized,
    B: AsRef<[u8]> + ?Sized,
{
    let mut encoder = PercentEncoder(bytes.as_ref());

    while let Some((prefix, encoded_byte)) = encoder.partial_encode() {
        if !prefix.is_empty() {
            writer.write_str(prefix)?;
        }
        if let Some(encoded_byte) = encoded_byte {
            writer.write_str(&encoded_byte)?;
        }
    }

    Ok(())
}

struct PercentDecoder<'a>(&'a [u8]);

impl<'a> PercentDecoder<'a> {
    fn partial_decode(&mut self) -> Result<Option<(&'a str, Option<u8>)>, PercentDecodeError> {
        if self.0.is_empty() {
            return Ok(None);
        }

        let (prefix, suffix) = split_at_non_matching(self.0, byte_unreserved);
        
        // SAFETY:
        // `prefix` only contains bytes which satisfy `byte_unreserved`, which are all valid ASCII
        // characters. Therefore, it is valid UTF-8.
        let prefix = unsafe { str::from_utf8_unchecked(prefix) };

        match suffix {
            Some((byte, suffix)) => {
                if byte != b'%' {
                    return Err(PercentDecodeError);
                }
                
                let [hex_msb, hex_lsb]: [u8; 2] = suffix
                    .get(..2)
                    .and_then(|hex_bytes| hex_bytes.try_into().ok())
                    .ok_or(PercentDecodeError)?;

                let hex_byte = hex::hex_to_byte(hex_msb, hex_lsb)
                    .map_err(|_| PercentDecodeError)?;

                self.0 = &suffix[2..];

                Ok(Some((prefix, Some(hex_byte))))
            },

            None => {
                self.0 = &self.0[self.0.len()..];
                Ok(Some((prefix, None)))
            },
        }
    }
}

#[cfg(feature = "alloc")]
fn percent_decode_internal<B>(bytes: &B) -> Result<Either<&str, Vec<u8>>, PercentDecodeError>
where
    B: AsRef<[u8]> + ?Sized,
{
    let mut decoder = PercentDecoder(bytes.as_ref());

    match decoder.partial_decode()?.unwrap_or(("", None)) {
        (prefix, Some(byte)) => {
            let mut buf = Vec::new();
            buf.extend(prefix.bytes());
            buf.push(byte);

            while let Some((prefix, byte)) = decoder.partial_decode()? {
                buf.extend(prefix.bytes());
                if let Some(byte) = byte {
                    buf.push(byte);
                }
            }

            Ok(Inr(buf))
        },

        (prefix, None) => Ok(Inl(prefix))
    }
}

#[cfg(feature = "alloc")]
pub fn percent_decode_to_utf8<B>(bytes: &B) -> Result<Cow<str>, PercentDecodeError>
where
    B: AsRef<[u8]> + ?Sized,
{
    percent_decode_internal(bytes).and_then(|decoded| match decoded {
        Inl(decoded_str) => Ok(Cow::Borrowed(decoded_str)),
        Inr(decoded_bytes) => String::from_utf8(decoded_bytes)
            .map(Cow::Owned)
            .map_err(|_| PercentDecodeError),
    })
}

#[cfg(feature = "alloc")]
pub fn percent_decode_to_bytes<B>(bytes: &B) -> Result<Cow<[u8]>, PercentDecodeError>
where
    B: AsRef<[u8]> + ?Sized,
{
    percent_decode_internal(bytes).map(|decoded| match decoded {
        Inl(decoded_str) => Cow::Borrowed(decoded_str.as_bytes()),
        Inr(decoded_bytes) => Cow::Owned(decoded_bytes),
    })
}

#[derive(Debug)]
pub struct PercentDecodeError;

impl fmt::Display for PercentDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid rfc 3986 percent-encoded string")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for PercentDecodeError {}

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

        assert_eq!(&*percent_encode("Ladies + Gentlemen"), "Ladies%20%2B%20Gentlemen");
        assert_eq!(&*percent_encode("An encoded string!"), "An%20encoded%20string%21");
        assert_eq!(&*percent_encode("Dogs, Cats & Mice"), "Dogs%2C%20Cats%20%26%20Mice");
        assert_eq!(&*percent_encode("☃"), "%E2%98%83");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_percent_decode() {
        #[cfg(all(feature = "alloc", not(feature = "std")))]
        use alloc::borrow::Cow;

        #[cfg(feature = "std")]
        use std::borrow::Cow;

        use super::{percent_decode_to_utf8, percent_decode_to_bytes};

        assert!(matches!(percent_decode_to_utf8(""), Ok(Cow::Borrowed(""))));
        assert!(matches!(percent_decode_to_bytes(""), Ok(Cow::Borrowed(b""))));
        assert!(matches!(percent_decode_to_utf8("foobar"), Ok(Cow::Borrowed("foobar"))));
        assert!(matches!(percent_decode_to_bytes("foobar"), Ok(Cow::Borrowed(b"foobar"))));

        assert!(matches!(percent_decode_to_utf8("Ladies%20%2B%20Gentlemen").as_deref(), Ok("Ladies + Gentlemen")));
        assert!(matches!(percent_decode_to_bytes("Ladies%20%2B%20Gentlemen").as_deref(), Ok(b"Ladies + Gentlemen")));
        assert!(matches!(percent_decode_to_utf8("An%20encoded%20string%21").as_deref(), Ok("An encoded string!")));
        assert!(matches!(percent_decode_to_bytes("An%20encoded%20string%21").as_deref(), Ok(b"An encoded string!")));
        assert!(matches!(percent_decode_to_utf8("Dogs%2C%20Cats%20%26%20Mice").as_deref(), Ok("Dogs, Cats & Mice")));
        assert!(matches!(percent_decode_to_bytes("Dogs%2C%20Cats%20%26%20Mice").as_deref(), Ok(b"Dogs, Cats & Mice")));
        assert!(matches!(percent_decode_to_utf8("%E2%98%83").as_deref(), Ok("☃")));

        assert!(matches!(percent_decode_to_utf8("%e2%98%83").as_deref(), Ok("☃")));

        assert!(matches!(percent_decode_to_utf8("%41%6E%20%65%6E%63%6F%64%65%64%20%73%74%72%69%6E%67%21").as_deref(), Ok("An encoded string!")));

        assert!(matches!(percent_decode_to_utf8("hello!"), Err(_)));
        assert!(matches!(percent_decode_to_bytes("hello!"), Err(_)));
        assert!(matches!(percent_decode_to_utf8("%2"), Err(_)));
        assert!(matches!(percent_decode_to_bytes("%2"), Err(_)));
        assert!(matches!(percent_decode_to_utf8("%2!"), Err(_)));
        assert!(matches!(percent_decode_to_bytes("%2!"), Err(_)));

        assert!(matches!(percent_decode_to_utf8("%FF"), Err(_)));
        assert!(matches!(percent_decode_to_bytes("%FF").as_deref(), Ok(&[0xff])));
    }
}
