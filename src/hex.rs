use std::{
    error,
    fmt::{self, Write},
    marker::PhantomData,
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct HexBytes<'a, E = Lowercase> {
    inner: &'a [u8],
    _marker: PhantomData<E>,
}

impl<'a, E> HexBytes<'a, E> {
    #[inline]
    #[must_use]
    pub const fn new(bytes: &'a [u8]) -> Self {
        Self {
            inner: bytes,
            _marker: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub const fn to_inner(self) -> &'a [u8] {
        self.inner
    }
}

impl<'a, E: Encode> fmt::Debug for HexBytes<'a, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().copied().map(HexByte::<E>::new))
            .finish()
    }
}

impl<'a, E: Encode> fmt::Display for HexBytes<'a, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for &byte in self.inner.iter() {
            fmt::Display::fmt(&HexByte::<E>::new(byte), f)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct HexByte<E> {
    inner: u8,
    _marker: PhantomData<E>,
}

impl<E> HexByte<E> {
    #[inline]
    #[must_use]
    pub const fn new(byte: u8) -> Self {
        Self {
            inner: byte,
            _marker: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub const fn to_inner(self) -> u8 {
        self.inner
    }
}

impl<E: Encode> fmt::Debug for HexByte<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (b0, b1) = <E as Encode>::byte_to_hex(self.inner);
        f.write_str("0x")
            .and_then(|_| f.write_char(char::from(b0)))
            .and_then(|_| f.write_char(char::from(b1)))
    }
}

impl<E: Encode> fmt::Display for HexByte<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (b0, b1) = <E as Encode>::byte_to_hex(self.inner);
        f.write_char(char::from(b0))
            .and_then(|_| f.write_char(char::from(b1)))
    }
}

pub trait Encode {
    fn byte_to_hex(byte: u8) -> (u8, u8);
}

pub struct Lowercase;

impl Encode for Lowercase {
    #[inline]
    fn byte_to_hex(byte: u8) -> (u8, u8) {
        byte_to_hex_lower(byte)
    }
}

pub struct Uppercase;

impl Encode for Uppercase {
    #[inline]
    fn byte_to_hex(byte: u8) -> (u8, u8) {
        byte_to_hex_upper(byte)
    }
}

/// Converts the given byte to its lowercase hexadecimal representation. The first byte returned
/// encodes the most significant 4 bits, and the second byte encodes the least significant 4 bits.
///
/// ```
/// # use libshire::hex::byte_to_hex_lower;
/// assert_eq!(byte_to_hex_lower(15), (b'0', b'f'));
/// assert_eq!(byte_to_hex_lower(139), (b'8', b'b'));
/// ```
#[inline]
#[must_use]
pub fn byte_to_hex_lower(byte: u8) -> (u8, u8) {
    (
        nybble_to_hex_lower(byte >> 4),
        nybble_to_hex_lower(byte & 0xF),
    )
}

/// Returns the ASCII byte corresponding to the given hex nybble, using lowercase for the digits A
/// to F. Assumes the given value is less than 16.
#[inline]
fn nybble_to_hex_lower(nybble: u8) -> u8 {
    match nybble {
        0..=9 => 0x30 + nybble,
        _ => 0x57 + nybble,
    }
}

/// Converts the given byte to its uppercase hexadecimal representation. The first byte returned
/// encodes the most significant 4 bits, and the second byte encodes the least significant 4 bits.
///
/// ```
/// # use libshire::hex::byte_to_hex_upper;
/// assert_eq!(byte_to_hex_upper(15), (b'0', b'F'));
/// assert_eq!(byte_to_hex_upper(139), (b'8', b'B'));
/// ```
#[inline]
#[must_use]
pub fn byte_to_hex_upper(byte: u8) -> (u8, u8) {
    (
        nybble_to_hex_upper(byte >> 4),
        nybble_to_hex_upper(byte & 0xF),
    )
}

/// Returns the ASCII byte corresponding to the given hex nybble, using uppercase for the digits A
/// to F. Assumes the given value is less than 16.
#[inline]
fn nybble_to_hex_upper(nybble: u8) -> u8 {
    match nybble {
        0..=9 => 0x30 + nybble,
        _ => 0x37 + nybble,
    }
}

pub fn hex_to_be_byte_array<const N: usize>(hex: &str) -> Result<[u8; N], ArrayParseError> {
    let mut iter = hex.chars().rev();
    let mut buf = [0u8; N];
    let mut bytes = 0usize;

    while let Some(ch0) = iter.next() {
        bytes += 1;
        if bytes > N {
            return Err(ArrayParseError::TooLong(N))
        }

        match iter.next() {
            Some(ch1) => {
                buf[N - bytes] = hex_to_byte(ch1, ch0)?;
            },
            None => {
                buf[N - bytes] = hex_to_nybble(ch0)?;
                return Ok(buf);
            },
        }
    }

    Ok(buf)
}

#[inline]
pub fn hex_to_byte(ch0: char, ch1: char) -> Result<u8, ParseError> {
    Ok((hex_to_nybble(ch0)? << 4) | hex_to_nybble(ch1)?)
}

#[inline]
fn hex_to_nybble(ch: char) -> Result<u8, ParseError> {
    match ch {
        '0'..='9' => Ok((ch as u8) - 0x30),
        'A'..='F' => Ok((ch as u8) - 0x37),
        'a'..='f' => Ok((ch as u8) - 0x57),
        ch => Err(ParseError::BadChar(ch)),
    }
}

#[derive(Debug)]
pub enum ParseError {
    BadChar(char),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadChar(ch) => write!(f, "bad hex chararcter '{}'", ch),
        }
    }
}

impl error::Error for ParseError {}

#[derive(Debug)]
pub enum ArrayParseError {
    BadHex(ParseError),
    TooLong(usize),
}

impl fmt::Display for ArrayParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadHex(err) => fmt::Display::fmt(err, f),
            Self::TooLong(max_len) => write!(f, "hex string exceeds maximum allowed length {}", max_len),
        }
    }
}

impl error::Error for ArrayParseError {}

impl From<ParseError> for ArrayParseError {
    fn from(err: ParseError) -> Self {
        Self::BadHex(err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hex_bytes_debug() {
        assert_eq!(
            format!("{:?}", HexBytes::<Lowercase>::new(&[0x87, 0xe1, 0x8f, 0xaa, 0x88, 0x8d, 0x43, 0x4e, 0xf2, 0xb2, 0x5d, 0xe1, 0xa5, 0x1b, 0xa0, 0x94])),
            "[0x87, 0xe1, 0x8f, 0xaa, 0x88, 0x8d, 0x43, 0x4e, 0xf2, 0xb2, 0x5d, 0xe1, 0xa5, 0x1b, 0xa0, 0x94]"
        );

        assert_eq!(
            format!("{:?}", HexBytes::<Uppercase>::new(&[0x87, 0xe1, 0x8f, 0xaa, 0x88, 0x8d, 0x43, 0x4e, 0xf2, 0xb2, 0x5d, 0xe1, 0xa5, 0x1b, 0xa0, 0x94])),
            "[0x87, 0xE1, 0x8F, 0xAA, 0x88, 0x8D, 0x43, 0x4E, 0xF2, 0xB2, 0x5D, 0xE1, 0xA5, 0x1B, 0xA0, 0x94]"
        );
    }

    #[test]
    fn test_hex_bytes_display() {
        assert_eq!(
            HexBytes::<Lowercase>::new(&[0x87, 0xe1, 0x8f, 0xaa, 0x88, 0x8d, 0x43, 0x4e, 0xf2, 0xb2, 0x5d, 0xe1, 0xa5, 0x1b, 0xa0, 0x94]).to_string(),
            "87e18faa888d434ef2b25de1a51ba094"
        );

        assert_eq!(
            HexBytes::<Uppercase>::new(&[0x87, 0xe1, 0x8f, 0xaa, 0x88, 0x8d, 0x43, 0x4e, 0xf2, 0xb2, 0x5d, 0xe1, 0xa5, 0x1b, 0xa0, 0x94]).to_string(),
            "87E18FAA888D434EF2B25DE1A51BA094"
        );
    }

    #[test]
    fn test_nybble_to_hex_lower() {
        assert_eq!(nybble_to_hex_lower(0), b'0');
        assert_eq!(nybble_to_hex_lower(1), b'1');
        assert_eq!(nybble_to_hex_lower(2), b'2');
        assert_eq!(nybble_to_hex_lower(3), b'3');
        assert_eq!(nybble_to_hex_lower(4), b'4');
        assert_eq!(nybble_to_hex_lower(5), b'5');
        assert_eq!(nybble_to_hex_lower(6), b'6');
        assert_eq!(nybble_to_hex_lower(7), b'7');
        assert_eq!(nybble_to_hex_lower(8), b'8');
        assert_eq!(nybble_to_hex_lower(9), b'9');
        assert_eq!(nybble_to_hex_lower(10), b'a');
        assert_eq!(nybble_to_hex_lower(11), b'b');
        assert_eq!(nybble_to_hex_lower(12), b'c');
        assert_eq!(nybble_to_hex_lower(13), b'd');
        assert_eq!(nybble_to_hex_lower(14), b'e');
        assert_eq!(nybble_to_hex_lower(15), b'f');
    }

    #[test]
    fn test_nybble_to_hex_upper() {
        assert_eq!(nybble_to_hex_upper(0), b'0');
        assert_eq!(nybble_to_hex_upper(1), b'1');
        assert_eq!(nybble_to_hex_upper(2), b'2');
        assert_eq!(nybble_to_hex_upper(3), b'3');
        assert_eq!(nybble_to_hex_upper(4), b'4');
        assert_eq!(nybble_to_hex_upper(5), b'5');
        assert_eq!(nybble_to_hex_upper(6), b'6');
        assert_eq!(nybble_to_hex_upper(7), b'7');
        assert_eq!(nybble_to_hex_upper(8), b'8');
        assert_eq!(nybble_to_hex_upper(9), b'9');
        assert_eq!(nybble_to_hex_upper(10), b'A');
        assert_eq!(nybble_to_hex_upper(11), b'B');
        assert_eq!(nybble_to_hex_upper(12), b'C');
        assert_eq!(nybble_to_hex_upper(13), b'D');
        assert_eq!(nybble_to_hex_upper(14), b'E');
        assert_eq!(nybble_to_hex_upper(15), b'F');
    }

    #[test]
    fn test_byte_to_hex_lower() {
        assert_eq!(byte_to_hex_lower(0x00), (b'0', b'0'));
        assert_eq!(byte_to_hex_lower(0x01), (b'0', b'1'));
        assert_eq!(byte_to_hex_lower(0x0F), (b'0', b'f'));
        assert_eq!(byte_to_hex_lower(0x10), (b'1', b'0'));
        assert_eq!(byte_to_hex_lower(0x1F), (b'1', b'f'));
        assert_eq!(byte_to_hex_lower(0x9A), (b'9', b'a'));
        assert_eq!(byte_to_hex_lower(0xA9), (b'a', b'9'));
        assert_eq!(byte_to_hex_lower(0xF0), (b'f', b'0'));
        assert_eq!(byte_to_hex_lower(0xFF), (b'f', b'f'));
    }

    #[test]
    fn test_byte_to_hex_upper() {
        assert_eq!(byte_to_hex_upper(0x00), (b'0', b'0'));
        assert_eq!(byte_to_hex_upper(0x01), (b'0', b'1'));
        assert_eq!(byte_to_hex_upper(0x0F), (b'0', b'F'));
        assert_eq!(byte_to_hex_upper(0x10), (b'1', b'0'));
        assert_eq!(byte_to_hex_upper(0x1F), (b'1', b'F'));
        assert_eq!(byte_to_hex_upper(0x9A), (b'9', b'A'));
        assert_eq!(byte_to_hex_upper(0xA9), (b'A', b'9'));
        assert_eq!(byte_to_hex_upper(0xF0), (b'F', b'0'));
        assert_eq!(byte_to_hex_upper(0xFF), (b'F', b'F'));
    }

    #[test]
    fn test_hex_to_nybble() {
        assert_eq!(hex_to_nybble('0').unwrap(), 0x0);
        assert_eq!(hex_to_nybble('1').unwrap(), 0x1);
        assert_eq!(hex_to_nybble('2').unwrap(), 0x2);
        assert_eq!(hex_to_nybble('3').unwrap(), 0x3);
        assert_eq!(hex_to_nybble('4').unwrap(), 0x4);
        assert_eq!(hex_to_nybble('5').unwrap(), 0x5);
        assert_eq!(hex_to_nybble('6').unwrap(), 0x6);
        assert_eq!(hex_to_nybble('7').unwrap(), 0x7);
        assert_eq!(hex_to_nybble('8').unwrap(), 0x8);
        assert_eq!(hex_to_nybble('9').unwrap(), 0x9);
        assert_eq!(hex_to_nybble('a').unwrap(), 0xa);
        assert_eq!(hex_to_nybble('b').unwrap(), 0xb);
        assert_eq!(hex_to_nybble('c').unwrap(), 0xc);
        assert_eq!(hex_to_nybble('d').unwrap(), 0xd);
        assert_eq!(hex_to_nybble('e').unwrap(), 0xe);
        assert_eq!(hex_to_nybble('f').unwrap(), 0xf);
        assert_eq!(hex_to_nybble('A').unwrap(), 0xa);
        assert_eq!(hex_to_nybble('B').unwrap(), 0xb);
        assert_eq!(hex_to_nybble('C').unwrap(), 0xc);
        assert_eq!(hex_to_nybble('D').unwrap(), 0xd);
        assert_eq!(hex_to_nybble('E').unwrap(), 0xe);
        assert_eq!(hex_to_nybble('F').unwrap(), 0xf);

        assert!(matches!(hex_to_nybble('g'), Err(ParseError::BadChar('g'))));
        assert!(matches!(hex_to_nybble('G'), Err(ParseError::BadChar('G'))));
    }

    #[test]
    fn test_hex_to_be_byte_array() {
        assert_eq!(hex_to_be_byte_array("").unwrap(), []);
        assert_eq!(hex_to_be_byte_array("").unwrap(), [0x00]);
        assert_eq!(hex_to_be_byte_array("").unwrap(), [0x00, 0x00]);

        assert_eq!(
            hex_to_be_byte_array("d90058decebf").unwrap(),
            [0xd9, 0x00, 0x58, 0xde, 0xce, 0xbf]
        );

        assert_eq!(
            hex_to_be_byte_array("D90058DECEBF").unwrap(),
            [0xd9, 0x00, 0x58, 0xde, 0xce, 0xbf]
        );

        assert_eq!(
            hex_to_be_byte_array("90058DECEBF").unwrap(),
            [0x09, 0x00, 0x58, 0xde, 0xce, 0xbf]
        );

        assert!(matches!(
            hex_to_be_byte_array::<5>("d90058decebf"),
            Err(ArrayParseError::TooLong(5))
        ));
    }
}
