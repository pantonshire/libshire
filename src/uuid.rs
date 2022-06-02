use std::{error, fmt, str};

use crate::{hex, strings::FixedString};

// TODO: make conformity to RFC 4122 an invariant of this type (which means it cannot be created
// safely from an arbitrary [u8; 16]).

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Uuid([u8; 16]);

// UUID ANATOMY
//
// Offset | Field
// -------+---------------------------
//      0 | time_low
//      1 |
//      2 |
//      3 |
// -------+---------------------------
//      4 | time_mid
//      5 |
// -------+---------------------------
//      6 | time_hi_and_version
//      7 |
// -------+---------------------------
//      8 | clock_seq_hi_and_reserved
// -------+---------------------------
//      9 | clock_seq_low
// -------+---------------------------
//     10 | node
//     11 |
//     12 |
//     13 |
//     14 |
//     15 |

impl Uuid {
    #[inline]
    #[must_use]
    pub const fn nil() -> Self {
        Self([0; 16])
    }

    #[inline]
    #[must_use]
    pub const fn from_bytes(bytes: [u8; 16]) -> Self {
        Self(bytes)
    }

    pub fn new_v5<T>(namespace: Uuid, name: &T) -> Result<Self, UuidV5Error>
    where
        T: AsRef<[u8]> + ?Sized,
    {
        const UUID_VERSION: u8 = 5;

        let hash = sha1(namespace.to_bytes(), <T as AsRef<[u8]>>::as_ref(name))?;

        let mut buf = [0u8; 16];
        buf.copy_from_slice(&hash[..16]);
        buf[6] = (buf[6] & 0xF) | (UUID_VERSION << 4);
        buf[8] = (buf[8] & 0x3F) | 0x80;

        Ok(Self::from_bytes(buf))
    }

    #[inline]
    #[must_use]
    pub fn to_bytes(self) -> [u8; 16] {
        self.0
    }

    #[must_use]
    pub fn as_string(&self) -> FixedString<36> {
        let mut buf = [0u8; 36];

        for (i, byte) in self.0.iter().copied().enumerate() {
            let (b0, b1) = hex::byte_to_hex_lower(byte);
            let offset = match i {
                0..=3 => 0,
                4..=5 => 1,
                6..=7 => 2,
                8..=9 => 3,
                _ => 4,
            };
            buf[i * 2 + offset] = b0;
            buf[i * 2 + 1 + offset] = b1;
        }

        buf[8] = b'-';
        buf[13] = b'-';
        buf[18] = b'-';
        buf[23] = b'-';

        debug_assert!(str::from_utf8(&buf).is_ok());

        // SAFETY:
        // `byte_to_hex_lower` always returns a pair of ASCII characters, and `b'-'` is a valid
        // ASCII character, so `buf` contains a valid ASCII string. All valid ASCII strings are
        // also valid UTF-8, so `buf` is valid UTF-8.
        unsafe { FixedString::from_raw_array(buf) }
    }
}

impl Default for Uuid {
    #[inline]
    fn default() -> Self {
        Self::nil()
    }
}

impl str::FromStr for Uuid {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let groups = {
            let mut groups_iter = s.split('-');
            let mut groups_buf = [""; 5];
            let mut num_groups = 0;
            for (i, group) in groups_iter.by_ref().take(5).enumerate() {
                groups_buf[i] = group;
                num_groups += 1;
            }
            if num_groups < 5 {
                return Err(ParseError::NotEnoughGroups(num_groups));
            }
            if groups_iter.next().is_some() {
                return Err(ParseError::TooManyGroups);
            }
            groups_buf
        };

        let mut buf = [0u8; 16];

        buf[..4].copy_from_slice(
            &hex::hex_to_be_byte_array::<4>(groups[0]).map_err(ParseError::BadTimeLow)?,
        );
        buf[4..6].copy_from_slice(
            &hex::hex_to_be_byte_array::<2>(groups[1]).map_err(ParseError::BadTimeMid)?,
        );
        buf[6..8].copy_from_slice(
            &hex::hex_to_be_byte_array::<2>(groups[2]).map_err(ParseError::BadTimeHi)?,
        );
        buf[8..10].copy_from_slice(
            &hex::hex_to_be_byte_array::<2>(groups[3]).map_err(ParseError::BadClockSeq)?,
        );
        buf[10..].copy_from_slice(
            &hex::hex_to_be_byte_array::<6>(groups[4]).map_err(ParseError::BadNode)?,
        );

        Ok(Self::from_bytes(buf))
    }
}

impl fmt::Display for Uuid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.as_string())
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Uuid {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer
    {
        serializer.serialize_str(&self.as_string())
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Uuid {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>
    {
        let s: &str = serde::Deserialize::deserialize(deserializer)?;
        s.parse()
            .map_err(serde::de::Error::custom)
    }
}

#[derive(Debug)]
pub enum ParseError {
    NotEnoughGroups(usize),
    TooManyGroups,
    BadTimeLow(hex::ArrayParseError),
    BadTimeMid(hex::ArrayParseError),
    BadTimeHi(hex::ArrayParseError),
    BadClockSeq(hex::ArrayParseError),
    BadNode(hex::ArrayParseError),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotEnoughGroups(groups) => {
                write!(f, "expected 5 groups of digits, found {}", groups)
            }
            Self::TooManyGroups => {
                write!(
                    f,
                    "found an unexpected extra group after the first 5 groups"
                )
            }
            Self::BadTimeLow(err) => {
                write!(f, "error decoding `time_low` (first) group: {}", err)
            }
            Self::BadTimeMid(err) => {
                write!(f, "error decoding `time_mid` (second) group: {}", err)
            }
            Self::BadTimeHi(err) => {
                write!(f, "error decoding `time_hi` (third) group: {}", err)
            }
            Self::BadClockSeq(err) => {
                write!(f, "error decoding `clock_seq` (fourth) group: {}", err)
            }
            Self::BadNode(err) => {
                write!(f, "error decoding `node` (fifth) group: {}", err)
            }
        }
    }
}

impl error::Error for ParseError {}

#[derive(Debug)]
pub enum UuidV5Error {
    NameTooLong(usize),
}

impl fmt::Display for UuidV5Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NameTooLong(size) => write!(f, "uuid v5 name too long ({} bytes)", size),
        }
    }
}

impl error::Error for UuidV5Error {}

fn sha1(namespace: [u8; 16], name: &[u8]) -> Result<[u8; 20], UuidV5Error> {
    let (mut h0, mut h1, mut h2, mut h3, mut h4) = (
        0x67452301u32,
        0xefcdab89u32,
        0x98badcfeu32,
        0x10325476u32,
        0xc3d2e1f0u32,
    );

    // Break the namespace and name (and some additional trailing bytes) into 64-byte chunks and
    // update the state for each chunk.
    for chunk in Sha1ChunkIter::new(namespace, name)? {
        let mut words = [0u32; 80];

        // Break the 64-byte chunk into 16 4-byte words, and store them as the first 16 values in
        // the `words` buffer.
        for (i, word) in words.iter_mut().take(16).enumerate() {
            *word = u32::from_be_bytes(chunk[(i * 4)..(i * 4 + 4)].try_into().unwrap());
        }

        // Calculate the remaining 64 4-byte words.
        for i in 16..80 {
            words[i] = (words[i - 3] ^ words[i - 8] ^ words[i - 14] ^ words[i - 16]).rotate_left(1);
        }

        let (mut a, mut b, mut c, mut d, mut e) = (h0, h1, h2, h3, h4);

        // 80-round main loop for the current chunk.
        for (i, word) in words.iter().copied().enumerate() {
            let (f, k) = match i {
                0..=19 => ((b & c) | (!b & d), 0x5a827999),
                20..=39 => (b ^ c ^ d, 0x6ed9eba1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8f1bbcdc),
                _ => (b ^ c ^ d, 0xca62c1d6),
            };

            let temp = (a.rotate_left(5))
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(word);

            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = temp;
        }

        h0 = h0.wrapping_add(a);
        h1 = h1.wrapping_add(b);
        h2 = h2.wrapping_add(c);
        h3 = h3.wrapping_add(d);
        h4 = h4.wrapping_add(e);
    }

    // Copy the 5 4-byte hash values into a single 20-byte array, to be returned as the final hash
    // value.
    let mut hash = [0u8; 20];
    hash[..4].copy_from_slice(&h0.to_be_bytes());
    hash[4..8].copy_from_slice(&h1.to_be_bytes());
    hash[8..12].copy_from_slice(&h2.to_be_bytes());
    hash[12..16].copy_from_slice(&h3.to_be_bytes());
    hash[16..].copy_from_slice(&h4.to_be_bytes());

    Ok(hash)
}

struct Sha1ChunkIter<'a> {
    namespace: [u8; 16],
    name: &'a [u8],
    message_len_bits: u64,
    namespace_added: bool,
    one_bit_added: bool,
    message_len_added: bool,
}

impl<'a> Sha1ChunkIter<'a> {
    fn new(namespace: [u8; 16], name: &'a [u8]) -> Result<Self, UuidV5Error> {
        let message_len_bits = u64::try_from(name.len())
            .ok()
            .and_then(|len| len.checked_add(16))
            .and_then(|len| len.checked_mul(8))
            .ok_or(UuidV5Error::NameTooLong(name.len()))?;

        Ok(Self {
            namespace,
            name,
            message_len_bits,
            namespace_added: false,
            one_bit_added: false,
            message_len_added: false,
        })
    }
}

impl<'a> Iterator for Sha1ChunkIter<'a> {
    type Item = [u8; 64];

    fn next(&mut self) -> Option<Self::Item> {
        if self.message_len_added {
            None
        } else {
            let mut chunk = [0u8; 64];
            let mut chunk_offset = 0;

            // If the 16-byte namespace has not already appeared in a chunk, then we need to add it
            // to the current chunk.
            if !self.namespace_added {
                // Copy the namespace into the start of the current chunk.
                chunk[..16].copy_from_slice(&self.namespace);

                // Since the 16-byte namespace is currently the only thing in the chunk, we can
                // just set the chunk offset to 16 rather than incrementing it by 16.
                chunk_offset = 16;

                self.namespace_added = true;
            }

            // Check whether there are any bytes of the name remaining that have not appeared in
            // any chunk.
            if !self.name.is_empty() {
                // Calculate how many bytes of the name to add to this chunk by taking the minimum
                // of the length of the remaining part of the name and the free space in the
                // current chunk. This will always be non-zero because a maximum of 16 bytes of the
                // chunk have been used at this point (to store the namespace), so there will
                // always be at least 48 bytes available to store a portion of the name.
                let name_slice_len = self.name.len().min(64 - chunk_offset);

                // Copy the selected portion of the name into the chunk.
                chunk[chunk_offset..(chunk_offset + name_slice_len)]
                    .copy_from_slice(&self.name[..name_slice_len]);

                // Advance the chunk offset by the number of bytes we just wrote to it.
                chunk_offset += name_slice_len;

                // Shrink the size of the name slice so the portion of the name we just added is no
                // longer included.
                self.name = &self.name[name_slice_len..];
            }

            // Once we've written the entire name to the chunk, we now need to add the "1" bit
            // after the name, the zero-padding and the length of the hashed message in bits. Note
            // that this is a separate `if` statement rather than an `else` statement because `if`
            // statement above may have changed the value of `self.name`.
            if self.name.is_empty() {
                // If there's space in the chunk, add the byte 0x80 to the chunk in order to add a
                // "1" bit at the end of the message, as required by SHA-1.
                if !self.one_bit_added && chunk_offset < 64 {
                    chunk[chunk_offset] = 0x80;
                    chunk_offset += 1;
                    self.one_bit_added = true;
                }

                // If we've already added the "1" bit and there's space in the chunk, add the
                // message length to the end of the chunk.
                if self.one_bit_added && chunk_offset < 57 {
                    chunk[56..].copy_from_slice(&self.message_len_bits.to_be_bytes());
                    self.message_len_added = true;
                }
            }

            Some(chunk)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Uuid;

    #[test]
    fn test_uuid_display() {
        assert_eq!(
            Uuid::from_bytes([
                0x12, 0x3e, 0x45, 0x67, 0xe8, 0x9b, 0x12, 0xd3, 0xa4, 0x56, 0x42, 0x66, 0x14, 0x17,
                0x40, 0x00
            ])
            .to_string(),
            "123e4567-e89b-12d3-a456-426614174000"
        );
    }

    #[test]
    fn test_uuid_parse() {
        assert_eq!(
            "123e4567-e89b-12d3-a456-426614174000"
                .parse::<Uuid>()
                .unwrap(),
            Uuid::from_bytes([
                0x12, 0x3e, 0x45, 0x67, 0xe8, 0x9b, 0x12, 0xd3, 0xa4, 0x56, 0x42, 0x66, 0x14, 0x17,
                0x40, 0x00
            ])
        );
    }

    #[test]
    fn test_uuidv5() {
        let namespace = "123e4567-e89b-12d3-a456-426614174000".parse().unwrap();

        assert_eq!(
            Uuid::new_v5(namespace, "hello").unwrap(),
            "971690ef-3543-5938-95a4-29c6b029d731".parse().unwrap()
        );
    }

    #[test]
    fn test_sha1() {
        use super::sha1;

        assert_eq!(
            sha1(*b"abcdefghijklmnop", b"").unwrap(),
            [
                0x14, 0xf3, 0x99, 0x52, 0x88, 0xac, 0xd1, 0x89, 0xe6, 0xe5, 0x0a, 0x7a, 0xf4, 0x7e,
                0xe7, 0x09, 0x9a, 0xa6, 0x82, 0xb9
            ]
        );

        assert_eq!(
            sha1(*b"abcdefghijklmnop", b"hello").unwrap(),
            [
                0x35, 0x52, 0x6e, 0x86, 0xd8, 0x66, 0x5b, 0x7e, 0x91, 0x68, 0xf9, 0x94, 0x4d, 0xff,
                0x3b, 0x5e, 0xd4, 0xb9, 0x30, 0x1c
            ]
        );

        assert_eq!(
            sha1(
                *b"abcdefghijklmnop",
                b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLM"
            )
            .unwrap(),
            [
                0x4e, 0xbd, 0x2c, 0x7f, 0xff, 0xa5, 0x75, 0xe0, 0xe0, 0xc4, 0xed, 0x50, 0x7b, 0x8b,
                0x3c, 0x93, 0xdc, 0x2d, 0xad, 0x0d
            ]
        );

        assert_eq!(
            sha1(
                *b"abcdefghijklmnop",
                b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMN"
            )
            .unwrap(),
            [
                0xb3, 0x5b, 0x3d, 0x3d, 0xaa, 0xa5, 0x92, 0xfd, 0x15, 0x49, 0xd3, 0xa9, 0x81, 0xad,
                0x85, 0x58, 0x03, 0xce, 0x01, 0x21
            ]
        );

        assert_eq!(
            sha1(
                *b"abcdefghijklmnop",
                b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTU"
            )
            .unwrap(),
            [
                0xae, 0x12, 0xd0, 0xa7, 0x54, 0x8b, 0xa5, 0x99, 0x41, 0x15, 0xfa, 0x04, 0x8f, 0xe1,
                0xcd, 0x7d, 0x91, 0xd8, 0x61, 0xc7,
            ]
        );

        assert_eq!(
            sha1(
                *b"abcdefghijklmnop",
                b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUV"
            )
            .unwrap(),
            [
                0x72, 0xd2, 0x58, 0xb5, 0x62, 0x4a, 0x55, 0x72, 0xd7, 0x55, 0x2d, 0xd9, 0xe2, 0x11,
                0x4d, 0x4a, 0xc3, 0x8b, 0xd7, 0x61
            ]
        );

        assert_eq!(
            sha1(
                *b"abcdefghijklmnop",
                b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUW"
            )
            .unwrap(),
            [
                0xa1, 0x75, 0x25, 0xb5, 0xd3, 0x15, 0x31, 0x63, 0x18, 0xf4, 0x83, 0x5c, 0x05, 0xbb,
                0xf2, 0x5d, 0x8f, 0x89, 0x55, 0x13
            ]
        );
    }
}
