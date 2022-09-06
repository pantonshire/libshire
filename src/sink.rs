use core::fmt;

pub trait StrSink {
    type Error;

    fn sink_str(&mut self, s: &str) -> Result<(), Self::Error>;

    fn sink_char(&mut self, c: char) -> Result<(), Self::Error> {
        let mut buf = [0u8; 4];
        let s = c.encode_utf8(&mut buf);
        self.sink_str(s)
    }
}

impl<W> StrSink for W
where
    W: fmt::Write,
{
    type Error = fmt::Error;

    #[inline]
    fn sink_str(&mut self, s: &str) -> Result<(), Self::Error> {
        self.write_str(s)
    }

    #[inline]
    fn sink_char(&mut self, c: char) -> Result<(), Self::Error> {
        self.write_char(c)
    }
}

#[cfg(feature = "alloc")]
pub use string_sink::StringSink;

#[cfg(feature = "alloc")]
mod string_sink {
    use core::convert::Infallible;

    #[cfg(not(feature = "std"))]
    use alloc::string::String;

    use super::StrSink;

    #[repr(transparent)]
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub struct StringSink(pub String);

    impl StringSink {
        #[inline]
        #[must_use]
        pub fn from_string_ref(s: &String) -> &Self {
            // SAFETY:
            // Since `StringSink` uses `repr(transparent)`, it has the same memory layout as
            // `String`.
            unsafe { &*(s as *const String as *const Self) }
        }

        #[inline]
        #[must_use]
        pub fn from_string_mut(s: &mut String) -> &mut Self {
            // SAFETY:
            // Since `StringSink` uses `repr(transparent)`, it has the same memory layout as
            // `String`.
            unsafe { &mut *(s as *mut String as *mut Self) }
        }
    }

    impl AsRef<StringSink> for String {
        #[inline]
        fn as_ref(&self) -> &StringSink {
            StringSink::from_string_ref(self)
        }
    }

    impl AsMut<StringSink> for String {
        #[inline]
        fn as_mut(&mut self) -> &mut StringSink {
            StringSink::from_string_mut(self)
        }
    }

    impl StrSink for StringSink {
        type Error = Infallible;

        #[inline]
        fn sink_str(&mut self, s: &str) -> Result<(), Self::Error> {
            self.0.push_str(s);
            Ok(())
        }

        #[inline]
        fn sink_char(&mut self, c: char) -> Result<(), Self::Error> {
            self.0.push(c);
            Ok(())
        }
    }
}
