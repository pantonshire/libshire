use core::fmt::{self, Arguments};

pub trait StrSink {
    type Error;

    fn sink_str(&mut self, s: &str) -> Result<(), Self::Error>;

    fn sink_char(&mut self, c: char) -> Result<(), Self::Error> {
        let mut buf = [0u8; 4];
        let s = c.encode_utf8(&mut buf);
        self.sink_str(s)
    }
}

pub trait FmtSink: StrSink {
    fn sink_fmt<'a>(&mut self, args: Arguments<'a>) -> Result<(), <Self as StrSink>::Error>;
}

#[macro_export]
macro_rules! sink_fmt {
    ($dst:expr, $($arg:tt)*) => {
        FmtSink::sink_fmt($dst, core::format_args!($($arg)*))
    };
}

pub use sink_fmt;

#[repr(transparent)]
pub struct FmtWriteSink<W: fmt::Write>(pub W);

impl<W: fmt::Write> FmtWriteSink<W> {
    #[inline]
    #[must_use]
    pub fn from_ref(w: &W) -> &Self {
        // SAFETY:
        // `FmtWriteSink` uses `repr(transparent)`, so it has the same memory layout as `W`.
        unsafe { &*(w as *const W as *const Self) }
    }
    
    #[inline]
    #[must_use]
    pub fn from_mut(w: &mut W) -> &mut Self {
        // SAFETY:
        // `FmtWriteSink` uses `repr(transparent)`, so it has the same memory layout as `W`.
        unsafe { &mut *(w as *mut W as *mut Self) }
    }
}

impl<W: fmt::Write> StrSink for FmtWriteSink<W> {
    type Error = fmt::Error;

    #[inline]
    fn sink_str(&mut self, s: &str) -> Result<(), Self::Error> {
        self.0.write_str(s)
    }

    #[inline]
    fn sink_char(&mut self, c: char) -> Result<(), Self::Error> {
        self.0.write_char(c)
    }
}

impl<W: fmt::Write> FmtSink for FmtWriteSink<W> {
    #[inline]
    fn sink_fmt<'a>(&mut self, args: Arguments<'a>) -> Result<(), <Self as StrSink>::Error> {
        self.0.write_fmt(args)
    }
}

#[cfg(feature = "alloc")]
pub use string_sink::SinkString;

#[cfg(feature = "alloc")]
mod string_sink {
    use core::{convert::Infallible, fmt::{self, Arguments}};

    #[cfg(not(feature = "std"))]
    use alloc::string::String;

    use super::{StrSink, FmtSink};

    #[repr(transparent)]
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub struct SinkString(pub String);

    impl SinkString {
        #[inline]
        #[must_use]
        pub fn empty() -> Self {
            Self(String::new())
        }

        #[inline]
        #[must_use]
        pub fn with_capacity(capacity: usize) -> Self {
            Self(String::with_capacity(capacity))
        }

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

    impl AsRef<SinkString> for String {
        #[inline]
        fn as_ref(&self) -> &SinkString {
            SinkString::from_string_ref(self)
        }
    }

    impl AsMut<SinkString> for String {
        #[inline]
        fn as_mut(&mut self) -> &mut SinkString {
            SinkString::from_string_mut(self)
        }
    }

    impl StrSink for SinkString {
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

    impl FmtSink for SinkString {
        fn sink_fmt<'a>(&mut self, args: Arguments<'a>) -> Result<(), <Self as StrSink>::Error> {
            // We discard any error, since writing to a `String` should be infallible for correct
            // implementations of `Display` etc.
            let _ = <String as fmt::Write>::write_fmt(&mut self.0, args);
            Ok(())
        }
    }
}

#[cfg(feature = "std")]
pub use io_sink::IoWriteSink;

#[cfg(feature = "std")]
mod io_sink {
    use core::fmt::Arguments;
    use std::io;

    use super::{StrSink, FmtSink};
    
    #[repr(transparent)]
    pub struct IoWriteSink<W: io::Write>(pub W);

    impl<W: io::Write> IoWriteSink<W> {
        #[inline]
        #[must_use]
        pub fn from_ref(w: &W) -> &Self {
            // SAFETY:
            // `IoWriteSink` uses `repr(transparent)`, so it has the same memory layout as `W`.
            unsafe { &*(w as *const W as *const Self) }
        }
        
        #[inline]
        #[must_use]
        pub fn from_mut(w: &mut W) -> &mut Self {
            // SAFETY:
            // `IoWriteSink` uses `repr(transparent)`, so it has the same memory layout as `W`.
            unsafe { &mut *(w as *mut W as *mut Self) }
        }
    }

    impl<W: io::Write> StrSink for IoWriteSink<W> {
        type Error = io::Error;

        #[inline]
        fn sink_str(&mut self, s: &str) -> Result<(), Self::Error> {
            self.0.write_all(s.as_bytes())
        }
    }

    impl<W: io::Write> FmtSink for IoWriteSink<W> {
        #[inline]
        fn sink_fmt<'a>(&mut self, args: Arguments<'a>) -> Result<(), <Self as StrSink>::Error> {
            self.0.write_fmt(args)
        }
    }
}
