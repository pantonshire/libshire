#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(feature = "alloc", not(feature = "std")))]
extern crate alloc;

pub mod convert;
pub mod either;
pub mod encoding;
pub mod strings;
pub mod uuid;
