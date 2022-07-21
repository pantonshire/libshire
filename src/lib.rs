#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod convert;
pub mod either;
pub mod hex;
pub mod strings;
pub mod uuid;
