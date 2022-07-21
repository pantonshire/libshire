#[cfg(any(feature = "alloc", feature = "std"))]
pub mod experimental;
pub mod fixed;
pub mod capped;
#[cfg(any(feature = "alloc", feature = "std"))]
pub mod inlining;

pub use fixed::{FixedString, Error as FixedStringError};
pub use capped::{CappedString, Error as CappedStringError};
#[cfg(any(feature = "alloc", feature = "std"))]
pub use inlining::{InliningString, InliningString22};
