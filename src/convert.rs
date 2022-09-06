use core::convert::Infallible;

/// Consumes an element of type `Infallible` and produces an element of any type `T`. This is
/// possible because `Infallible` has no elements and thus this function can never be called, so
/// the statement "for any given type `T`, whenever this function returns, it returns an element of
/// `T`" is vacuously true. In MLTT, this corresponds to a proof by contradiction.
/// 
/// ```
/// # use std::convert::Infallible;
/// # use libshire::convert::infallible_elim;
/// use std::io;
/// let x: Result<u32, Infallible> = Ok(123);
/// let y: Result<u32, io::Error> = x.map_err(infallible_elim);
/// ```
#[inline]
#[must_use]
pub const fn infallible_elim<T>(infallible: Infallible) -> T {
    match infallible {}
}

/// Converts an element of type `Infallible` to an element of the "never" type `!`. The never type
/// can be more useful than `Infallible` because it can be coerced to any other type and implements
/// many more traits than `Infallible` does.
#[inline]
pub const fn infallible_to_never(infallible: Infallible) -> ! {
    infallible_elim(infallible)
}

pub trait Empty: Sized {
    fn elim<T>(self) -> T;

    #[inline]
    fn never(self) -> ! {
        self.elim()
    }
}

impl Empty for Infallible {
    #[inline]
    fn elim<T>(self) -> T {
        infallible_elim(self)
    }
}

#[inline]
#[must_use]
pub fn result_elim<T, E>(res: Result<T, E>) -> T
where
    E: Empty,
{
    match res {
        Ok(x) => x,
        Err(e) => e.elim(),
    }
}

#[inline]
#[must_use]
pub fn clone<T: Clone>(x: &T) -> T {
    x.clone()
}

#[inline]
#[must_use]
pub fn clone_mut<T: Clone>(x: &mut T) -> T {
    (*x).clone()
}

#[inline]
#[must_use]
pub fn copy<T: Copy>(x: &T) -> T {
    *x
}

#[inline]
#[must_use]
pub fn copy_mut<T: Copy>(x: &mut T) -> T {
    *x
}
