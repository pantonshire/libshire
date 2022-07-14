use std::{
    convert::identity,
    fmt,
    hint,
    ops::{Deref, DerefMut},
    process::{ExitCode, Termination},
};

use crate::convert::{clone, clone_mut, copy, copy_mut, Empty};

pub use Either::{Inl, Inr};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Either<L, R> {
    Inl(L),
    Inr(R),
}

impl<L, R> Either<L, R> {
    /// Returns a new `Either` that is `Inl` if the given result is `Ok`, and `Inr` if the given
    /// result is `Err`.
    /// 
    /// ```
    /// # use libshire::either::{Either, Inl, Inr};
    /// let res = u8::try_from(123u32);
    /// assert_eq!(Either::from_result(res), Inl(123));
    /// ```
    #[inline]
    #[must_use]
    pub fn from_result(result: Result<L, R>) -> Self {
        match result {
            Ok(l) => Inl(l),
            Err(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub const fn as_ref(&self) -> Either<&L, &R> {
        match self {
            Inl(l) => Inl(l),
            Inr(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn as_mut(&mut self) -> Either<&mut L, &mut R> {
        match self {
            Inl(l) => Inl(l),
            Inr(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> Either<&<L as Deref>::Target, &<R as Deref>::Target>
    where
        L: Deref,
        R: Deref,
    {
        match self {
            Inl(l) => Inl(l),
            Inr(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn as_deref_l(&self) -> Either<&<L as Deref>::Target, &R>
    where
        L: Deref,
    {
        match self {
            Inl(l) => Inl(l),
            Inr(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn as_deref_r(&self) -> Either<&L, &<R as Deref>::Target>
    where
        R: Deref,
    {
        match self {
            Inl(l) => Inl(l),
            Inr(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> Either<&mut <L as Deref>::Target, &mut <R as Deref>::Target>
    where
        L: DerefMut,
        R: DerefMut,
    {
        match self {
            Inl(l) => Inl(l),
            Inr(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn as_deref_mut_l(&mut self) -> Either<&mut <L as Deref>::Target, &mut R>
    where
        L: DerefMut,
    {
        match self {
            Inl(l) => Inl(l),
            Inr(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn as_deref_mut_r(&mut self) -> Either<&mut L, &mut <R as Deref>::Target>
    where
        R: DerefMut,
    {
        match self {
            Inl(l) => Inl(l),
            Inr(r) => Inr(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn fold<T, F, G>(self, f: F, g: G) -> T
    where
        F: FnOnce(L) -> T,
        G: FnOnce(R) -> T,
    {
        match self {
            Inl(l) => f(l),
            Inr(r) => g(r),
        }
    }

    #[inline]
    #[must_use]
    pub fn fold_l<F: FnOnce(L) -> R>(self, f: F) -> R {
        self.fold(f, identity)
    }

    #[inline]
    #[must_use]
    pub fn fold_r<F: FnOnce(R) -> L>(self, f: F) -> L {
        self.fold(identity, f)
    }

    #[inline]
    #[must_use]
    pub fn select<T>(&self, if_l: T, if_r: T) -> T {
        match self {
            Inl(_) => if_l,
            Inr(_) => if_r,
        }
    }

    #[inline]
    #[must_use]
    pub fn map<T, U, F, G>(self, f: F, g: G) -> Either<T, U>
    where
        F: FnOnce(L) -> T,
        G: FnOnce(R) -> U,
    {
        self.fold(|l| Inl(f(l)), |r| Inr(g(r)))
    }

    #[inline]
    #[must_use]
    pub fn map_l<T, F: FnOnce(L) -> T>(self, f: F) -> Either<T, R> {
        self.fold(|l| Inl(f(l)), Inr)
    }

    #[inline]
    #[must_use]
    pub fn map_r<T, F: FnOnce(R) -> T>(self, f: F) -> Either<L, T> {
        self.fold(Inl, |r| Inr(f(r)))
    }

    #[inline]
    #[must_use]
    pub fn is_l(&self) -> bool {
        self.select(true, false)
    }

    #[inline]
    #[must_use]
    pub fn is_r(&self) -> bool {
        self.select(false, true)
    }

    #[inline]
    #[must_use]
    pub fn flip(self) -> Either<R, L> {
        self.fold(Inr, Inl)
    }

    #[inline]
    #[must_use]
    pub fn elim_l(self) -> R
    where
        L: Empty,
    {
        self.fold_l(<L as Empty>::elim)
    }

    #[inline]
    #[must_use]
    pub fn elim_r(self) -> L
    where
        R: Empty,
    {
        self.fold_r(<R as Empty>::elim)
    }

    #[inline]
    #[must_use]
    pub fn some_l(self) -> Option<L> {
        self.fold(Some, |_| None)
    }

    #[inline]
    #[must_use]
    pub fn some_r(self) -> Option<R> {
        self.fold(|_| None, Some)
    }

    #[inline]
    #[must_use]
    pub fn into_options(self) -> (Option<L>, Option<R>) {
        self.fold(|l| (Some(l), None), |r| (None, Some(r)))
    }

    #[inline]
    pub fn ok_l_or<E>(self, err: E) -> Result<L, E> {
        self.fold(Ok, |_| Err(err))
    }

    #[inline]
    pub fn ok_l_or_else<E, F: FnOnce(R) -> E>(self, err: F) -> Result<L, E> {
        self.fold(Ok, |r| Err(err(r)))
    }

    #[inline]
    pub fn ok_r_or<E>(self, err: E) -> Result<R, E> {
        self.fold(|_| Err(err), Ok)
    }

    #[inline]
    pub fn ok_r_or_else<E, F: FnOnce(L) -> E>(self, err: F) -> Result<R, E> {
        self.fold(|l| Err(err(l)), Ok)
    }

    #[inline]
    pub fn into_result(self) -> Result<L, R> {
        self.fold(Ok, Err)
    }

    #[inline]
    #[must_use]
    pub fn unwrap_l_or(self, default: L) -> L {
        self.fold_r(|_| default)
    }

    #[inline]
    #[must_use]
    pub fn unwrap_r_or(self, default: R) -> R {
        self.fold_l(|_| default)
    }

    #[inline]
    #[must_use]
    pub fn unwrap_l_or_else<F>(self, f: F) -> L
    where
        F: FnOnce() -> L,
    {
        self.fold_r(|_| f())
    }

    #[inline]
    #[must_use]
    pub fn unwrap_r_or_else<F>(self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        self.fold_l(|_| f())
    }

    #[inline]
    #[must_use]
    pub fn unwrap_l_or_default<F>(self) -> L
    where
        L: Default,
    {
        self.unwrap_l_or_else(Default::default)
    }

    #[inline]
    #[must_use]
    pub fn unwrap_r_or_default<F>(self) -> R
    where
        R: Default,
    {
        self.unwrap_r_or_else(Default::default)
    }

    #[inline]
    pub fn unwrap_l(self) -> L {
        match self {
            Inl(l) => l,
            Inr(_) => panic!("called `Either::unwrap_l` on a `Inr` value"),
        }
    }

    #[inline]
    pub fn unwrap_r(self) -> R {
        match self {
            Inl(_) => panic!("called `Either::unwrap_r` on a `Inl` value"),
            Inr(r) => r,
        }
    }

    /// # Safety
    /// The value must be `Inl`. Calling this method on an `Inr` value is undefined behaviour.
    #[inline]
    pub unsafe fn unwrap_l_unchecked(self) -> L {
        match self {
            Inl(l) => l,
            // SAFETY:
            // The caller is responsible for ensuring that the value is not `Inr`.
            Inr(_) => hint::unreachable_unchecked(),
        }
    }

    /// # Safety
    /// The value must be `Inr`. Calling this method on an `Inl` value is undefined behaviour.
    #[inline]
    pub unsafe fn unwrap_r_unchecked(self) -> R {
        match self {
            // SAFETY:
            // The caller is responsible for ensuring that the value is not `Inl`.
            Inl(_) => hint::unreachable_unchecked(),
            Inr(r) => r,
        }
    }

    #[inline]
    pub fn expect_l(self, msg: &str) -> L {
        match self {
            Inl(l) => l,
            Inr(_) => panic!("{}", msg),
        }
    }

    #[inline]
    pub fn expect_r(self, msg: &str) -> R {
        match self {
            Inl(_) => panic!("{}", msg),
            Inr(r) => r,
        }
    }

    #[inline]
    pub fn inspect<F, G>(self, f: F, g: G) -> Either<L, R>
    where
        F: FnOnce(&L),
        G: FnOnce(&R),
    {
        match self {
            Inl(ref l) => f(l),
            Inr(ref r) => g(r),
        };
        self
    }

    #[inline]
    pub fn inspect_l<F, G>(self, f: F) -> Either<L, R>
    where
        F: FnOnce(&L),
    {
        if let Inl(ref l) = self {
            f(l);
        }
        self
    }

    #[inline]
    pub fn inspect_r<F, G>(self, f: F) -> Either<L, R>
    where
        F: FnOnce(&R),
    {
        if let Inr(ref r) = self {
            f(r);
        }
        self
    }
}

impl<L, R> Either<&L, &R> {
    #[inline]
    #[must_use]
    pub fn cloned(self) -> Either<L, R>
    where
        L: Clone,
        R: Clone,
    {
        self.map(clone, clone)
    }

    #[inline]
    #[must_use]
    pub fn copied(self) -> Either<L, R>
    where
        L: Copy,
        R: Copy,
    {
        self.map(copy, copy)
    }
}

impl<L, R> Either<&L, R> {
    #[inline]
    #[must_use]
    pub fn cloned_l(self) -> Either<L, R>
    where
        L: Clone,
    {
        self.map_l(clone)
    }

    #[inline]
    #[must_use]
    pub fn copied_l(self) -> Either<L, R>
    where
        L: Copy,
    {
        self.map_l(copy)
    }
}

impl<L, R> Either<L, &R> {
    #[inline]
    #[must_use]
    pub fn cloned_r(self) -> Either<L, R>
    where
        R: Clone,
    {
        self.map_r(clone)
    }

    #[inline]
    #[must_use]
    pub fn copied_r(self) -> Either<L, R>
    where
        R: Copy,
    {
        self.map_r(copy)
    }
}

impl<L, R> Either<&mut L, &mut R> {
    #[inline]
    #[must_use]
    pub fn cloned(self) -> Either<L, R>
    where
        L: Clone,
        R: Clone,
    {
        self.map(clone_mut, clone_mut)
    }

    #[inline]
    #[must_use]
    pub fn copied(self) -> Either<L, R>
    where
        L: Copy,
        R: Copy,
    {
        self.map(copy_mut, copy_mut)
    }
}

impl<L, R> Either<&mut L, R> {
    #[inline]
    #[must_use]
    pub fn cloned_l(self) -> Either<L, R>
    where
        L: Clone,
    {
        self.map_l(clone_mut)
    }

    #[inline]
    #[must_use]
    pub fn copied_l(self) -> Either<L, R>
    where
        L: Copy,
    {
        self.map_l(copy_mut)
    }
}

impl<L, R> Either<L, &mut R> {
    #[inline]
    #[must_use]
    pub fn cloned_r(self) -> Either<L, R>
    where
        R: Clone,
    {
        self.map_r(clone_mut)
    }

    #[inline]
    #[must_use]
    pub fn copied_r(self) -> Either<L, R>
    where
        R: Copy,
    {
        self.map_r(copy_mut)
    }
}

impl<T> Either<T, T> {
    #[inline]
    #[must_use]
    pub fn fold_symmetric(self) -> T {
        self.fold(identity, identity)
    }
}

impl<T> Either<T, ()> {
    #[inline]
    #[must_use]
    pub fn from_option(option: Option<T>) -> Self {
        option.map_or(Inr(()), Inl)
    }

    #[inline]
    #[must_use]
    pub fn into_option(self) -> Option<T> {
        self.fold(Some, |_| None)
    }
}

impl<T> From<Either<T, ()>> for Option<T> {
    #[inline]
    fn from(either: Either<T, ()>) -> Self {
        either.into_option()
    }
}

impl<T> From<Option<T>> for Either<T, ()> {
    #[inline]
    fn from(option: Option<T>) -> Self {
        Either::from_option(option)
    }
}

impl<L, R> From<Either<L, R>> for Result<L, R> {
    #[inline]
    fn from(either: Either<L, R>) -> Self {
        either.into_result()
    }
}

impl<L, R> From<Result<L, R>> for Either<L, R> {
    #[inline]
    fn from(result: Result<L, R>) -> Self {
        Either::from_result(result)
    }
}

impl<L, R> Empty for Either<L, R>
where
    L: Empty,
    R: Empty,
{
    #[inline]
    fn elim<T>(self) -> T {
        self.fold(<L as Empty>::elim, <R as Empty>::elim)
    }
}

impl<L, R> Termination for Either<L, R>
where
    L: Termination,
    R: Termination,
{
    #[inline]
    fn report(self) -> ExitCode {
        self.fold(<L as Termination>::report, <R as Termination>::report)
    }
}

impl<L, R> fmt::Display for Either<L, R>
where
    L: fmt::Display,
    R: fmt::Display,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Inl(l) => <L as fmt::Display>::fmt(l, f),
            Inr(r) => <R as fmt::Display>::fmt(r, f),
        }
    }
}
