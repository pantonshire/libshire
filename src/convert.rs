use std::convert::Infallible;

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

/// The bottom type ⊥ with no elements. Since it has no elements, having an element of `Bot` is an
/// inherent contradiction and it can therefore be converted to any other type. In MLTT, this
/// corresponds to a proof by contradiction.
/// 
/// `Bot` serves the same purpose as `std::convert::Infallible` and the currently unstable "never"
/// type `!`, but provides more convenience methods than the former.
pub struct Bot(BotRepr);

impl Bot {
    #[inline]
    #[must_use]
    pub const fn elim<T>(self) -> T {
        self.0.elim()
    }

    #[inline]
    #[must_use]
    pub const fn elim_ref<T>(&self) -> T {
        self.0.elim()
    }

    #[inline]
    pub const fn never(self) -> ! {
        self.elim()
    }
}

impl Clone for Bot {
    #[inline]
    fn clone(&self) -> Self {
        self.elim_ref()
    }
}

impl Copy for Bot {}

impl From<Infallible> for Bot {
    #[inline]
    fn from(infallible: Infallible) -> Self {
        infallible_elim(infallible)
    }
}

impl From<Bot> for Infallible {
    #[inline]
    fn from(bot: Bot) -> Self {
        bot.elim()
    }
}

enum BotRepr {}

impl BotRepr {
    #[inline]
    const fn elim<T>(self) -> T {
        match self {}
    }

    #[inline]
    const fn elim_ref<T>(&self) -> T {
        match *self {}
    }
}

impl Clone for BotRepr {
    #[inline]
    fn clone(&self) -> Self {
        self.elim_ref()
    }
}

impl Copy for BotRepr {}

#[inline]
#[must_use]
pub fn clone<T: Clone>(x: &T) -> T {
    x.clone()
}

#[inline]
#[must_use]
pub fn clone_mut<T: Clone>(x: &mut T) -> T {
    (&*x).clone()
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
