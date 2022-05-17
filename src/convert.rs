use std::convert::Infallible;

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
    pub fn elim<T>(self) -> T {
        self.0.elim()
    }

    #[inline]
    #[must_use]
    pub fn elim_ref<T>(&self) -> T {
        self.0.elim()
    }

    #[inline]
    pub fn never(self) -> ! {
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
    fn from(infallible: Infallible) -> Self {
        infallible_elim(infallible)
    }
}

impl From<Bot> for Infallible {
    fn from(bot: Bot) -> Self {
        bot.elim()
    }
}

enum BotRepr {}

impl BotRepr {
    #[inline]
    fn elim<T>(self) -> T {
        match self {}
    }

    #[inline]
    fn elim_ref<T>(&self) -> T {
        match *self {}
    }
}

impl Clone for BotRepr {
    fn clone(&self) -> Self {
        self.elim_ref()
    }
}

impl Copy for BotRepr {}

#[inline]
#[must_use]
pub fn infallible_elim<T>(infallible: Infallible) -> T {
    match infallible {}
}

#[inline]
pub fn infallible_to_never(infallible: Infallible) -> ! {
    infallible_elim(infallible)
}
