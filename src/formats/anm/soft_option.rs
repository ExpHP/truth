use crate::pos::Sp;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(in crate::formats::anm) enum SoftOption<T> {
    Missing,
    /// No value came from either an ANM source
    Defaulted(T),
    /// A value obtained from an image source.  These values are "soft" and can still be replaced by newer values.
    FromImageSource(T),
    /// A value explicitly provided by the user.  These do NOT get replaced by newer values.
    Explicit(Sp<T>),
}

impl<T> Default for SoftOption<T> {
    fn default() -> Self { SoftOption::Missing }
}

#[allow(unused)]
impl<T> SoftOption<T> {
    pub fn is_missing(&self) -> bool { matches!(self, SoftOption::Missing) }
    pub fn is_from_image_source(&self) -> bool { matches!(self, SoftOption::FromImageSource(_)) }
    pub fn is_explicit(&self) -> bool { matches!(self, SoftOption::Explicit(_)) }

    /// Set `self` "explicitly" (preventing future modification).
    pub fn set_explicit(&mut self, value: Sp<T>) {
        if !matches!(self, SoftOption::Explicit(_)) {
            *self = SoftOption::Explicit(value);
        }
    }

    /// Set `self` "softly" (i.e. only if not already explicitly set by the user, and in a way
    /// that allows future calls to overwrite it again).
    pub fn set_softly_from_image_source(&mut self, value: T) {
        if !matches!(self, SoftOption::Explicit(_)) {
            *self = SoftOption::FromImageSource(value);
        }
    }

    /// Set `self` only if the value is missing.  Used near the end of processing to set defaults
    /// (which may be derived from other values).
    pub fn set_default_if_missing(&mut self, value: T) {
        if matches!(self, SoftOption::Missing) {
            *self = SoftOption::Defaulted(value);
        }
    }

    pub fn filter(self, predicate: impl FnOnce(&T) -> bool) -> Self {
        if let Some(x) = self.as_option() {
            if predicate(x) {
                return SoftOption::Missing;
            }
        }
        self
    }

    pub fn as_explicit(&self) -> Option<Sp<&T>> {
        match self {
            SoftOption::Explicit(value) => Some(sp!(value.span => value)),
            _ => None,
        }
    }

    pub fn as_option(&self) -> Option<&T> {
        match self {
            SoftOption::Missing => None,
            SoftOption::Defaulted(value) => Some(value),
            SoftOption::FromImageSource(value) => Some(value),
            SoftOption::Explicit(value) => Some(value),
        }
    }

    pub fn into_option(self) -> Option<T> {
        match self {
            SoftOption::Missing => None,
            SoftOption::Defaulted(value) => Some(value),
            SoftOption::FromImageSource(value) => Some(value),
            SoftOption::Explicit(value) => Some(value.value),
        }
    }
}
