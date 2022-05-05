use crate::pos::Sp;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(in crate::formats::anm) enum SoftOption<T> {
    Missing,
    /// A value obtained from an image source.  Soft values can still be replaced by newer values.
    Soft(T),
    /// A value explicitly provided by the user.  These do NOT get replaced by newer values.
    Explicit(Sp<T>),
}

impl<T> Default for SoftOption<T> {
    fn default() -> Self { SoftOption::Missing }
}

#[allow(unused)]
impl<T> SoftOption<T> {
    pub fn is_missing(&self) -> bool { matches!(self, SoftOption::Missing) }

    /// Set `self` "explicitly" (preventing future modification).
    pub fn set_explicit(&mut self, value: Sp<T>) {
        if matches!(self, SoftOption::Missing | SoftOption::Soft(_)) {
            *self = SoftOption::Explicit(value);
        }
    }
    /// Set `self` "softly" (allowing future calls to overwrite it again).
    pub fn set_soft(&mut self, value: T) {
        if matches!(self, SoftOption::Missing | SoftOption::Soft(_)) {
            *self = SoftOption::Soft(value);
        }
    }
    /// Set `self` "softly", only if the value is missing.  (use to supply a default value)
    pub fn set_soft_if_missing(&mut self, value: T) {
        if matches!(self, SoftOption::Missing) {
            *self = SoftOption::Soft(value);
        }
    }
    pub fn filter(self, predicate: impl FnOnce(&T) -> bool) -> Self {
        if let SoftOption::Soft(x) | SoftOption::Explicit(sp_pat!(x)) = &self {
            if predicate(x) {
                return SoftOption::Missing;
            }
        }
        self
    }
    pub fn into_option(self) -> Option<T> {
        match self {
            SoftOption::Missing => None,
            SoftOption::Soft(value) => Some(value),
            SoftOption::Explicit(value) => Some(value.value),
        }
    }
}
