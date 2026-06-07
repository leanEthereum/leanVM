use std::ops::Deref;

use crate::ArenaVec;

#[derive(Debug)]
pub enum ArenaCow<'a, T> {
    Borrowed(&'a [T]),
    Owned(ArenaVec<T>),
}

impl<T> ArenaCow<'_, T> {
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        match self {
            Self::Borrowed(s) => s,
            Self::Owned(v) => v,
        }
    }

    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.as_slice().is_empty()
    }
}

impl<T: Clone> ArenaCow<'_, T> {
    /// Take ownership of the buffer, copying into the arena only if currently borrowed.
    #[inline]
    #[must_use]
    pub fn into_owned(self) -> ArenaVec<T> {
        match self {
            Self::Borrowed(s) => ArenaVec::from_slice(s),
            Self::Owned(v) => v,
        }
    }
}

impl<'a, T> From<&'a [T]> for ArenaCow<'a, T> {
    #[inline]
    fn from(s: &'a [T]) -> Self {
        Self::Borrowed(s)
    }
}

impl<T> From<ArenaVec<T>> for ArenaCow<'_, T> {
    #[inline]
    fn from(v: ArenaVec<T>) -> Self {
        Self::Owned(v)
    }
}

impl<T> Deref for ArenaCow<'_, T> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> AsRef<[T]> for ArenaCow<'_, T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}
