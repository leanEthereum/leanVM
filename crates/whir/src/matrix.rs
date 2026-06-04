// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use std::marker::PhantomData;

use field::PackedValue;

pub type MatrixViewMut<'a, T> = Matrix<T, &'a mut [T]>;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Dimensions {
    /// Number of columns in the matrix.
    pub width: usize,
    /// Number of rows in the matrix.
    pub height: usize,
}

/// Dense, row-major matrix backed by a flat buffer `V` (owned `Vec<T>` or a borrowed slice).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Matrix<T, V = Vec<T>> {
    /// Flat buffer of matrix values in row-major order.
    pub values: V,
    /// Number of columns; the number of rows is `values.len() / width`.
    pub width: usize,
    /// Marker for the element type `T` (needed when `V` does not contain `T`).
    _phantom: PhantomData<T>,
}

impl<T: Clone + Send + Sync, V: AsRef<[T]> + Send + Sync> Matrix<T, V> {
    /// Create a new dense matrix of the given dimensions, backed by the given storage.
    ///
    /// It is undefined behavior to create a matrix such that `values.len() % width != 0`.
    #[must_use]
    pub fn new(values: V, width: usize) -> Self {
        debug_assert!(values.as_ref().len().is_multiple_of(width));
        Self {
            values,
            width,
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn width(&self) -> usize {
        self.width
    }

    #[inline]
    pub fn height(&self) -> usize {
        self.values.as_ref().len().checked_div(self.width).unwrap_or(0)
    }

    pub fn as_view_mut(&mut self) -> MatrixViewMut<'_, T>
    where
        V: AsMut<[T]>,
    {
        MatrixViewMut::new(self.values.as_mut(), self.width)
    }

    /// Row `r` as an iterator over its values, or `None` if out of bounds.
    #[inline]
    pub fn row(&self, r: usize) -> Option<impl Iterator<Item = T> + '_> {
        (r < self.height()).then(|| {
            let start = r * self.width;
            self.values.as_ref()[start..start + self.width].iter().cloned()
        })
    }

    /// Packs `P::WIDTH` consecutive rows column-by-column, right-to-left, with `n_leading_zeros`
    /// zero packings prepended.
    ///
    /// Safety: caller must ensure `r + P::WIDTH <= height` and `effective_width <= width`.
    #[inline]
    pub fn vertically_packed_row_rtl<P>(
        &self,
        r: usize,
        effective_width: usize,
        n_leading_zeros: usize,
    ) -> impl Iterator<Item = P>
    where
        T: Copy,
        P: PackedValue<Value = T> + Default,
    {
        let width = self.width;
        debug_assert!(effective_width <= width);
        debug_assert!(r + P::WIDTH <= self.height());
        let values = self.values.as_ref();
        let base = r * width;
        (0..n_leading_zeros).map(|_| P::default()).chain(
            (0..effective_width)
                .rev()
                .map(move |c| P::from_fn(|i| unsafe { *values.get_unchecked(base + i * width + c) })),
        )
    }
}
