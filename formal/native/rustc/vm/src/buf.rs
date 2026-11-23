//! A fixed-capacity array (`EVec`, `WVec` of `NativeVm/Code/Data.lean`): its count, then its
//! entries, up to the capacity `N`. Every operation that would pass the capacity rejects (`None`).

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Buf<T: Copy, const N: usize> {
    pub len: usize,
    pub items: [T; N],
}

impl<T: Copy, const N: usize> Buf<T, N> {
    /// The entries.
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        self.items.get(..self.len).unwrap_or(&[])
    }

    /// The empty array.
    #[inline(always)]
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Append `x`.
    #[inline(always)]
    pub fn push(&mut self, x: T) -> Option<()> {
        let slot = self.items.get_mut(self.len)?;
        *slot = x;
        self.len += 1;
        Some(())
    }

    /// Append `xs`.
    #[inline(never)]
    pub fn extend(&mut self, xs: &[T]) -> Option<()> {
        for &x in xs {
            self.push(x)?;
        }
        Some(())
    }

    /// The array `xs`.
    #[inline(always)]
    pub fn set(&mut self, xs: &[T]) -> Option<()> {
        self.clear();
        self.extend(xs)
    }

    /// `n` entries, to be written through the slice returned.
    #[inline(always)]
    pub fn resize(&mut self, n: usize) -> Option<&mut [T]> {
        let slice = self.items.get_mut(..n)?;
        self.len = n;
        Some(slice)
    }
}
