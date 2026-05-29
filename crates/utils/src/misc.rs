use std::sync::atomic::{AtomicPtr, Ordering};

use backend::*;

pub fn from_end<A>(slice: &[A], n: usize) -> &[A] {
    assert!(n <= slice.len());
    &slice[slice.len() - n..]
}

/// Run `g(i, row)` in parallel over `i in 0..len`, where `row` is `[&mut A; N]` holding
/// the `i`-th element of each of the `N` equal-length vectors (a transposed row).
/// Dispatched through the in-house [`parallel`] pool.
pub fn transposed_par_for_each_mut<A: Send + Sync, const N: usize, G>(array: &mut [Vec<A>; N], g: G)
where
    G: Fn(usize, [&mut A; N]) + Sync,
{
    // all vectors must have the same length
    let len = array[0].len();
    let data_ptrs: [AtomicPtr<A>; N] = array.each_mut().map(|v| AtomicPtr::new(v.as_mut_ptr()));

    parallel::for_each_index(len, |i| {
        // SAFETY: distinct `i` access disjoint row `i` of each of the `N` vectors, and the
        // arrays outlive the dispatch (the dispatcher blocks until all tasks complete).
        let row: [&mut A; N] = unsafe { std::array::from_fn(|j| &mut *data_ptrs[j].load(Ordering::Relaxed).add(i)) };
        g(i, row);
    });
}

pub fn collect_refs<T>(vecs: &[Vec<T>]) -> Vec<&[T]> {
    vecs.iter().map(Vec::as_slice).collect()
}

#[derive(Debug, Clone, Default)]
pub struct Counter(usize);

impl Counter {
    pub fn get_next(&mut self) -> usize {
        let val = self.0;
        self.0 += 1;
        val
    }

    pub fn new() -> Self {
        Self(0)
    }
}
