use std::sync::atomic::{AtomicPtr, Ordering};

pub fn from_end<A>(slice: &[A], n: usize) -> &[A] {
    assert!(n <= slice.len());
    &slice[slice.len() - n..]
}

pub fn transposed_par_for_each_mut<A: Send + Sync, const N: usize, G>(array: &mut [Vec<A>; N], g: G)
where
    G: Fn(usize, [&mut A; N]) + Sync,
{
    // all vectors must have the same length
    let len = array[0].len();
    let data_ptrs: [AtomicPtr<A>; N] = array.each_mut().map(|v| AtomicPtr::new(v.as_mut_ptr()));

    parallel::for_each_index(len, |i| {
        let row: [&mut A; N] = unsafe { std::array::from_fn(|j| &mut *data_ptrs[j].load(Ordering::Relaxed).add(i)) };
        g(i, row);
    });
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
