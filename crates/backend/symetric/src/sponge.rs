// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;
use field::PrimeCharacteristicRing;

/// Absorbs `data` RTL into an IV state `[data.len(), 0, ..., 0]` in RATE-sized chunks.
/// assumes data length is a multiple of RATE (= 8 in practice).
pub fn hash_slice<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, data: &[T]) -> [T; OUT]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    debug_assert!(data.len().is_multiple_of(RATE));
    let mut state = [T::default(); WIDTH];
    state[0] = T::from_usize(data.len());
    for chunk in data.chunks_exact(RATE).rev() {
        state[WIDTH - RATE..].copy_from_slice(chunk);
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}

/// Precompute sponge state after absorbing `n_zero_chunks` all-zero RATE-chunks
/// into an IV state `[iv_first, 0, ..., 0]`. Caller provides `iv_first` (typically
/// the length, in field elements, of the full slice that will eventually be hashed).
pub fn precompute_zero_suffix_state<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    iv_first: T,
    n_zero_chunks: usize,
) -> [T; WIDTH]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state = [T::default(); WIDTH];
    state[0] = iv_first;
    for _ in 0..n_zero_chunks {
        for s in &mut state[WIDTH - RATE..] {
            *s = T::default();
        }
        comp.compress_mut(&mut state);
    }
    state
}

/// RTL = Right-to-left. Absorbs starting from the provided `initial_state` in RATE-sized chunks.
#[inline(always)]
pub fn hash_rtl_iter_with_initial_state<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    mut iter: I,
    initial_state: &[T; WIDTH],
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state = *initial_state;
    while let Some(elem) = iter.next() {
        state[WIDTH - 1] = elem;
        for pos in (WIDTH - RATE..WIDTH - 1).rev() {
            state[pos] = iter.next().unwrap();
        }
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}
