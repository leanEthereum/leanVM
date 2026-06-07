use std::ops::{Add, Sub};

use field::*;
use zk_alloc::{ArenaVec, OwnedBuffer};

use crate::{EFPacking, PF, PFPacking};

pub const PARALLEL_THRESHOLD: usize = 1 << 9;

/// AoS->SoA transpose of `slice` into the already-sized packed buffer `out` (`out.len()`
/// packed elements, each consuming `packing_width` scalars).
fn fill_packed_extension<EF: ExtensionField<PF<EF>>>(slice: &[EF], out: &mut [EFPacking<EF>]) {
    let width = packing_width::<EF>();
    let write = |slot: &mut EFPacking<EF>, chunk: &[EF]| {
        *slot = EFPacking::<EF>::from_ext_slice(chunk);
    };
    if slice.len() < PARALLEL_THRESHOLD {
        for (slot, chunk) in out.iter_mut().zip(slice.chunks_exact(width)) {
            write(slot, chunk);
        }
    } else {
        parallel::par_for_each_mut(out, |idx, slot| {
            write(slot, &slice[idx * width..][..width]);
        });
    }
}

pub fn pack_extension<EF: ExtensionField<PF<EF>>, B: OwnedBuffer<EFPacking<EF>>>(slice: &[EF]) -> B {
    B::build(slice.len() / packing_width::<EF>(), |out| {
        fill_packed_extension(slice, out)
    })
}

fn fill_unpacked_extension<EF: ExtensionField<PF<EF>>>(vec: &[EFPacking<EF>], out: &mut [EF]) {
    let width = packing_width::<EF>();
    let total = out.len();
    let write = |out_chunk: &mut [EF], x: &EFPacking<EF>| {
        let packed_coeffs = x.as_basis_coefficients_slice();
        for (lane, slot) in out_chunk.iter_mut().enumerate() {
            *slot = EF::from_basis_coefficients_fn(|j| packed_coeffs[j].as_slice()[lane]);
        }
    };
    if total < PARALLEL_THRESHOLD {
        for (chunk, x) in out.chunks_exact_mut(width).zip(vec.iter()) {
            write(chunk, x);
        }
    } else {
        // One pool task per group of `group` packed elements, each writing `group * width`
        // contiguous output scalars from a disjoint slice of `vec`.
        let group = parallel::recommended_chunk_size(vec.len());
        parallel::par_chunks_mut(out, group * width, |ci, out_chunk| {
            for (k, sub) in out_chunk.chunks_exact_mut(width).enumerate() {
                write(sub, &vec[ci * group + k]);
            }
        });
    }
}

pub fn unpack_extension<EF: ExtensionField<PF<EF>>, B: OwnedBuffer<EF>>(vec: &[EFPacking<EF>]) -> B {
    B::build(vec.len() * packing_width::<EF>(), |out| {
        fill_unpacked_extension(vec, out)
    })
}

pub const fn packing_log_width<EF: Field>() -> usize {
    packing_width::<EF>().ilog2() as usize
}

pub const fn packing_width<EF: Field>() -> usize {
    PFPacking::<EF>::WIDTH
}

pub const fn must_unpack_multilinears<EF: Field>(n_vars: usize) -> bool {
    n_vars <= 1 + packing_log_width::<EF>()
}

#[inline]
fn fill_fold<OF: Send, C: Fn(usize) -> OF + Sync>(res: &mut [OF], seq: bool, compute: C) {
    if seq || res.len() < PARALLEL_THRESHOLD {
        for (i, r) in res.iter_mut().enumerate() {
            *r = compute(i);
        }
    } else {
        parallel::par_fill(res, &compute);
    }
}

#[inline]
fn fold_fill<OF: Send, B: OwnedBuffer<OF>, C: Fn(usize) -> OF + Sync>(len: usize, seq: bool, compute: C) -> B {
    B::build(len, |res| fill_fold(res, seq, compute))
}

pub fn fold_multilinear<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    F: Fn(IF, EF) -> OF + Sync + Send,
    B: OwnedBuffer<OF>,
>(
    m: &[IF],
    alpha: EF,
    mul_if_of: &F,
    seq: bool,
) -> B {
    let new_size = m.len() / 2;
    fold_fill(new_size, seq, |i| mul_if_of(m[i + new_size] - m[i], alpha) + m[i])
}

pub fn fold_multilinear_at_bit<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    F: Fn(IF, EF) -> OF + Sync + Send,
    B: OwnedBuffer<OF>,
>(
    m: &[IF],
    alpha: EF,
    bit: usize,
    mul_if_of: &F,
    seq: bool,
) -> B {
    assert!(m.len() >= 2 * (1 << bit), "bit out of range for slice length");
    if bit == 0 {
        return fold_fill(m.len() / 2, seq, |j| {
            mul_if_of(m[2 * j + 1] - m[2 * j], alpha) + m[2 * j]
        });
    }
    let stride = 1usize << bit;
    let lo_mask = stride - 1;
    fold_fill(m.len() / 2, seq, |new_j| {
        let i_hi = new_j >> bit;
        let i_lo = new_j & lo_mask;
        let i0 = (i_hi << (bit + 1)) | i_lo;
        let i1 = i0 | stride;
        mul_if_of(m[i1] - m[i0], alpha) + m[i0]
    })
}

pub fn batch_fold_multilinears<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    F: Fn(IF, EF) -> OF + Sync + Send,
>(
    polys: &[&[IF]],
    alpha: EF,
    mul_if_of: F,
) -> Vec<ArenaVec<OF>> {
    let total_size: usize = polys.iter().map(|p| p.len()).sum();
    if total_size < PARALLEL_THRESHOLD {
        polys
            .iter()
            .map(|poly| fold_multilinear(poly, alpha, &mul_if_of, true))
            .collect()
    } else {
        parallel::par_map_collect(polys.len(), |i| fold_multilinear(polys[i], alpha, &mul_if_of, true))
    }
}

pub fn batch_fold_multilinears_at_bit<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    F: Fn(IF, EF) -> OF + Sync + Send,
>(
    polys: &[&[IF]],
    alpha: EF,
    bit: usize,
    mul_if_of: F,
) -> Vec<ArenaVec<OF>> {
    let total_size: usize = polys.iter().map(|p| p.len()).sum();
    if total_size < PARALLEL_THRESHOLD {
        polys
            .iter()
            .map(|poly| fold_multilinear_at_bit(poly, alpha, bit, &mul_if_of, true))
            .collect()
    } else {
        parallel::par_map_collect(polys.len(), |i| {
            fold_multilinear_at_bit(polys[i], alpha, bit, &mul_if_of, true)
        })
    }
}

/// Returns a vector of uninitialized elements of type `A` with the specified length.
/// # Safety
/// Entries should be overwritten before use.
#[must_use]
pub unsafe fn uninitialized_vec<A>(len: usize) -> Vec<A> {
    #[allow(clippy::uninit_vec)]
    unsafe {
        let mut vec = Vec::with_capacity(len);
        vec.set_len(len);
        vec
    }
}

pub fn split_at_mut_many<'a, A>(slice: &'a mut [A], indices: &[usize]) -> Vec<&'a mut [A]> {
    for i in 0..indices.len() {
        if i > 0 {
            assert!(indices[i] > indices[i - 1]);
        }
        assert!(indices[i] <= slice.len());
    }

    if indices.is_empty() {
        return vec![slice];
    }

    let mut result = Vec::with_capacity(indices.len() + 1);
    let mut current_slice = slice;
    let mut prev_idx = 0;

    for &idx in indices {
        let adjusted_idx = idx - prev_idx;
        let (left, right) = current_slice.split_at_mut(adjusted_idx);
        result.push(left);
        current_slice = right;
        prev_idx = idx;
    }

    result.push(current_slice);

    result
}

// Sequential

pub fn iter_split_4<A>(u: &[A]) -> impl Iterator<Item = ((&A, &A), (&A, &A))> {
    let n = u.len();
    assert!(n.is_multiple_of(4));
    let (u_left, u_right) = u.split_at(n / 2);
    let (u_ll, u_lr) = u_left.split_at(n / 4);
    let (u_rl, u_rr) = u_right.split_at(n / 4);
    u_ll.iter().zip(u_lr.iter()).zip(u_rl.iter().zip(u_rr.iter()))
}

pub fn iter_mut_split_2<A>(u: &mut [A]) -> impl Iterator<Item = (&mut A, &mut A)> {
    let n = u.len();
    assert!(n.is_multiple_of(2));
    let (u_left, u_right) = u.split_at_mut(n / 2);
    u_left.iter_mut().zip(u_right.iter_mut())
}

#[allow(clippy::type_complexity)]
pub fn zip_fold_2<'a, 'b, A, B>(
    u: &'a [A],
    folded: &'b mut [B],
) -> impl Iterator<Item = (((&'a A, &'a A), (&'a A, &'a A)), (&'b mut B, &'b mut B))> {
    let n = u.len();
    assert!(n.is_multiple_of(4));
    assert_eq!(folded.len(), n / 2);
    iter_split_4(u).zip(iter_mut_split_2(folded))
}

pub fn to_big_endian_bits(value: usize, bit_count: usize) -> Vec<bool> {
    (0..bit_count).rev().map(|i| (value >> i) & 1 == 1).collect()
}

pub fn to_big_endian_in_field<F: Field>(value: usize, bit_count: usize) -> Vec<F> {
    (0..bit_count)
        .rev()
        .map(|i| F::from_bool((value >> i) & 1 == 1))
        .collect()
}

pub fn to_little_endian_bits(value: usize, bit_count: usize) -> Vec<bool> {
    let mut res = to_big_endian_bits(value, bit_count);
    res.reverse();
    res
}

#[cfg(test)]
mod bench_tests {
    use std::time::{Duration, Instant};

    use koala_bear::QuinticExtensionFieldKB;
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    use super::*;

    type EF = QuinticExtensionFieldKB;

    const LOG_SIZES: [usize; 6] = [8, 12, 16, 20, 22, 24];
    const REPETITIONS: usize = 10;

    fn print_header(name: &str) {
        println!(
            "\nBenchmarking {} (packing_width = {}, repetitions = {})",
            name,
            packing_width::<EF>(),
            REPETITIONS
        );
        println!(
            "{:>10} | {:>14} | {:>14} | {:>14} | {:>14}",
            "log_n", "n_ext_elems", "avg (ms)", "min (ms)", "max (ms)"
        );
    }

    fn measure<R>(mut f: impl FnMut() -> R) -> (Duration, Duration, Duration) {
        let mut total = Duration::ZERO;
        let mut min_t = Duration::MAX;
        let mut max_t = Duration::ZERO;
        for _ in 0..REPETITIONS {
            let t = Instant::now();
            let out = f();
            let d = t.elapsed();
            std::hint::black_box(out);
            total += d;
            if d < min_t {
                min_t = d;
            }
            if d > max_t {
                max_t = d;
            }
        }
        (total / REPETITIONS as u32, min_t, max_t)
    }

    fn print_row(log_n: usize, n: usize, avg: Duration, min_t: Duration, max_t: Duration) {
        println!(
            "{:>10} | {:>14} | {:>14.3} | {:>14.3} | {:>14.3}",
            log_n,
            n,
            avg.as_secs_f64() * 1000.0,
            min_t.as_secs_f64() * 1000.0,
            max_t.as_secs_f64() * 1000.0,
        );
    }

    #[test]
    fn bench_unpack_extension() {
        let mut rng = StdRng::seed_from_u64(0);
        print_header("unpack_extension");
        for &log_n in &LOG_SIZES {
            let n = 1usize << log_n;
            let ext_vec: Vec<EF> = (0..n).map(|_| rng.random()).collect();
            let packed: Vec<_> = pack_extension(&ext_vec);
            let _ = unpack_extension::<EF, Vec<_>>(&packed); // warmup
            let (avg, min_t, max_t) = measure(|| unpack_extension::<EF, Vec<_>>(&packed));
            print_row(log_n, n, avg, min_t, max_t);
        }
    }

    #[test]
    fn bench_pack_extension() {
        let mut rng = StdRng::seed_from_u64(0);
        print_header("pack_extension");
        for &log_n in &LOG_SIZES {
            let n = 1usize << log_n;
            let ext_vec: Vec<EF> = (0..n).map(|_| rng.random()).collect();
            let _ = pack_extension::<EF, Vec<_>>(&ext_vec); // warmup
            let (avg, min_t, max_t) = measure(|| pack_extension::<EF, Vec<_>>(&ext_vec));
            print_row(log_n, n, avg, min_t, max_t);
        }
    }
}
