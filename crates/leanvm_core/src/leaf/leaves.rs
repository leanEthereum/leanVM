//! The prover's leaf vectors: one leaf per row of a block, the producers' bits raised to their powers.

use super::{Block, Coord, Layout, Producer};
use crate::{PAR_THRESHOLD, gkr};
use parallel::Chunks;
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use primitives::field::MixedSums8;
use primitives::field::{F64, F192};
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        not(target_feature = "vpclmulqdq")
    )
)))]
use primitives::field::{F192Unreduced, mul2, mul4};
#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        not(target_feature = "vpclmulqdq")
    )
))]
use primitives::field::{F192x1, F192x1Unreduced};
use std::mem::MaybeUninit;
use std::ops::Range;

/// A non-constant coordinate as `(source, coefficient)`: its leaf contribution is
/// the mixed product `coeff · source(z)` with `source(z) ∈ K`, `coeff ∈ E`.
enum Term<'a> {
    Col(usize, F192),
    Prod(usize, usize, F192),
    IntIndex(F192, u32),
    Public(&'a [F64], F192),
}

/// Flatten one coordinate into leaf terms at coefficient `w`. A [`Coord::Sum`]
/// spreads its children over the SAME `w`: they are one coordinate, so they share
/// its `α`-power.
fn push_terms<'a>(c: &'a Coord, w: F192, terms: &mut Vec<Term<'a>>, constant: &mut F192) {
    match c {
        Coord::Const(v) => *constant += w.mul_base(*v),
        Coord::Col(i) => terms.push(Term::Col(*i, w)),
        Coord::Prod(i, j) => terms.push(Term::Prod(*i, *j, w)),
        Coord::Scaled(c, i) => terms.push(Term::Col(*i, w.mul_base(*c))),
        Coord::IntIndex { base, shift } => {
            *constant += w.mul_base(*base);
            terms.push(Term::IntIndex(w, *shift));
        }
        Coord::Public(column) => terms.push(Term::Public(column.values.as_slice(), w)),
        Coord::Sparse(column) => terms.push(Term::Public(column.dense(), w)),
        Coord::Sum(cs) => {
            for c in cs {
                push_terms(c, w, terms, constant);
            }
        }
    }
}

/// Rows per task of a block's leaf fill, a multiple of eight.
const LEAF_CHUNK: usize = 1 << 10;

/// One tuple's leaves, `β − Σ_i w_i c_i(z)` for every row `z`, into `dst`. The
/// row-invariant weights and constant coordinates are folded once into `const_part`.
///
/// With `products`, also the leaves' [`gkr::next_level`] while they are in registers:
/// `dst` then holds whole groups of eight rows, and `products` a quarter of its length.
fn fill_tuple(
    coords: &[Coord],
    cols: &[&[F64]],
    w: &[F192],
    beta: F192,
    dst: &mut [MaybeUninit<F192>],
    products: Option<&mut [MaybeUninit<F192>]>,
) {
    let mut const_part = beta;
    let mut terms: Vec<Term> = Vec::with_capacity(coords.len());
    for (i, c) in coords.iter().enumerate() {
        push_terms(c, w[i], &mut terms, &mut const_part);
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    )))]
    let row = |z: usize| -> F192 {
        // The α-weighted coordinate sum defers its reductions: each mixed
        // product contributes its three raw limb products (3 PMULL, no
        // reduction tail), one combined reduction per row at the end,
        // bit-identical to summing reduced `mul_base` terms.
        let mut acc = F192Unreduced::ZERO;
        for t in &terms {
            acc ^= match t {
                Term::Col(i, c) => c.mul_base_unreduced(cols[*i][z]),
                Term::Prod(i, j, c) => c.mul_base_unreduced(cols[*i][z] * cols[*j][z]),
                Term::IntIndex(c, shift) => c.mul_base_unreduced(F64((z as u64) << shift)),
                Term::Public(vals, c) => c.mul_base_unreduced(vals[z]),
            };
        }
        const_part + acc.reduce()
    };
    // Eight rows at once: each term's coefficient meets eight words in one batched
    // product, and the eight sums reduce together. Elsewhere one row at a time.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    let rows8 = |z: usize| -> [F192; 8] {
        let mut sums = MixedSums8::new();
        for t in &terms {
            let (c, k) = match t {
                Term::Col(i, c) => (c, *cols[*i][z..z + 8].as_array().unwrap()),
                Term::Prod(i, j, c) => (c, std::array::from_fn(|r| cols[*i][z + r] * cols[*j][z + r])),
                Term::IntIndex(c, shift) => (c, std::array::from_fn(|r| F64(((z + r) as u64) << shift))),
                Term::Public(vals, c) => (c, *vals[z..z + 8].as_array().unwrap()),
            };
            sums.add(*c, k);
        }
        sums.reduce().map(|s| const_part + s)
    };
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"),
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    )))]
    let rows8 = |z: usize| -> [F192; 8] { std::array::from_fn(|r| row(z + r)) };
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    )))]
    let fill = |base: usize, dst: &mut [MaybeUninit<F192>], products: Option<&mut [MaybeUninit<F192>]>| {
        let (groups, tail) = dst.as_chunks_mut::<8>();
        let tail_start = base + 8 * groups.len();
        if let Some(products) = products {
            debug_assert!(tail.is_empty() && products.len() == 2 * groups.len());
            for ((g, out), pair) in groups.iter_mut().enumerate().zip(products.as_chunks_mut::<2>().0) {
                let l = rows8(base + 8 * g);
                let [a, b, c, d] = mul4([l[0], l[2], l[4], l[6]], [l[1], l[3], l[5], l[7]]);
                pair.write_copy_of_slice(&mul2([a, c], [b, d]));
                out.write_copy_of_slice(&l);
            }
        } else {
            for (g, out) in groups.iter_mut().enumerate() {
                out.write_copy_of_slice(&rows8(base + 8 * g));
            }
        }
        for (r, slot) in tail.iter_mut().enumerate() {
            slot.write(row(tail_start + r));
        }
    };
    // One row at a time with every value in vector registers from its load to its store: the
    // terms' products summed unreduced and reduced once, and four rows' product formed from them.
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    ))]
    let constant = F192x1::new(const_part);
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    ))]
    let row = |z: usize| -> F192x1 {
        let mut acc = F192x1Unreduced::zero();
        for t in &terms {
            let (c, k) = match t {
                Term::Col(i, c) => (c, cols[*i][z]),
                Term::Prod(i, j, c) => (c, cols[*i][z] * cols[*j][z]),
                Term::IntIndex(c, shift) => (c, F64((z as u64) << shift)),
                Term::Public(vals, c) => (c, vals[z]),
            };
            acc ^= F192x1::load(c).mul_base_unreduced(k);
        }
        constant + acc.reduce()
    };
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    ))]
    let fill = |base: usize, dst: &mut [MaybeUninit<F192>], products: Option<&mut [MaybeUninit<F192>]>| {
        if let Some(products) = products {
            let (quads, tail) = dst.as_chunks_mut::<4>();
            debug_assert!(tail.is_empty() && products.len() == quads.len());
            for ((q, [o0, o1, o2, o3]), product) in quads.iter_mut().enumerate().zip(products) {
                let z = base + 4 * q;
                let (a, b, c, d) = (row(z), row(z + 1), row(z + 2), row(z + 3));
                a.store(o0);
                b.store(o1);
                c.store(o2);
                d.store(o3);
                ((a * b) * (c * d)).store(product);
            }
        } else {
            for (r, slot) in dst.iter_mut().enumerate() {
                row(base + r).store(slot);
            }
        }
    };
    if dst.len() >= PAR_THRESHOLD {
        if let Some(products) = products {
            let products = Chunks::new(products, LEAF_CHUNK / 4);
            parallel::chunks_mut(dst, LEAF_CHUNK, |ci, chunk| {
                // SAFETY: task `ci` alone takes chunk `ci` of the products, the quarter of its rows.
                fill(ci * LEAF_CHUNK, chunk, Some(unsafe { products.get(ci) }));
            });
        } else {
            parallel::chunks_mut(dst, LEAF_CHUNK, |ci, chunk| fill(ci * LEAF_CHUNK, chunk, None));
        }
    } else {
        fill(0, dst, products);
    }
}

/// One tuple's leaves over `2^kappa` rows, in a vector of their own.
pub(super) fn tuple_leaves(coords: &[Coord], kappa: usize, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<F192> {
    let mut leaves = Box::new_uninit_slice(1 << kappa);
    fill_tuple(coords, cols, w, beta, &mut leaves, None);
    // SAFETY: the fill wrote every slot.
    unsafe { leaves.assume_init() }.into_vec()
}

/// Rows per task of the producers' per-bit passes.
const PRODUCER_CHUNK: usize = 1 << 12;

/// A producer's entries' leaves, `β − π_α(e_x)`, which its bits raise to their powers.
fn producer_leaves(p: &Producer, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<F192> {
    tuple_leaves(&p.coords, p.kappa, cols, w, beta)
}

/// Build one side's leaf vector: block `b` row `z` holds `β − Σ_i w_i c_i(z)` for
/// the fingerprint weights `w = eq(α⃗, ·)`, then each producer's bit blocks, bit `i`'s
/// row `x` holding `(β − π_α(e_x))^{2^i}` where that bit of `m_x` is set and `1` where
/// it is not, followed implicitly by the identity `1` up to `2^μ`. Returns the leaves
/// and their first product level, `gkr::next_level`, formed for most blocks in the same pass.
pub fn build_leaves(
    blocks: &[Block],
    producers: &[Producer],
    lay: &Layout,
    cols: &[&[F64]],
    w: &[F192],
    beta: F192,
) -> (Vec<F192>, Vec<F192>) {
    let kappas: Vec<usize> = blocks
        .iter()
        .map(|b| b.kappa)
        .chain(producers.iter().flat_map(|p| std::iter::repeat_n(p.kappa, p.bits)))
        .collect();
    let explicit = kappas
        .iter()
        .zip(&lay.offsets)
        .map(|(&kappa, &offset)| offset + (1usize << kappa))
        .max()
        .unwrap_or(1);
    debug_assert!(explicit <= 1usize << lay.mu);
    // `stack_offsets` packs the power-of-two blocks contiguously from zero, so the
    // blocks tile `0..explicit` and every slot below is written by one of them: the
    // identity fill would be overwritten in full, and this is the largest buffer in
    // the proof. The `covered` test is what licenses skipping it, so a layout that
    // ever left a hole falls back to filling rather than leaving rows unwritten.
    // Capacity is rounded to whole four-tuples because the GKR's layer
    // pads this level to that before reading it, and growing it here would copy it.
    let covered: usize = kappas.iter().map(|&kappa| 1usize << kappa).sum();
    let mut leaves = Vec::with_capacity(explicit.next_multiple_of(4));
    let slots = &mut leaves.spare_capacity_mut()[..explicit];
    if covered != explicit {
        slots.fill(MaybeUninit::new(F192::ONE));
    }
    let n_products = explicit.div_ceil(4);
    let mut products = Vec::with_capacity(n_products.next_multiple_of(4));
    let product_slots = &mut products.spare_capacity_mut()[..n_products];
    let mut fused: Vec<Range<usize>> = Vec::with_capacity(blocks.len());
    // Every row of every block is a real row: a table's height is exactly the
    // number of rows it executed (`cpu::filler`), so no block has padding rows
    // whose tuples would have to be divided back out of the product.
    for (b, blk) in blocks.iter().enumerate() {
        let (off, len) = (lay.offsets[b], 1usize << blk.kappa);
        let dst = &mut slots[off..off + len];
        // A block of eight rows or more starts at a multiple of its size, so its
        // four-tuples are its own.
        if blk.kappa >= 3 {
            debug_assert!(off.is_multiple_of(len), "a block starts at a multiple of its size");
            let products = &mut product_slots[off / 4..(off + len) / 4];
            fill_tuple(&blk.coords, cols, w, beta, dst, Some(products));
            fused.push(off / 4..(off + len) / 4);
        } else {
            fill_tuple(&blk.coords, cols, w, beta, dst, None);
        }
    }
    let mut b = blocks.len();
    for p in producers {
        let mut q = producer_leaves(p, cols, w, beta);
        let mult = cols[p.col];
        for bit in 0..p.bits {
            let off = lay.offsets[b];
            let dst = &mut slots[off..off + (1usize << p.kappa)];
            // Bit `bit`'s leaves, then `q` squared in place for the next bit.
            parallel::chunks_mut2(dst, &mut q, PRODUCER_CHUNK, |ci, dst, q| {
                let mult = &mult[ci * PRODUCER_CHUNK..];
                for ((slot, q), m) in dst.iter_mut().zip(q.iter_mut()).zip(mult) {
                    slot.write(if (m.0 >> bit) & 1 == 1 { *q } else { F192::ONE });
                    *q = q.square();
                }
            });
            b += 1;
        }
    }
    // SAFETY: the blocks tile `0..explicit` when they cover it, and the identity fill wrote it otherwise.
    unsafe { leaves.set_len(explicit) };
    // The products no block fill formed: the small blocks', the producers' and any hole's.
    fused.sort_unstable_by_key(|r| r.start);
    let mut start = 0;
    for r in fused.into_iter().chain(std::iter::once(n_products..n_products)) {
        if start < r.start {
            let dst = &mut product_slots[start..r.start];
            let product = |i: usize| gkr::padded_product(&leaves, start + i);
            if dst.len() >= PAR_THRESHOLD {
                parallel::fill(dst, |i| MaybeUninit::new(product(i)));
            } else {
                for (i, slot) in dst.iter_mut().enumerate() {
                    slot.write(product(i));
                }
            }
        }
        start = start.max(r.end);
    }
    // SAFETY: the block fills wrote the ranges in `fused`, and the pass above every slot between them.
    unsafe { products.set_len(n_products) };
    (leaves, products)
}

/// What the producer's air sums against `eq(ζ, ·)` (§sec:lookup): its bits as `E`
/// columns, then for each bit `i` the public column `(β − π_α(e_x))^{2^i} − 1`, so that
/// bit `i`'s leaf is `1 + b_i·P'_i`. Prover-side; the verifier evaluates the public
/// half itself, its program columns' share in a deferred claim.
pub fn producer_columns(p: &Producer, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<Vec<F192>> {
    let mut q = producer_leaves(p, cols, w, beta);
    let mult = cols[p.col];
    let bits = (0..p.bits).map(|bit| {
        let mut column = Vec::with_capacity(1 << p.kappa);
        column.extend(mult.iter().map(|m| F192::from(F64((m.0 >> bit) & 1))));
        column
    });
    let mut public = Vec::with_capacity(p.bits);
    for _ in 0..p.bits {
        let mut column = Vec::with_capacity(1 << p.kappa);
        column.extend(q.iter().map(|&v| v + F192::ONE));
        public.push(column);
        parallel::for_each_mut(&mut q, |_, v| *v = v.square());
    }
    bits.chain(public).collect()
}
