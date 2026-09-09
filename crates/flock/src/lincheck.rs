// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Lincheck PIOP for **block-diagonal** R1CS over GF(2).
//!
//! Reduces the zerocheck's three evaluation claims, together with the linear constraints `a = Az`, `b = Bz`, `c = z`, to one family of committed witness slices at a fresh inner point.
//!
//! ## Matrix structure (the assumption we exploit)
//!
//! `A = I_{2^n_log} ⊗ A_0` (block-diagonal with `A_0` repeated `2^n_log`
//! times along the diagonal), and likewise for B. The circuit supplies the base matrices' linear maps without materializing them.
//!
//! With the row/col index decomposed as `(i_inner, i_outer)` with `k_log`
//! inner bits and `n_log` outer bits (`m = k_log + n_log`), the bilinear MLE
//! factors:
//!
//!   `Â(i, x)  =  Â_0(i_inner, x_inner) · eq(i_outer, x_outer)`
//!
//! So for the claim `v = â(x) = Σ_i z(i) · Â(i, x)` the outer summation
//! collapses by the eq-MLE identity:
//!
//!   `v  =  Σ_{i_inner}  Â_0(i_inner, x_inner) · ẑ(i_inner, x_outer)`
//!
//! This is a sum over only `2^k_log` terms, with `ẑ(·, x_outer)` being the
//! partial fold of `z` at the outer half of the claim point.
//!
//! ## Protocol shape (circuit R1CS: C = I, one shared claim point)
//!
//! The zerocheck leaves `â`, `b̂` and `ĉ` at the **same** point `(z, ρ-values)`,
//! so lincheck folds `z` **once**, at that shared point. For R1CS coming from
//! circuits `C = I`, so the c-claim is a direct `z`-claim and enters the same
//! batch as A and B rather than travelling to the PCS on its own.
//!
//! The prover partially folds the witness at the shared outer point and forms the column marginal of `A + α B + α² I`, with a constant-wire pin at `α³`. A product sumcheck reduces its inner product to the final `2^k_skip` witness slices, which the prover sends after the rounds. The verifier reconstructs the terminal marginal through the circuit's bilinear form; ring switching binds the slices to the commitment.
//!
//! ## Quirky (univariate-skip) claim points
//!
//! To compose with the **zerocheck's univariate skip** for the first `k_skip`
//! variables, claim points use the [`QuirkyPoint`] representation:
//!
//!   `x = (z_skip ∈ F_{2^192},  x_inner_rest ∈ F_{2^192}^{k_log − k_skip},  x_outer ∈ F_{2^192}^{n_log})`
//!
//! - `z_skip` is the univariate-skip challenge; it represents all `k_skip`
//!   skip variables collapsed via the polynomial extension with Lagrange
//!   basis on `φ_8(0), …, φ_8(2^{k_skip} − 1)`.
//! - The remaining `k_log − k_skip` inner coords plus the `n_log` outer
//!   coords are standard multilinear.
//!
//! When evaluating the bilinear matrix MLE at a quirky claim point, the
//! eq factor for the inner row index becomes the **outer product of**:
//! `L_{i_skip}(z_skip) · eq(x_inner_rest, i_inner_rest)`, where `L_*` are
//! Lagrange weights at `z_skip` for the `k_skip` skip dims (see
//! [`build_quirky_eq_table`]).
//!
//! The prover's partial fold `ẑ(·, x_outer)` is unchanged: it only depends
//! on `x_outer` (still pure multilinear). The verifier-side eq tables and
//! the final-sample reduction are the only changes.
//!
//! ## Conventions
//!
//! - **Point ordering inside `QuirkyPoint`.** `x_inner_rest[0..k_log − k_skip]`
//!   bind to inner variables `i_inner_rest[0..k_log − k_skip]`. `x_outer[0..n_log]`
//!   to outer vars.
//! - **Eq table layout.** `eq_table[i]` where `i = Σ b_j · 2^j` is
//!   `Π_j eq(point[j], b_j) = Π_j (1 + point[j] + b_j)`.
//! - **`z_packed` byte layout (specific to lincheck, enabling column-scan
//!   lookup tables without an explicit transpose).** Writing `i_outer = 8·byte_idx + r`
//!   with `r ∈ {0,..,7}` and `byte_idx ∈ {0,..,n_outer/8 − 1}`, the bit
//!   `z[i_inner, i_outer]` lives at:
//!     - **byte position** `byte_idx · k + i_inner`,
//!     - **bit-within-byte** `r`.
//!
//!   Equivalently: `z_packed` is organized in `n_outer/8` *stripes* of `k`
//!   contiguous bytes each. Stripe `byte_idx` covers all `i_inner ∈ {0,..,k}`
//!   for the same outer batch `i_outer ∈ {8·byte_idx, …, 8·byte_idx + 7}`.
//!   Each byte holds 8 outer bits for one i_inner.
//!
//!   In bit-position terms, the bit-index decomposes as:
//!   ```text
//!   LSB:  3 bits = r           (= low 3 bits of i_outer, = bit-within-byte)
//!         k_log bits = i_inner
//!   MSB:  (n_log − 3) bits = byte_idx (= upper bits of i_outer)
//!   ```
//!
//!   This layout makes the partial-fold column scan sequential: for each
//!   `byte_idx`, all `k` per-i_inner bytes are at consecutive byte positions,
//!   so we build a 256-entry sum table for the 8 outer values once per
//!   `byte_idx` and apply it across all `i_inner` with one lookup + one XOR
//!   per byte.

use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use pcs::ring_switch::inner_product_ext;
use primitives::field::F192;
use primitives::multilinear::{eq_eval, eq_table as build_eq, lagrange_weights_naive};
#[cfg(test)]
use zk_alloc::ArenaVec;

// ---------------------------------------------------------------------------
// LincheckCircuit: the per-block linear structure lincheck consumes
// ---------------------------------------------------------------------------
//
// Lincheck's hot path computes a single length-`k = 2^k_log` vector
//
//   `comb_vec[c] = ξ_A(c) + α · ξ_B(c)`
//
// where `ξ_M(c) = Σ_r eq_inner[r] · M[r, c]` is the eq-weighted column
// marginal of base matrix `M ∈ {A_0, B_0}`, at cost ∝ NNZ.
//
// `LincheckCircuit` is the seam: the prover and verifier take
// `&dyn LincheckCircuit` instead of a pair of matrices. The one live impl is
// `hash::WalkLincheckCircuit`, which walks the circuit in both directions
// (forwards for the verifier's `bilinear_form`, backwards for the prover's
// marginal) and never touches a matrix entry. See doc/leanvm, Annex C
// "Evaluating the matrices".

/// Per-block linear structure consumed by lincheck. Implementations produce
/// the α-batched column marginal `comb_vec[c] = ξ_A(c) + α · ξ_B(c)` either
/// by walking the circuit or another representation of its linear maps.
pub trait LincheckCircuit: Sync {
    /// Number of columns in the per-block matrices A_0, B_0 (= k = 2^k_log).
    fn n_cols(&self) -> usize;

    /// Compute `comb_vec[c] = (eq^T · A_0)[c] + α · (eq^T · B_0)[c]` over
    /// `c ∈ [0, n_cols())`. `eq_inner.len() == n_cols()`.
    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192>;

    /// Column index of the constant-one wire. Lincheck folds one extra
    /// `β = α³`-term into the comb at this column so the sumcheck also proves
    /// that the committed constant column is the all-ones vector (whose MLE is
    /// the constant `1`), closing the all-zero witness soundness gap. This
    /// REQUIRES the witness to set that wire to `1` in *every* batched instance,
    /// padding included. The term rides a power of `α`, so it costs no
    /// transcript message.
    fn const_pin_col(&self) -> usize;

    /// Optional verifier-side fast path (doc/leanvm, Annex C): the
    /// α-batched bilinear form
    ///
    ///   `(uᵀ A_0 w) + α·(uᵀ B_0 w)`
    ///
    /// for arbitrary row weights `u` and column weights `w` (length
    /// `n_cols()` each), WITHOUT materializing the length-k column marginal.
    /// [`verify`] only ever consumes the marginal through one inner product
    /// against a column-weight vector, so an implementation that can walk its
    /// circuit (O(circuit) field ops, see `hash::bilinear_walk`) answers
    /// here and never pays the ∝ NNZ marginal. Default `None`: the verifier
    /// falls back to `fold_alpha_batched`.
    fn bilinear_form(&self, _alpha: F192, _u: &[F192], _w: &[F192]) -> Option<F192> {
        None
    }
}

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// A "quirky" claim point: one univariate-skip coord (`z_skip`) representing
/// the first `k_skip` variables via the polynomial extension with the φ_8 basis,
/// followed by multilinear coords for the rest of inner and for outer.
///
/// Total "elements" = `1 + (k_log − k_skip) + n_log`, which is the shape the
/// zerocheck's extract_c output uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuirkyPoint {
    /// Univariate-skip challenge ∈ F₁₉₂ (tower). Binds all `k_skip` skip variables.
    pub z_skip: F192,
    /// Multilinear coords for the inner dims *after* the skip block. Length
    /// `k_log − k_skip`.
    pub x_inner_rest: Vec<F192>,
    /// Multilinear coords for the outer dims. Length `n_log = m − k_log`.
    pub x_outer: Vec<F192>,
}

// Lincheck prover message: a partial product-sumcheck that proves the two
// scalar consistency equations against `z` partially folded at the shared
// outer half `x_ab.x_outer`, without sending the full length-`2^k_log` vector.
// (No LincheckProof struct: every scalar rides the shared transcript stream:
// the high multilinear rounds' messages, then `z_partial`, the post-sumcheck
// length-2^k_skip residual, which is the output claim itself.)

/// Lincheck output: the `2^k_skip` bit-slice claims on `z` at the inner point
/// `r_inner_rest` combined with `x_ab.x_outer` (publicly known to the caller).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LincheckClaim {
    /// The A/B batching challenge (sampled first).
    pub alpha: F192,
    /// The constant-pin challenge `alpha³`; zero when the circuit has no pin
    /// column.
    pub beta: F192,
    /// The sumcheck round challenges, in round order (MSB-first binding).
    pub r_rounds: Vec<F192>,
    /// Multilinear post-vector random sample, length `k_log − k_skip`.
    pub r_inner_rest: Vec<F192>,
    /// The transmitted post-sumcheck vector: the 64 bit-slice values of `z` at
    /// `(r_inner_rest, x_ab.x_outer)`, pinned by the terminal identity. This IS
    /// the AB claim, and it IS its ring-switch `s_hat_v`, so the opening
    /// verifier reuses it rather than receiving the same values a second time.
    pub s_hat_v: Vec<F192>,
}

/// Reasons the verifier may reject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// One of the input quirky points has wrong `x_inner_rest` length
    /// (expected `k_log − k_skip`).
    BadInnerRestLength {
        which: &'static str,
        expected: usize,
        got: usize,
    },
    /// One of the input quirky points has wrong `x_outer` length
    /// (expected `n_log = m − k_log`).
    BadOuterLength {
        which: &'static str,
        expected: usize,
        got: usize,
    },
    /// The circuit's column count isn't `2^k_log`.
    BadNCols { expected: usize, got: usize },
    /// `k_skip` exceeds `k_log` (the matrix inner dimension).
    KSkipExceedsKLog { k_skip: usize, k_log: usize },
    /// The scalar consistency check failed for one of (A, B, C).
    /// Detected: `Σ_{i_inner} M̂_0_quirky(z_skip, x_inner_rest, i_inner) · z_x_vec[i_inner] ≠ v`.
    ConsistencyFailed { which: &'static str },
    /// The proof stream ran out while reading a message.
    Transcript(fiat_shamir::transcript::Error),
}

// ---------------------------------------------------------------------------
// Core kernels
// ---------------------------------------------------------------------------

/// Partial fold of `z` at the outer half of a claim point, single-matrix,
/// **scalar reference**. Uses the lincheck `z_packed` stripe layout
/// (see module docs).
///
///   `output[i_inner] = Σ_{i_outer ∈ {0,1}^n_log}  z[i_inner, i_outer] · eq_outer[i_outer]`
///
/// Equivalently, `output[i_inner] = ẑ(i_inner_as_F192, x_outer)` for boolean
/// `i_inner`. Used as the cross-check oracle for the production
/// `partial_fold_packed_z_triple`.
#[cfg(test)]
pub fn partial_fold_packed_z(z_packed: &[u8], m: usize, k_log: usize, eq_outer: &[F192]) -> Vec<F192> {
    let n_log = m - k_log;
    let k = 1usize << k_log;
    let n_outer = 1usize << n_log;
    assert_eq!(z_packed.len(), (1usize << m) / 8);
    assert_eq!(eq_outer.len(), n_outer);
    assert!(n_log >= 3, "need n_outer ≥ 8 for byte stripes");
    let n_stripes = n_outer / 8;

    let mut out = vec![F192::ZERO; k];
    for byte_idx in 0..n_stripes {
        let stripe = &z_packed[byte_idx * k..(byte_idx + 1) * k];
        for (i_inner, &byte) in stripe.iter().enumerate() {
            if byte == 0 {
                continue;
            }
            let mut bits = byte;
            while bits != 0 {
                let r = bits.trailing_zeros() as usize;
                let i_outer = 8 * byte_idx + r;
                out[i_inner] += eq_outer[i_outer];
                bits &= bits - 1;
            }
        }
    }
    out
}

/// Padding-aware variant of `partial_fold_packed_z_fast`. Skips rows
/// `i_inner ∈ [useful_bits, k)`, since those rows hold zero in every block of an
/// honestly padded witness, so the fold over the outer dim is zero. Output
/// is byte-identical to the dense path on such witnesses.
fn partial_fold_packed_z_fast_padded(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    let n_log = m - k_log;
    let k = 1usize << k_log;
    let n_outer = 1usize << n_log;
    assert_eq!(z_packed.len(), (1usize << m) / 8);
    assert_eq!(eq_outer.len(), n_outer);
    assert!(n_log >= 3, "need n_outer ≥ 8 for byte stripes");
    assert!(useful_bits <= k);
    let n_stripes = n_outer / 8;

    let stripes_per_chunk = (n_stripes / 256).max(1);
    let bytes_per_chunk = stripes_per_chunk * k;

    // Keep one length-k accumulator per worker rather than per chunk.
    let n_chunks = z_packed.len().div_ceil(bytes_per_chunk);
    parallel::fold_reduce(
        n_chunks,
        || vec![F192::ZERO; k],
        |acc, chunk_idx| {
            let lo = chunk_idx * bytes_per_chunk;
            let chunk_bytes = &z_packed[lo..(lo + bytes_per_chunk).min(z_packed.len())];
            let stripe_start = chunk_idx * stripes_per_chunk;
            let mut table = vec![F192::ZERO; 256];
            for (rel_stripe, stripe) in chunk_bytes.chunks(k).enumerate() {
                let byte_idx = stripe_start + rel_stripe;
                build_sum_table(&eq_outer[8 * byte_idx..8 * byte_idx + 8], &mut table);
                for (i_inner, &z_byte) in stripe[..useful_bits].iter().enumerate() {
                    acc[i_inner] += table[z_byte as usize];
                }
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b.iter()) {
                *x += *y;
            }
            a
        },
    )
}

/// Stripes swept per accumulator touch in the NEON tiled partial fold.
/// Larger values re-stream the accumulator less often but grow the tables that must stay in L1.
const NEON_TILE_T: usize = 8;

/// x86-64 twin of the tiled gather kernel below.
///
/// `VPTERNLOGQ` is the exact counterpart of AArch64's `EOR3`: an arbitrary
/// three-input bitwise function in one instruction, so immediate `0x96`
/// (`a ^ b ^ c`) folds a paired-stripe accumulate the same way. Only the
/// `c0`/`c1` limbs ride in the vector: `c2` is scalar and takes two XORs.
///
/// # Safety
/// - `tile_bytes_ptr` must point to at least `TILE_T * k` bytes, with `bs + 8`
///   readable in every stripe row (guaranteed by `bs + BLOCK_K <= k`).
/// - `tables_ptr` must point to at least `TILE_T * 256` `F192`.
/// - `out_ptr` must point to at least 8 writable `F192`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl"))]
#[inline(never)]
#[allow(unsafe_op_in_unsafe_fn)]
unsafe fn process_block_avx512_single(
    tile_bytes_ptr: *const u8,
    k: usize,
    bs: usize,
    tables_ptr: *const F192,
    out_ptr: *mut F192,
) {
    use std::arch::x86_64::*;
    const TILE_T: usize = NEON_TILE_T;
    // `F192` is `#[repr(C)]` with `c0, c1, c2`, so a 128-bit load at `&c0`
    // covers exactly the `(c0, c1)` pair.
    const XOR3: i32 = 0x96;

    let mut acc01 = [_mm_setzero_si128(); 8];
    let mut acc2 = [0u64; 8];
    for i in 0..8 {
        let out = &*out_ptr.add(i);
        acc01[i] = _mm_loadu_si128((&out.c0 as *const u64).cast());
        acc2[i] = out.c2;
    }

    // One unaligned 8-byte load per stripe replaces eight LDRB-equivalents,
    // and stripes are swept in pairs so each vector accumulator folds both
    // table entries with a single VPTERNLOGQ.
    let mut t = 0;
    while t + 1 < TILE_T {
        let ta0 = tables_ptr.add(t * 256);
        let ta1 = tables_ptr.add((t + 1) * 256);
        let w0 = (tile_bytes_ptr.add(t * k + bs) as *const u64).read_unaligned();
        let w1 = (tile_bytes_ptr.add((t + 1) * k + bs) as *const u64).read_unaligned();
        for i in 0..8 {
            let e0 = &*ta0.add(((w0 >> (8 * i)) & 0xff) as usize);
            let e1 = &*ta1.add(((w1 >> (8 * i)) & 0xff) as usize);
            let v0 = _mm_loadu_si128((&e0.c0 as *const u64).cast());
            let v1 = _mm_loadu_si128((&e1.c0 as *const u64).cast());
            acc01[i] = _mm_ternarylogic_epi64::<XOR3>(acc01[i], v0, v1);
            acc2[i] ^= e0.c2 ^ e1.c2;
        }
        t += 2;
    }
    if t < TILE_T {
        let ta = tables_ptr.add(t * 256);
        let w = (tile_bytes_ptr.add(t * k + bs) as *const u64).read_unaligned();
        for i in 0..8 {
            let entry = &*ta.add(((w >> (8 * i)) & 0xff) as usize);
            let v = _mm_loadu_si128((&entry.c0 as *const u64).cast());
            acc01[i] = _mm_xor_si128(acc01[i], v);
            acc2[i] ^= entry.c2;
        }
    }

    for i in 0..8 {
        let out = &mut *out_ptr.add(i);
        _mm_storeu_si128((&mut out.c0 as *mut u64).cast(), acc01[i]);
        out.c2 = acc2[i];
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl"))]
use self::process_block_avx512_single as process_block_single;
/// The two architectures' inner kernels are interchangeable at the call site.
#[cfg(target_arch = "aarch64")]
use self::process_block_neon_single as process_block_single;

/// Single-matrix NEON inner kernel: sweep TILE_T=8 stripes of a stripe-tile
/// for one BLOCK_K=8 block of i_inner positions, keeping all 8 accumulators
/// in NEON Q-registers.
///
/// # Safety
/// - `tile_bytes_ptr` must point to at least `TILE_T * k` bytes.
/// - `tables_ptr` must point to at least `TILE_T * 256` F192 entries.
/// - `out_ptr` must point to at least 8 F192 entries of mutable storage.
#[cfg(target_arch = "aarch64")]
#[inline(never)]
#[allow(unsafe_op_in_unsafe_fn)]
unsafe fn process_block_neon_single(
    tile_bytes_ptr: *const u8,
    k: usize,
    bs: usize,
    tables_ptr: *const F192,
    out_ptr: *mut F192,
) {
    use primitives::field::neon::xor3_u64;
    use std::arch::aarch64::*;
    const TILE_T: usize = NEON_TILE_T;

    let mut acc01 = [vdupq_n_u64(0); 8];
    let mut acc2 = [0u64; 8];
    for i in 0..8 {
        let out = &*out_ptr.add(i);
        acc01[i] = vld1q_u64(&out.c0);
        acc2[i] = out.c2;
    }

    // The 8 z index bytes of a stripe are consecutive, so fetch them with one
    // unaligned 8-byte scalar load and shift them out of the register rather
    // than with eight LDRBs: the gather already issues a table load per index,
    // and a second load per index would nearly double this kernel's load-port
    // pressure for data that is already in a register.
    //
    // Stripes are swept in pairs so each vector accumulator folds both table
    // lookups with one EOR3, halving the accumulator updates and the serial
    // dependency chain through each of the 8 live accumulators. The `c2`
    // limbs are scalar, so they just take two XORs.
    let mut t = 0;
    while t + 1 < TILE_T {
        let ta0 = tables_ptr.add(t * 256);
        let ta1 = tables_ptr.add((t + 1) * 256);
        let w0 = (tile_bytes_ptr.add(t * k + bs) as *const u64).read_unaligned();
        let w1 = (tile_bytes_ptr.add((t + 1) * k + bs) as *const u64).read_unaligned();
        for i in 0..8 {
            let e0 = &*ta0.add(((w0 >> (8 * i)) & 0xff) as usize);
            let e1 = &*ta1.add(((w1 >> (8 * i)) & 0xff) as usize);
            acc01[i] = xor3_u64(acc01[i], vld1q_u64(&e0.c0), vld1q_u64(&e1.c0));
            acc2[i] ^= e0.c2 ^ e1.c2;
        }
        t += 2;
    }
    if t < TILE_T {
        let ta = tables_ptr.add(t * 256);
        let w = (tile_bytes_ptr.add(t * k + bs) as *const u64).read_unaligned();
        for i in 0..8 {
            let entry = &*ta.add(((w >> (8 * i)) & 0xff) as usize);
            acc01[i] = veorq_u64(acc01[i], vld1q_u64(&entry.c0));
            acc2[i] ^= entry.c2;
        }
    }

    for i in 0..8 {
        let out = &mut *out_ptr.add(i);
        vst1q_u64(&mut out.c0, acc01[i]);
        out.c2 = acc2[i];
    }
}

/// Shared shape validation for the two tiled NEON folds. Returns
/// `(k, n_tiles, useful)`, where `useful` is `useful_bits` rounded up to a
/// `BLOCK_K` multiple: padded rows fold to zero, and a boundary block's padding
/// bytes are 0 ⇒ `table[0] = 0` ⇒ they contribute nothing.
#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl")
))]
fn neon_fold_params(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> (usize, usize, usize) {
    const TILE_T: usize = NEON_TILE_T;
    const BLOCK_K: usize = 8;

    let n_log = m - k_log;
    let k = 1usize << k_log;
    let n_outer = 1usize << n_log;
    assert_eq!(z_packed.len(), (1usize << m) / 8);
    assert_eq!(eq_outer.len(), n_outer);
    assert!(
        n_log >= 3 + TILE_T.trailing_zeros() as usize,
        "need n_outer ≥ 8·TILE_T stripes"
    );
    assert!(k_log >= 3, "need k ≥ 8");
    assert!(useful_bits <= k);
    let n_stripes = n_outer / 8;
    assert_eq!(n_stripes % TILE_T, 0);
    assert_eq!(k % BLOCK_K, 0);
    let useful = (useful_bits.div_ceil(BLOCK_K) * BLOCK_K).min(k);
    (k, n_stripes / TILE_T, useful)
}

/// **i_inner-partitioned** NEON partial fold: parallelizes over the
/// **output** (`i_inner`) instead of over z stripes.
///
/// Workers own disjoint output slices, keeping one shared length-`k` accumulator and avoiding a final reduction. Each worker rebuilds the per-tile sum tables for its slice.
#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl")
))]
fn partial_fold_packed_z_iblock_padded(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    const TILE_T: usize = NEON_TILE_T;
    const BLOCK_K: usize = 8;

    let (k, n_tiles, useful) = neon_fold_params(z_packed, m, k_log, useful_bits, eq_outer);

    // Rows [useful, k) stay zero from the vec init.
    let mut out = vec![F192::ZERO; k];
    if useful == 0 {
        return out;
    }

    // Partition the useful i_inner range across workers. Each chunk independently
    // rebuilds the per-tile sum tables, so chunk count drives redundant table
    // work that does NOT scale with cores and dominates the residual at the
    // protocol's m. One chunk per worker minimizes that
    // redundancy; the pool's claim counter then rebalances a straggler (an
    // efficiency core, say) without needing extra chunks to steal from. Each
    // chunk is a BLOCK_K multiple.
    let p = parallel::num_threads();
    let i_chunk = (useful / p).max(BLOCK_K).next_multiple_of(BLOCK_K);

    parallel::chunks_mut(&mut out[..useful], i_chunk, |ci, out_slice| {
        let i_base = ci * i_chunk;
        let n_block = out_slice.len() / BLOCK_K;
        // Per-tile tables stay L1-resident.
        let mut tables = vec![F192::ZERO; TILE_T * 256];
        for tile in 0..n_tiles {
            let stripe_base = tile * TILE_T;
            for t in 0..TILE_T {
                let eq_off = 8 * (stripe_base + t);
                build_sum_table(&eq_outer[eq_off..eq_off + 8], &mut tables[t * 256..(t + 1) * 256]);
            }
            let tables_ptr = tables.as_ptr();
            // Base of this (tile, i_base): process_block reads
            // z_base[t·k + bs] = z[(stripe_base+t)·k + i_base + bs].
            let z_base = unsafe { z_packed.as_ptr().add(stripe_base * k + i_base) };
            for b in 0..n_block {
                let i = b * BLOCK_K;
                unsafe {
                    process_block_single(z_base, k, i, tables_ptr, out_slice.as_mut_ptr().add(i));
                }
            }
        }
    });
    out
}

/// Outer(tile)-partitioned sibling of [`partial_fold_packed_z_iblock_padded`]
/// with the same result, parallelized to remove the redundant per-worker sum-table
/// rebuilds that cap iblock's multicore scaling. **This is the default fold**
/// (`partial_fold_packed_z_best`).
///
/// iblock partitions the length-k **output** across workers, so every worker
/// rebuilds **all** `n_stripes` tile tables: table work is done `p`× and does not
/// shrink with cores, taking a large share of the multi-threaded wall. Here we
/// partition the **tiles** (outer/stripe dim): each worker owns a contiguous tile
/// band, builds each of its tile tables exactly **once**, folds them into a
/// private length-k partial, and the `p` partials are XOR-reduced at the end. The
/// partial is the full length-k output, while the register-tiled inner kernel keeps its accumulators in NEON registers. This trades reduction traffic for eliminating redundant table construction.
///
/// # Safety / preconditions: identical to the iblock kernel.
#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl")
))]
fn partial_fold_packed_z_oblock_padded(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    const TILE_T: usize = NEON_TILE_T;
    const BLOCK_K: usize = 8;

    let (k, n_tiles, useful) = neon_fold_params(z_packed, m, k_log, useful_bits, eq_outer);

    // Columns [useful, k) stay zero from the partial init.
    if useful == 0 {
        return vec![F192::ZERO; k];
    }

    // One private length-k partial per worker; workers own contiguous tile bands,
    // so each tile's sum-tables are built exactly once (not once per worker).
    let p = parallel::num_threads();
    let tiles_per_worker = n_tiles.div_ceil(p);
    let n_workers = n_tiles.div_ceil(tiles_per_worker); // ≤ p, every band non-empty

    let mut partials = vec![F192::ZERO; n_workers * k];
    parallel::chunks_mut(&mut partials, k, |w, partial| {
        let tile_lo = w * tiles_per_worker;
        let tile_hi = ((w + 1) * tiles_per_worker).min(n_tiles);
        // Build each tile's L1-resident tables once.
        let mut tables = vec![F192::ZERO; TILE_T * 256];
        for tile in tile_lo..tile_hi {
            let stripe_base = tile * TILE_T;
            for t in 0..TILE_T {
                let eq_off = 8 * (stripe_base + t);
                build_sum_table(&eq_outer[eq_off..eq_off + 8], &mut tables[t * 256..(t + 1) * 256]);
            }
            let tables_ptr = tables.as_ptr();
            let z_base = unsafe { z_packed.as_ptr().add(stripe_base * k) };
            let mut bs = 0usize;
            while bs < useful {
                unsafe {
                    process_block_single(z_base, k, bs, tables_ptr, partial.as_mut_ptr().add(bs));
                }
                bs += BLOCK_K;
            }
        }
    });

    // XOR-reduce the per-worker partials: parallel over columns, sequential over
    // workers so each partial is streamed once.
    let (first, rest) = partials.split_at(k);
    let mut out = first.to_vec();
    let col_chunk = parallel::recommended_chunk_size(k);
    for chunk in rest.chunks(k) {
        parallel::chunks_mut_zip(&mut out, chunk, col_chunk, |_, o, s| {
            for (o_i, s_i) in o.iter_mut().zip(s) {
                *o_i += *s_i;
            }
        });
    }
    out
}

/// Dispatch helper: pick the fastest single-matrix partial fold available
/// for the given (m, k_log). Threads `useful_bits` through so the kernel
/// can skip blocks past the useful region of each block (byte-identical to
/// the dense path on honestly-padded witnesses).
fn partial_fold_packed_z_best(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    useful_bits: usize,
    eq_outer: &[F192],
) -> Vec<F192> {
    if n_log_ok_for_tile(m, k_log, NEON_TILE_T) {
        #[cfg(any(
            target_arch = "aarch64",
            all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl")
        ))]
        {
            // `oblock` avoids per-worker table construction but adds private partials and a reduction, so use it only above the tuned crossover.
            let n_log = m - k_log;
            if n_log >= OBLOCK_MIN_N_LOG {
                return partial_fold_packed_z_oblock_padded(z_packed, m, k_log, useful_bits, eq_outer);
            }
            partial_fold_packed_z_iblock_padded(z_packed, m, k_log, useful_bits, eq_outer)
        }
        #[cfg(not(any(
            target_arch = "aarch64",
            all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl")
        )))]
        {
            partial_fold_packed_z_fast_padded(z_packed, m, k_log, useful_bits, eq_outer)
        }
    } else {
        partial_fold_packed_z_fast_padded(z_packed, m, k_log, useful_bits, eq_outer)
    }
}

/// Outer-dimension threshold (`n_log = m − k_log`) at/above which the
/// outer(tile)-partitioned fold beats the i_inner-partitioned one. See
/// [`partial_fold_packed_z_best`] for the crossover calibration.
#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl")
))]
const OBLOCK_MIN_N_LOG: usize = 16;

/// Quick test for "can we use the tiled fast path?". Tile uses `TILE_T`
/// stripes; we need `n_stripes` divisible by TILE_T and enough outer dim.
fn n_log_ok_for_tile(m: usize, k_log: usize, tile_t: usize) -> bool {
    let n_log = m - k_log;
    if n_log < 3 + (tile_t.trailing_zeros() as usize) {
        return false;
    }
    let n_stripes = 1usize << (n_log - 3);
    n_stripes.is_multiple_of(tile_t)
}

/// Build a 256-entry sum table over 8 F192 values:
///   `table[b] = Σ_{r: bit r of b is set}  eq8[r]`
///
/// Doubling construction (255 XORs): for each new bit position `i ∈ 0..8`,
/// extend the table by XORing `eq8[i]` into each existing entry. This
/// avoids the naive 8·256 = 2048 operations.
#[inline]
fn build_sum_table(eq8: &[F192], table: &mut [F192]) {
    debug_assert_eq!(eq8.len(), 8);
    debug_assert_eq!(table.len(), 256);
    table[0] = F192::ZERO;
    for i in 0..8 {
        let e = eq8[i];
        let len = 1usize << i;
        for j in 0..len {
            table[len + j] = table[j] + e;
        }
    }
}

/// Pack a logical Boolean witness vector into the lincheck `z_packed`
/// stripe layout. The input `z_logical` is indexed linearly with
/// `z_logical[i_inner + i_outer · k]` = z's value at `(i_inner, i_outer)`.
/// The output `z_packed[byte_idx · k + i_inner]` holds 8 outer bits
/// `z[i_inner, 8·byte_idx + r]` for `r ∈ 0..8`, with bit `r` within the byte.
///
/// See the module-level docs for the full bit-position decomposition.
#[cfg(test)]
pub fn pack_z_lincheck(z_logical: &[bool], m: usize, k_log: usize) -> ArenaVec<u8> {
    let k = 1usize << k_log;
    let n_total = 1usize << m;
    assert_eq!(z_logical.len(), n_total);
    let n_outer = n_total / k;
    assert_eq!(n_outer % 8, 0, "need n_outer ≥ 8 for byte stripes");
    let n_stripes = n_outer / 8;

    let mut z_packed = zk_alloc::alloc_uninit(n_total / 8);
    for byte_idx in 0..n_stripes {
        for i_inner in 0..k {
            let mut byte = 0u8;
            for r in 0..8 {
                let i_outer = 8 * byte_idx + r;
                let logical_idx = i_inner + i_outer * k;
                if z_logical[logical_idx] {
                    byte |= 1u8 << r;
                }
            }
            z_packed[byte_idx * k + i_inner].write(byte);
        }
    }
    // SAFETY: the nested loops write every output byte exactly once.
    unsafe { zk_alloc::assume_init(z_packed) }
}

/// Same output as `pack_z_lincheck`, but reads bits from the bit-packed `u64`
/// witness: logical bit `i` is bit `i % 64` of `z_packed_words[i / 64]`.
#[cfg(test)]
pub fn pack_z_lincheck_from_packed(z_packed_words: &[u64], m: usize, k_log: usize) -> ArenaVec<u8> {
    let k = 1usize << k_log;
    let n_total = 1usize << m;
    assert_eq!(z_packed_words.len(), n_total / 64);
    let n_outer = n_total / k;
    assert_eq!(n_outer % 8, 0, "need n_outer ≥ 8 for byte stripes");

    let mut z_packed = zk_alloc::alloc_uninit(n_total / 8);
    // Each stripe (byte_idx) writes a disjoint k-byte chunk, so process them in
    // parallel. Inside one stripe, k independent output bytes.
    parallel::chunks_mut(&mut z_packed, k, |byte_idx, chunk| {
        for i_inner in 0..k {
            let mut byte = 0u8;
            for r in 0..8 {
                let i_outer = 8 * byte_idx + r;
                let logical_idx = i_inner + i_outer * k;
                if (z_packed_words[logical_idx / 64] >> (logical_idx % 64)) & 1 == 1 {
                    byte |= 1u8 << r;
                }
            }
            chunk[i_inner].write(byte);
        }
    });
    // SAFETY: every parallel chunk writes each of its output bytes exactly once.
    unsafe { zk_alloc::assume_init(z_packed) }
}

/// Build the **quirky eq table** for a claim point on the inner half:
///
///   `out[i_skip + i_inner_rest · 2^k_skip]
///     = L_{i_skip}(z_skip)  ·  eq(x_inner_rest, i_inner_rest)`
///
/// where `L_{i_skip}` are Lagrange weights at `z_skip` for the φ_8 basis
/// over `{0, …, 2^k_skip − 1}`. Length: `2^k_log`.
///
/// Encoding: the skip dim occupies the **low** `k_skip` bits of the table
/// index (matches z_packed's stripe layout / zerocheck's LSB-first
/// univariate-skip variable ordering). The `k_log − k_skip` multilinear
/// inner-rest dims occupy the next bits.
pub fn build_quirky_eq_table(z_skip: F192, x_inner_rest: &[F192], k_skip: usize) -> Vec<F192> {
    let lambda_skip = lagrange_weights_naive(k_skip, z_skip);
    let eq_rest = build_eq(x_inner_rest);
    // Layout: index = i_skip + i_inner_rest · 2^k_skip  ⇒  i_skip is low bits.
    outer_product(&eq_rest, &lambda_skip)
}

/// `out[i_lo + i_hi · lo.len()] = lo[i_lo] · hi[i_hi]`: the `lo` dims vary
/// fastest, so `lo` occupies the low bits of the output index.
fn outer_product(hi: &[F192], lo: &[F192]) -> Vec<F192> {
    let mut out = Vec::with_capacity(hi.len() * lo.len());
    for &h in hi {
        for &l in lo {
            out.push(l * h);
        }
    }
    out
}

/// Length above which the inner product / element-wise kernels fan out to the
/// pool. Below it, sequential beats dispatch overhead.
const SUMCHECK_PAR_THRESHOLD: usize = 1usize << 12;

/// One round of product-sumcheck on `(c, z)`: compute `(q(1), q(∞))` =
/// `(Σ c_hi·z_hi, Σ (c_hi+c_lo)·(z_hi+z_lo))` over the top-bit split. The
/// `len()` of `c` and `z` is even; `half = len/2`.
fn sumcheck_round_eval_par(c: &[F192], z: &[F192]) -> (F192, F192) {
    let half = c.len() / 2;
    debug_assert_eq!(z.len(), c.len());
    let (clo, chi) = c.split_at(half);
    let (zlo, zhi) = z.split_at(half);
    if half < SUMCHECK_PAR_THRESHOLD {
        let mut e1 = F192::ZERO;
        let mut einf = F192::ZERO;
        for i in 0..half {
            e1 += chi[i] * zhi[i];
            einf += (chi[i] + clo[i]) * (zhi[i] + zlo[i]);
        }
        return (e1, einf);
    }
    parallel::map_reduce(
        half,
        || (F192::ZERO, F192::ZERO),
        |i| {
            let e1_i = chi[i] * zhi[i];
            let einf_i = (chi[i] + clo[i]) * (zhi[i] + zlo[i]);
            (e1_i, einf_i)
        },
        |a, b| (a.0 + b.0, a.1 + b.1),
    )
}

/// Bind the top remaining variable of `v` at challenge `r`: `v[i] ← v[i] +
/// r·(v[i+half] + v[i])` for `i ∈ [0, half)`, then truncate to `half`. In-place.
fn sumcheck_bind_top_in_place_par(v: &mut Vec<F192>, r: F192) {
    let half = v.len() / 2;
    if half < SUMCHECK_PAR_THRESHOLD {
        for i in 0..half {
            v[i] = v[i] + r * (v[i + half] + v[i]);
        }
    } else {
        let (lo, hi) = v.split_at_mut(half);
        let hi = &hi[..half];
        let chunk = parallel::recommended_chunk_size(half);
        parallel::chunks_mut_zip(lo, hi, chunk, |_, lo_c, hi_c| {
            for (lo_i, &hi_i) in lo_c.iter_mut().zip(hi_c) {
                *lo_i = *lo_i + r * (hi_i + *lo_i);
            }
        });
    }
    v.truncate(half);
}

/// **Fused fold + next-round evaluation.** Binds the top variable of *both*
/// `comb` and `z` at `r` (in place, each length halves) AND returns the next
/// product-sumcheck round's message `(q(1), q(∞))` over the just-bound tables,
/// all in a single pass over the data.
///
/// Why it fuses: round `t`'s message must be sent before `r_t` is sampled, so
/// eval(t) and bind(t) can't share a pass. But binding at `r_t` produces
/// exactly the table eval(t+1) reads, and `r_t` is known by then. The bound
/// values `new[i]` and `new[i+half2]` are precisely the `lo`/`hi` halves the
/// next round's eval pairs up, so we form each product the moment both bound
/// values exist. This replaces eval + two binds (3 passes) with 1.
///
/// Operates on quarters of each array (`half2 = len/4`). For `i ∈ 0..half2`:
/// ```text
///   lo' = q0[i] + r·(q2[i] + q0[i])   (= new[i],        next round's lo)
///   hi' = q1[i] + r·(q3[i] + q1[i])   (= new[i+half2],  next round's hi)
///   q0[i] ← lo';  q1[i] ← hi'
///   e1   += hi'·zhi';   einf += (hi'+lo')·(zhi'+zlo')
/// ```
/// In-place is safe: each `i` reads its 4 quarter-entries before writing the 2
/// low-half slots, and writes across distinct `i` are disjoint. Requires
/// `comb.len() == z.len()`, a power of two ≥ 4 (so the bound length ≥ 2 has a
/// well-defined next round; the caller guarantees this by only fusing when a
/// later round exists). The returned message is bit-identical to
/// `sumcheck_round_eval_par` run on the bound tables.
fn sumcheck_bind_both_and_eval_next(comb: &mut Vec<F192>, z: &mut Vec<F192>, r: F192) -> (F192, F192) {
    let len = comb.len();
    debug_assert_eq!(z.len(), len);
    let half = len / 2;
    let half2 = half / 2;
    debug_assert!(half2 >= 1, "fused step needs a well-defined next round");

    // q0,q1 = low half (written); q2,q3 = high half (read-only).
    let (c_lo, c_hi) = comb.split_at_mut(half);
    let (cq0, cq1) = c_lo.split_at_mut(half2);
    let (cq2, cq3) = c_hi.split_at(half2);
    let (z_lo, z_hi) = z.split_at_mut(half);
    let (zq0, zq1) = z_lo.split_at_mut(half2);
    let (zq2, zq3) = z_hi.split_at(half2);

    let (e1, einf) = if half2 < SUMCHECK_PAR_THRESHOLD {
        let mut e1 = F192::ZERO;
        let mut einf = F192::ZERO;
        for i in 0..half2 {
            let lo = cq0[i] + r * (cq2[i] + cq0[i]);
            let hi = cq1[i] + r * (cq3[i] + cq1[i]);
            let zlo = zq0[i] + r * (zq2[i] + zq0[i]);
            let zhi = zq1[i] + r * (zq3[i] + zq1[i]);
            cq0[i] = lo;
            cq1[i] = hi;
            zq0[i] = zlo;
            zq1[i] = zhi;
            e1 += hi * zhi;
            einf += (hi + lo) * (zhi + zlo);
        }
        (e1, einf)
    } else {
        // The two written quarters are indexed rather than zipped: eight-way
        // `zip` of four mutable and four shared slices has no counterpart here,
        // and index `i` of each quarter is written by exactly one task.
        let cq0_p = parallel::SendPtr(cq0.as_mut_ptr());
        let cq1_p = parallel::SendPtr(cq1.as_mut_ptr());
        let zq0_p = parallel::SendPtr(zq0.as_mut_ptr());
        let zq1_p = parallel::SendPtr(zq1.as_mut_ptr());
        parallel::map_reduce(
            half2,
            || (F192::ZERO, F192::ZERO),
            |i| {
                // SAFETY: distinct `i` touch distinct slots of four disjoint
                // quarters (`split_at_mut` above), all borrowed for the dispatch.
                let (c0, c1, z0, z1) = unsafe {
                    (
                        &mut *cq0_p.add(i),
                        &mut *cq1_p.add(i),
                        &mut *zq0_p.add(i),
                        &mut *zq1_p.add(i),
                    )
                };
                let lo = *c0 + r * (cq2[i] + *c0);
                let hi = *c1 + r * (cq3[i] + *c1);
                let zlo = *z0 + r * (zq2[i] + *z0);
                let zhi = *z1 + r * (zq3[i] + *z1);
                *c0 = lo;
                *c1 = hi;
                *z0 = zlo;
                *z1 = zhi;
                (hi * zhi, (hi + lo) * (zhi + zlo))
            },
            |a, b| (a.0 + b.0, a.1 + b.1),
        )
    };

    comb.truncate(half);
    z.truncate(half);
    (e1, einf)
}

// ---------------------------------------------------------------------------
// API
// ---------------------------------------------------------------------------

/// The lincheck prover. Its claim retains the transmitted post-sumcheck
/// `z_partial`, which is exactly the AB claim's 64-entry ring-switch `s_hat_v`.
/// The opening reuses it without a second witness scan or transmission.
pub fn prove_padded_capture_s_hat_v(
    z_packed: &[u8],
    m: usize,
    k_log: usize,
    k_skip: usize,
    useful_bits: usize,
    circuit: &dyn LincheckCircuit,
    x_ab: &QuirkyPoint,
    ps: &mut ProverState,
) -> LincheckClaim {
    let k = 1usize << k_log;
    let n_log = m - k_log;
    assert!(m >= k_log);
    assert!(k_skip <= k_log, "k_skip must be ≤ k_log");
    assert!(useful_bits <= k, "useful_bits ({useful_bits}) > k ({k})");
    let inner_rest_len = k_log - k_skip;
    assert_eq!(circuit.n_cols(), k);
    assert_eq!(x_ab.x_inner_rest.len(), inner_rest_len);
    assert_eq!(x_ab.x_outer.len(), n_log);

    let trace = std::env::var("LINCHECK_TRACE").is_ok();
    let stage = |name: &str, t: std::time::Instant| {
        if trace {
            eprintln!("[lc] {name:<26} {:>7.2} ms", t.elapsed().as_secs_f64() * 1e3);
        }
    };

    // 1. Sample α (matches verifier's order). Used to batch the scalar
    //    consistency checks v_a, v_b, v_c into a single sumcheck.
    let alpha = ps.sample();

    // 2. Build the α-batched column marginal through the circuit.
    let t = std::time::Instant::now();
    let eq_inner = build_quirky_eq_table(x_ab.z_skip, &x_ab.x_inner_rest, k_skip);
    stage("build_quirky_eq", t);
    let t = std::time::Instant::now();
    let mut comb_vec = circuit.fold_alpha_batched(alpha, &eq_inner);
    stage("fold_alpha_batched", t);

    // 3. The zerocheck's c-claim, at α². `C = I`, so `ĉ(x_ab)` is the z-claim
    //    `Σ_j eq_inner[j]·ẑ(j, x_outer)`: the same row weights the matrices are
    //    folded against, which is why it costs one pass over a length-k vector
    //    and no extra sumcheck. It is what makes the AB and C claims come out
    //    of lincheck at ONE point.
    let alpha_sq = alpha.square();
    for (c, e) in comb_vec.iter_mut().zip(&eq_inner) {
        *c += alpha_sq * *e;
    }

    // 4. Constant-wire pin, at β = α³. Fold β·eq(j*, ·) into the comb so the
    //    same sumcheck also proves z_vec[j*] = 1 (the all-ones constant
    //    column). Since j* is a boolean index, eq(j*, ·) is the one-hot vector
    //    and this is a single entry update. See `LincheckCircuit::const_pin_col`.
    let beta = alpha_sq * alpha;
    comb_vec[circuit.const_pin_col()] += beta;

    // 5. Partial fold of z at the shared outer half (length-k F192 vector).
    let t = std::time::Instant::now();
    let eq_x_outer = build_eq(&x_ab.x_outer);
    let mut z_vec = partial_fold_packed_z_best(z_packed, m, k_log, useful_bits, &eq_x_outer);
    stage("partial_fold_z", t);

    let t_sumcheck = std::time::Instant::now();

    // 6. Standard multilinear product-sumcheck over the high `inner_rest_len`
    //    bits of `i`. Each round binds the TOP remaining bit. After `inner_rest_len` rounds, both
    //    tables collapse to length `2^k_skip`. Large rounds use the worker pool.
    let mut r_rounds = Vec::with_capacity(inner_rest_len);
    if inner_rest_len > 0 {
        // Round 0's message is the only standalone evaluation pass; every later
        // round's message falls out of binding the previous round (fold +
        // next-eval fused into one pass, see `sumcheck_bind_both_and_eval_next`).
        let (mut e1, mut einf) = sumcheck_round_eval_par(&comb_vec, &z_vec);
        // The running claim, mirrored from the verifier: `q(0) + q(1) = claim`
        // is what lets the wire drop `q(0)`, so the prover has to know it too.
        // Round 0's claim is the whole inner product, one O(k) pass over the
        // column vectors and negligible beside the sumcheck itself.
        let mut running = inner_product_ext(&comb_vec, &z_vec);
        for t in 0..inner_rest_len {
            let e0 = running + e1;
            ps.add_round_poly(&[e0, e0 + e1 + einf, einf], false);
            let r = ps.sample();
            running = (einf * r + (e0 + e1 + einf)) * r + e0;
            r_rounds.push(r);
            if t + 1 < inner_rest_len {
                // Fused: bind both tables at r AND compute round (t+1)'s message.
                let (ne1, neinf) = sumcheck_bind_both_and_eval_next(&mut comb_vec, &mut z_vec, r);
                e1 = ne1;
                einf = neinf;
            } else {
                // Final round: only z_vec is read afterwards (as z_partial), so
                // comb_vec's last fold would be dead work.
                sumcheck_bind_top_in_place_par(&mut z_vec, r);
            }
        }
    }
    stage("sumcheck (all rounds)", t_sumcheck);

    // 7. Send `z_partial` (the post-sumcheck collapsed z_vec). Length 2^k_skip.
    let z_partial = z_vec;
    for &x in z_partial.iter() {
        ps.add_scalar(x);
    }

    // 8. Convert sumcheck challenges to LSB-first `x_inner_rest` order. The
    //     loop binds the TOP bit each round, so r_rounds[0] bound bit
    //     (inner_rest_len − 1) of the i_rest part (= bit (k_log − 1) of i).
    //     LSB-first: x_inner_rest[j] binds bit (k_skip + j) of i, i.e.,
    //     r_inner_rest[j] = r_rounds[inner_rest_len − 1 − j].
    let mut r_inner_rest = r_rounds.clone();
    r_inner_rest.reverse();

    LincheckClaim {
        alpha,
        beta,
        r_rounds,
        r_inner_rest,
        s_hat_v: z_partial,
    }
}

/// Verify a lincheck proof. Walks the transcript in lockstep with the prover,
/// replays the α-batched product sumcheck against `v_a`, `v_b` and `v_c`, and
/// derives the single output z-claim `w`.
pub fn verify(
    m: usize,
    k_log: usize,
    k_skip: usize,
    circuit: &dyn LincheckCircuit,
    x_ab: &QuirkyPoint,
    v_a: F192,
    v_b: F192,
    v_c: F192,
    vs: &mut VerifierState<'_>,
) -> Result<LincheckClaim, VerifyError> {
    let k = 1usize << k_log;
    let n_log = m - k_log;

    if k_skip > k_log {
        return Err(VerifyError::KSkipExceedsKLog { k_skip, k_log });
    }
    let inner_rest_len = k_log - k_skip;
    let n_skip = 1usize << k_skip;

    if x_ab.x_inner_rest.len() != inner_rest_len {
        return Err(VerifyError::BadInnerRestLength {
            which: "x_ab",
            expected: inner_rest_len,
            got: x_ab.x_inner_rest.len(),
        });
    }
    if x_ab.x_outer.len() != n_log {
        return Err(VerifyError::BadOuterLength {
            which: "x_ab",
            expected: n_log,
            got: x_ab.x_outer.len(),
        });
    }
    if circuit.n_cols() != k {
        return Err(VerifyError::BadNCols {
            expected: k,
            got: circuit.n_cols(),
        });
    }

    // 1. Sample α (matches prover's order).
    let alpha = vs.sample();

    // 2. Row weights: the quirky eq table over the inner claim point, `u` in
    //    the final bilinear form. The α-batched column marginal the prover
    //    materializes (`fold_alpha_batched`, cost ∝ NNZ) is NOT built here:
    //    the verifier only ever consumes it through one inner product, so
    //    that work is deferred to step 5 (and walk-capable circuits answer it
    //    in O(circuit) ops without the marginal at all).
    let eq_inner = build_quirky_eq_table(x_ab.z_skip, &x_ab.x_inner_rest, k_skip);

    // 3. Replay the multilinear product-sumcheck (inner_rest_len rounds).
    //    Only the transcript messages drive the running claim; the prover's
    //    lockstep comb_vec fold is linear, so its end state is reconstructed
    //    in step 5 as column weights instead of being folded here.
    // Constant-wire pin (mirror of prove): β = α³, the comb's +β at the
    // constant column surfaces in step 5 as `+β·w_col[col]`, and the initial
    // target gains +β·1, since the honest all-ones constant column folds to 1.
    // See lincheck's `LincheckCircuit::const_pin_col`.
    // The zerocheck's c-claim at α² (mirror of prove step 3): `C = I`, so it
    // enters the comb as `α²·eq_inner` and the target as `α²·v_c`.
    let alpha_sq = alpha.square();
    let beta = alpha_sq * alpha;
    // The pin's target gains +β·1, the honest all-ones constant column folding to 1.
    let target = v_a + alpha * v_b + alpha_sq * v_c + beta;
    let mut running = target;
    let mut r_rounds = Vec::with_capacity(inner_rest_len);
    for _ in 0..inner_rest_len {
        // `c1 + c2 = claim` in char 2, so `c1` never rides the wire.
        let q = vs.next_round_poly(3, running, None).map_err(VerifyError::Transcript)?;
        let r = vs.sample();
        running = primitives::multilinear::poly_eval(&q, r);
        r_rounds.push(r);
    }

    // 4. Read + bind z_partial AFTER the sumcheck rounds (matches prover order).
    let z_partial: Vec<F192> = vs.next_scalars(n_skip).map_err(VerifyError::Transcript)?;

    // Convert sumcheck challenges to LSB-first x_inner_rest order (same
    // convention as prover; also the eq-ordering of the step-5 column weights).
    let mut r_inner_rest = r_rounds.clone();
    r_inner_rest.reverse();

    // 5. Final sumcheck consistency. The prover's comb_partial (comb_vec
    //    bound MSB-first at r_rounds) satisfies
    //
    //      ⟨comb_partial, z_partial⟩ = Σ_c comb_vec[c] · w_col[c],
    //      w_col[i_skip + i_rest·2^k_skip] = z_partial[i_skip] · eq(r_inner_rest, i_rest),
    //
    //    so the whole check collapses to ONE bilinear form
    //    `eq_innerᵀ·(A_0 + α·B_0)·w_col + β·w_col[pin]` against the running
    //    claim. Ties z_partial to the upstream v_a, v_b. Walk-capable circuits
    //    (`bilinear_form`) evaluate it in O(circuit) field ops; the fallback
    //    materializes the marginal and takes the inner product (identical
    //    value, exact field arithmetic).
    let eq_rest = build_eq(&r_inner_rest);
    let w_col = outer_product(&eq_rest, &z_partial);
    debug_assert_eq!(w_col.len(), k);
    let mut final_sum = match circuit.bilinear_form(alpha, &eq_inner, &w_col) {
        Some(v) => v,
        None => inner_product_ext(&circuit.fold_alpha_batched(alpha, &eq_inner), &w_col),
    };
    final_sum += beta * w_col[circuit.const_pin_col()];
    // The c term's `⟨eq_inner, w_col⟩`, by the tensor structure of both sides:
    // `eq_inner = eq(x_inner_rest) ⊗ λ(z_skip)` and `w_col = eq(r_inner_rest) ⊗
    // z_partial`, so it is 8 eq factors times a 64-term Lagrange combination
    // instead of a length-k inner product. That is the form the recursive
    // verifier can afford.
    let lambda_skip = lagrange_weights_naive(k_skip, x_ab.z_skip);
    let c_slice_value = lambda_skip
        .iter()
        .zip(&z_partial)
        .fold(F192::ZERO, |acc, (&w, &s)| acc + w * s);
    final_sum += alpha_sq * eq_eval(&x_ab.x_inner_rest, &r_inner_rest) * c_slice_value;
    if running != final_sum {
        return Err(VerifyError::ConsistencyFailed {
            which: "sumcheck-final",
        });
    }

    // 6. `z_partial` IS the output claim: the 64 bit-slice values of z at
    //    (r_inner_rest, x_outer), pinned by the identity just checked, and ring
    //    switching binds all 64 of them against the commitment.
    Ok(LincheckClaim {
        alpha,
        beta,
        r_rounds,
        r_inner_rest,
        s_hat_v: z_partial,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Test shim for the old dense-prove entry: the capture variant with a
    /// dense block and the captured `s_hat_v` discarded.
    fn prove(
        z_packed: &[u8],
        m: usize,
        k_log: usize,
        k_skip: usize,
        circuit: &dyn LincheckCircuit,
        x_ab: &QuirkyPoint,
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> LincheckClaim {
        prove_padded_capture_s_hat_v(z_packed, m, k_log, k_skip, 1 << k_log, circuit, x_ab, ps)
    }

    /// Test shim: the padded fast fold with a dense (no-padding) block.
    fn partial_fold_packed_z_fast_padded_dense(
        z_packed: &[u8],
        m: usize,
        k_log: usize,
        eq_outer: &[F192],
    ) -> Vec<F192> {
        partial_fold_packed_z_fast_padded(z_packed, m, k_log, 1 << k_log, eq_outer)
    }

    /// Reference fold `M_0^T · eq` (the row-MLE at all boolean column indices),
    /// used to locate meaningful mutation targets and as a dense oracle.
    /// The constant-one column the protocol tests pin. Any column works; the
    /// witness just has to carry a `1` there in every block, which is exactly
    /// what a real circuit's constant wire does.
    const PIN_COL: usize = 0;

    /// `rng.bits(n)` with the pin honoured in every block.
    fn pinned_bits(rng: &mut Rng, n: usize, k_log: usize) -> Vec<bool> {
        let mut z = rng.bits(n);
        for block in z.chunks_exact_mut(1 << k_log) {
            block[PIN_COL] = true;
        }
        z
    }

    /// Sparse boolean matrix, test-only: the protocol tests below drive lincheck
    /// with random R1CS instances, which is the one place a matrix still exists.
    /// Nothing on a prove or verify path builds one (see `hash`'s walks).
    #[derive(Clone)]
    struct SparseBinaryMatrix {
        num_rows: usize,
        num_cols: usize,
        rows: Vec<Vec<usize>>,
    }

    /// `A = I_{2^n_log} ⊗ A_0` applied to a boolean witness.
    fn apply_block_diag(m_0: &SparseBinaryMatrix, z: &[bool], k_log: usize) -> Vec<bool> {
        let k = 1usize << k_log;
        assert_eq!(m_0.num_rows, k);
        assert_eq!(m_0.num_cols, k);
        assert_eq!(z.len() % k, 0);
        let mut out = Vec::with_capacity(z.len());
        for z_block in z.chunks_exact(k) {
            out.extend(
                m_0.rows
                    .iter()
                    .map(|row| row.iter().fold(false, |acc, &col| acc ^ z_block[col])),
            );
        }
        out
    }

    /// A [`LincheckCircuit`] over materialized matrices, by the naive row
    /// scatter. Test-only, and no longer performance-critical, so there is no
    /// reason for it to be anything cleverer.
    struct SparseCircuit {
        a_0: SparseBinaryMatrix,
        b_0: SparseBinaryMatrix,
        pin: usize,
    }

    impl LincheckCircuit for SparseCircuit {
        fn n_cols(&self) -> usize {
            self.a_0.num_cols
        }
        fn const_pin_col(&self) -> usize {
            self.pin
        }
        fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
            let scatter = |m: &SparseBinaryMatrix| {
                let mut out = vec![F192::ZERO; m.num_cols];
                for (i, row) in m.rows.iter().enumerate() {
                    for &j in row {
                        out[j] += eq_inner[i];
                    }
                }
                out
            };
            let (a, b) = (scatter(&self.a_0), scatter(&self.b_0));
            a.iter().zip(&b).map(|(&x, &y)| x + alpha * y).collect()
        }
    }

    fn sparse_row_fold(matrix: &SparseBinaryMatrix, eq_table: &[F192]) -> Vec<F192> {
        assert_eq!(eq_table.len(), matrix.num_rows);
        let mut out = vec![F192::ZERO; matrix.num_cols];
        for (row_idx, row) in matrix.rows.iter().enumerate() {
            let e = eq_table[row_idx];
            for &col in row {
                out[col] += e;
            }
        }
        out
    }

    /// Sample a random `QuirkyPoint` for testing: z_skip ∈ F₁₉₂,
    /// x_inner_rest of length `k_log − k_skip`, x_outer of length `n_log`.
    fn random_quirky_point(m: usize, k_log: usize, k_skip: usize, rng: &mut Rng) -> QuirkyPoint {
        QuirkyPoint {
            z_skip: rng.ext(),
            x_inner_rest: rng.ext_vec(k_log - k_skip),
            x_outer: rng.ext_vec(m - k_log),
        }
    }

    /// "Quirky MLE evaluation" of a Boolean vector `f` at a quirky point.
    ///
    /// `ã(z_skip, x_inner_rest, x_outer) = Σ_i  f[i] · L_{i_skip}(z_skip)
    ///                                          · eq(x_inner_rest, i_inner_rest)
    ///                                          · eq(x_outer, i_outer)`
    ///
    /// where `i = i_skip + 2^k_skip · i_inner_rest + 2^k_log · i_outer` (matches
    /// the linear-LSB indexing of `f`).
    fn mle_eval_bool_quirky(f: &[bool], m: usize, k_log: usize, k_skip: usize, point: &QuirkyPoint) -> F192 {
        let k_skip_dim = 1usize << k_skip;
        let inner_rest_len = k_log - k_skip;
        let inner_rest_dim = 1usize << inner_rest_len;
        let k = 1usize << k_log;
        let n_outer = 1usize << (m - k_log);
        assert_eq!(f.len(), 1 << m);

        // Tower helpers: the point is F192 (the verifier's field), and the
        // expected value must equal the F192 claim the verifier derives.
        let lambda = lagrange_weights_naive(k_skip, point.z_skip);
        let eq_rest = build_eq(&point.x_inner_rest);
        let eq_outer = build_eq(&point.x_outer);
        debug_assert_eq!(lambda.len(), k_skip_dim);
        debug_assert_eq!(eq_rest.len(), inner_rest_dim);
        debug_assert_eq!(eq_outer.len(), n_outer);

        let mut acc = F192::ZERO;
        for i in 0..(1 << m) {
            if !f[i] {
                continue;
            }
            let i_skip = i & (k_skip_dim - 1);
            let i_inner_rest = (i >> k_skip) & (inner_rest_dim - 1);
            let i_outer = i / k;
            acc += lambda[i_skip] * eq_rest[i_inner_rest] * eq_outer[i_outer];
        }
        acc
    }

    /// Build a sparse boolean matrix with `nnz` random nonzero entries among
    /// `k × k` slots. Used for tests.
    fn random_sparse_matrix(k: usize, nnz: usize, rng: &mut Rng) -> SparseBinaryMatrix {
        let mut rows: Vec<Vec<usize>> = vec![Vec::new(); k];
        let mut seen = std::collections::HashSet::new();
        let mut count = 0;
        while count < nnz {
            let r = (rng.next_u64() as usize) % k;
            let c = (rng.next_u64() as usize) % k;
            if seen.insert((r, c)) {
                rows[r].push(c);
                count += 1;
            }
        }
        for row in &mut rows {
            row.sort();
        }
        SparseBinaryMatrix {
            num_rows: k,
            num_cols: k,
            rows,
        }
    }

    // ---- Unit tests for the kernels ----

    /// `partial_fold_packed_z` matches the direct sum.
    #[test]
    fn partial_fold_matches_direct() {
        for &(m, k_log) in &[(10usize, 3), (12, 4), (14, 5), (16, 8)] {
            let mut rng = Rng::new(33 + m as u64);
            let z = rng.bits(1 << m);
            let z_packed = pack_z_lincheck(&z, m, k_log);
            let n_log = m - k_log;
            let outer_point = rng.ext_vec(n_log);
            let eq_outer = build_eq(&outer_point);

            let got = partial_fold_packed_z(&z_packed, m, k_log, &eq_outer);

            let k = 1usize << k_log;
            assert_eq!(got.len(), k);
            for i_inner in 0..k {
                let mut acc = F192::ZERO;
                for i_outer in 0..(1usize << n_log) {
                    let i = i_inner + i_outer * k;
                    if z[i] {
                        acc += eq_outer[i_outer];
                    }
                }
                assert_eq!(got[i_inner], acc, "mismatch at m={m}, i_inner={i_inner}");
            }
        }
    }

    /// `partial_fold_packed_z_fast` (parallel lookup-table) matches the scalar
    /// reference `partial_fold_packed_z`.
    #[test]
    fn partial_fold_fast_matches_serial() {
        for &(m, k_log) in &[(10usize, 3), (12, 4), (14, 5), (16, 8), (18, 10)] {
            let mut rng = Rng::new(800 + m as u64);
            let z = rng.bits(1 << m);
            let z_packed = pack_z_lincheck(&z, m, k_log);
            let n_log = m - k_log;
            let p = rng.ext_vec(n_log);
            let eq = build_eq(&p);

            let serial = partial_fold_packed_z(&z_packed, m, k_log, &eq);
            let fast = partial_fold_packed_z_fast_padded_dense(&z_packed, m, k_log, &eq);
            assert_eq!(serial, fast, "at m={m}, k_log={k_log}");
        }
    }

    /// NEON single-matrix kernel matches the scalar reference.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn partial_fold_neon_single_matches_serial() {
        for &(m, k_log) in &[(14usize, 4), (14, 5), (16, 5), (16, 8), (18, 10)] {
            if !n_log_ok_for_tile(m, k_log, NEON_TILE_T) {
                continue;
            }
            let mut rng = Rng::new(7000 + m as u64);
            let z = rng.bits(1 << m);
            let z_packed = pack_z_lincheck(&z, m, k_log);
            let n_log = m - k_log;
            let p = rng.ext_vec(n_log);
            let eq = build_eq(&p);

            let serial = partial_fold_packed_z(&z_packed, m, k_log, &eq);
            let iblock = partial_fold_packed_z_iblock_padded(&z_packed, m, k_log, 1usize << k_log, &eq);
            assert_eq!(serial, iblock, "iblock at m={m}, k_log={k_log}");
        }
    }

    /// The default outer(tile)-partitioned fold is **bit-identical** to the legacy
    /// i_inner-partitioned iblock kernel, dense (useful=k) and padded (useful<k,
    /// including a non-byte-aligned shape) across tile-eligible sizes. GF(2¹²⁸) add
    /// is XOR (associative + commutative), so the two partition strategies must
    /// produce the exact same length-k vector.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn partial_fold_oblock_matches_iblock() {
        // (m, k_log, useful_bits); mix of dense and padded, all tile-eligible.
        let cases: &[(usize, usize, usize)] = &[
            (14, 4, 1 << 4),   // dense, small k
            (16, 8, 1 << 8),   // dense
            (18, 10, 1 << 10), // dense
            (20, 10, 597),     // padded, non-byte-aligned
            (22, 14, 15_409),  // padded, non-byte-aligned (k=16384)
        ];
        for &(m, k_log, useful_bits) in cases {
            assert!(n_log_ok_for_tile(m, k_log, NEON_TILE_T), "case must be tile-eligible");
            let k = 1usize << k_log;
            let n_log = m - k_log;
            let n_blocks = 1usize << n_log;
            let mut rng = Rng::new(7200 + (m * 31 + k_log) as u64);
            let mut z = rng.bits(1 << m);
            // Honest padding: zero rows [useful, k) of every block.
            for blk in 0..n_blocks {
                for j in useful_bits..k {
                    z[blk * k + j] = false;
                }
            }
            let z_packed = pack_z_lincheck(&z, m, k_log);
            let eq = build_eq(&rng.ext_vec(n_log));
            let want = partial_fold_packed_z_iblock_padded(&z_packed, m, k_log, useful_bits, &eq);
            let got = partial_fold_packed_z_oblock_padded(&z_packed, m, k_log, useful_bits, &eq);
            assert_eq!(want, got, "m={m} k_log={k_log} useful={useful_bits}");
        }
    }

    /// **Padding skip is byte-identical to the dense partial fold.** On a
    /// witness with honest zeros at rows `[useful_bits, 2^k_log)` of every
    /// block, the padded kernels (fast + NEON single) must produce the
    /// exact same `z_vec` as the dense kernels, and the dense scalar
    /// reference is the ground truth.
    ///
    /// Covers a `useful_bits` that is not byte-aligned (exercising the NEON
    /// boundary block, rounded up to `BLOCK_K = 8`) at two block sizes, plus one
    /// that lands exactly on a byte boundary.
    #[test]
    fn partial_fold_padded_matches_dense() {
        // (m, k_log, useful_bits)
        let cases: &[(usize, usize, usize)] = &[
            // BLAKE2s's own shape: k_log = 14, useful = 15409, not byte-aligned.
            (17, 14, 15_409),
            // A larger block, also not byte-aligned.
            (18, 15, 31_401),
            // Exact byte boundary.
            (19, 16, 42_560),
        ];
        for &(m, k_log, useful_bits) in cases {
            let mut rng = Rng::new(0xBADD_BEEF_u64.wrapping_add((k_log * 31 + m) as u64));
            let total_bits = 1usize << m;
            let n_log = m - k_log;
            let block_size = 1usize << k_log;
            let n_blocks = 1usize << n_log;

            // Random witness with bits [useful_bits, block_size) of every block
            // zeroed, mirroring the hash-module layout.
            let mut z = rng.bits(total_bits);
            for blk in 0..n_blocks {
                for j in useful_bits..block_size {
                    z[blk * block_size + j] = false;
                }
            }
            let z_packed = pack_z_lincheck(&z, m, k_log);
            let outer_point = rng.ext_vec(n_log);
            let eq_outer = build_eq(&outer_point);

            let dense_fast = partial_fold_packed_z_fast_padded_dense(&z_packed, m, k_log, &eq_outer);
            let padded_fast = partial_fold_packed_z_fast_padded(&z_packed, m, k_log, useful_bits, &eq_outer);
            assert_eq!(
                dense_fast, padded_fast,
                "fast: m={m}, k_log={k_log}, useful={useful_bits}"
            );

            #[cfg(target_arch = "aarch64")]
            if n_log_ok_for_tile(m, k_log, NEON_TILE_T) {
                let dense_neon = partial_fold_packed_z_iblock_padded(&z_packed, m, k_log, 1usize << k_log, &eq_outer);
                let padded_neon = partial_fold_packed_z_iblock_padded(&z_packed, m, k_log, useful_bits, &eq_outer);
                assert_eq!(
                    dense_neon, padded_neon,
                    "neon: m={m}, k_log={k_log}, useful={useful_bits}"
                );
            }
        }
    }

    // ---- End-to-end prove/verify roundtrip on honest data ----

    /// Build a small honest instance: random sparse A_0/B_0/C_0, random z;
    /// compute a, b, c via apply_block_diag; pick three points; compute true
    /// MLE evals as v, v', v''. Roundtrip prove/verify, check claim matches
    /// what the verifier would re-derive from the (now-known-honest) z.
    #[test]
    fn prove_verify_roundtrip_honest() {
        // Exercise a range of k_skip values:
        //   k_skip = 0 (no skip)     : reduces to multilinear lincheck
        //   k_skip = k_log (max)     : only univariate inner
        //   k_skip < k_log (typical) : protocol-realistic case
        for &(m, k_log, k_skip) in &[
            (10usize, 4, 0),
            (10, 4, 2),
            (10, 4, 4),
            (12, 5, 3),
            (14, 7, 6),
            (14, 7, 0),
        ] {
            let k = 1usize << k_log;
            let mut rng = Rng::new(55 + (m * 100 + k_log * 10 + k_skip) as u64);

            // Random sparse base matrices A_0, B_0 (no C since C = I in our use case).
            let nnz_per_mat = k * 2;
            let a_0 = random_sparse_matrix(k, nnz_per_mat, &mut rng);
            let b_0 = random_sparse_matrix(k, nnz_per_mat, &mut rng);

            // Random witness z, then a = A·z, b = B·z.
            let z = pinned_bits(&mut rng, 1 << m, k_log);
            let a = apply_block_diag(&a_0, &z, k_log);
            let b = apply_block_diag(&b_0, &z, k_log);
            let z_packed = pack_z_lincheck(&z, m, k_log);

            // **One shared quirky point** (since zerocheck gives a, b claims at
            // the same point).
            let x_ab = random_quirky_point(m, k_log, k_skip, &mut rng);

            // True quirky-MLE eval claims at the shared point.
            let v_a = mle_eval_bool_quirky(&a, m, k_log, k_skip, &x_ab);
            let v_b = mle_eval_bool_quirky(&b, m, k_log, k_skip, &x_ab);
            // C = I, so the c-claim is the quirky MLE of z itself.
            let v_c = mle_eval_bool_quirky(&z, m, k_log, k_skip, &x_ab);

            // Prove and verify with matched challengers.
            let circuit = SparseCircuit {
                a_0: a_0.clone(),
                b_0: b_0.clone(),
                pin: PIN_COL,
            };
            let mut ch_p = fiat_shamir::transcript::ProverState::from_label(b"flock-test-v0");
            let claim_p = prove(&z_packed, m, k_log, k_skip, &circuit, &x_ab, &mut ch_p);

            let proof_t = ch_p.into_proof();
            let mut ch_v = fiat_shamir::transcript::VerifierState::from_label(b"flock-test-v0", &proof_t);
            let claim_v = verify(m, k_log, k_skip, &circuit, &x_ab, v_a, v_b, v_c, &mut ch_v).unwrap_or_else(|e| {
                panic!("verify rejected honest proof at m={m},k_log={k_log},k_skip={k_skip}: {e:?}")
            });

            assert_eq!(
                claim_p, claim_v,
                "claim mismatch at m={m}, k_log={k_log}, k_skip={k_skip}"
            );

            // Every entry of the output vector must be the true bit-slice MLE
            // of z at (r_inner_rest, x_ab.x_outer): the whole claim, not just
            // one combination of it.
            let eq_rest = build_eq(&claim_v.r_inner_rest);
            let eq_outer = build_eq(&x_ab.x_outer);
            for i_skip in 0..(1usize << k_skip) {
                let mut acc = F192::ZERO;
                for (i_rest, &er) in eq_rest.iter().enumerate() {
                    for (i_outer, &eo) in eq_outer.iter().enumerate() {
                        if z[i_skip + (i_rest << k_skip) + (i_outer << k_log)] {
                            acc += er * eo;
                        }
                    }
                }
                assert_eq!(
                    claim_v.s_hat_v[i_skip], acc,
                    "slice {i_skip} wrong at m={m}, k_log={k_log}, k_skip={k_skip}"
                );
            }
        }
    }

    /// Verify must reject byte-mutated proofs. Mutation positions are picked
    /// where the corresponding matrix row-vector entry is **nonzero**;
    /// otherwise the inner-product delta vanishes and the mutation is
    /// undetectable (a property of the random sparse matrix, not a verifier
    /// bug). The verifier's consistency check is sound for *any* mutation in
    /// a nonzero-weighted slot.
    #[test]
    fn verify_rejects_mutations() {
        let m = 12;
        let k_log = 4;
        let k_skip = 2;
        let k = 1 << k_log;
        let mut rng = Rng::new(66);
        let a_0 = random_sparse_matrix(k, k * 5, &mut rng);
        let b_0 = random_sparse_matrix(k, k * 5, &mut rng);
        let z = pinned_bits(&mut rng, 1 << m, k_log);
        let a = apply_block_diag(&a_0, &z, k_log);
        let b = apply_block_diag(&b_0, &z, k_log);
        let z_packed = pack_z_lincheck(&z, m, k_log);
        let x_ab = random_quirky_point(m, k_log, k_skip, &mut rng);
        let v_a = mle_eval_bool_quirky(&a, m, k_log, k_skip, &x_ab);
        let v_b = mle_eval_bool_quirky(&b, m, k_log, k_skip, &x_ab);
        let v_c = mle_eval_bool_quirky(&z, m, k_log, k_skip, &x_ab);

        let circuit = SparseCircuit {
            a_0: a_0.clone(),
            b_0: b_0.clone(),
            pin: PIN_COL,
        };
        let mut ch_p = fiat_shamir::transcript::ProverState::from_label(b"flock-test-v0");
        let _ = prove(&z_packed, m, k_log, k_skip, &circuit, &x_ab, &mut ch_p);
        let proof_t = ch_p.into_proof();

        // Pick a mutation position where BOTH row vectors are nonzero so the
        // mutation guarantees both checks would diverge.
        let z_skip_g = x_ab.z_skip;
        let x_inner_rest_g = x_ab.x_inner_rest.to_vec();
        let eq_inner = build_quirky_eq_table(z_skip_g, &x_inner_rest_g, k_skip);
        let row_a = sparse_row_fold(&a_0, &eq_inner);
        let row_b = sparse_row_fold(&b_0, &eq_inner);
        let idx = (0..k)
            .find(|&i| row_a[i] != F192::ZERO || row_b[i] != F192::ZERO)
            .expect("no row-vector slot is nonzero in either A or B; test degenerate");

        // Mutations target `z_partial` (the post-sumcheck length-2^k_skip
        // vector), which rides the stream right after the 2·(k_log − k_skip)
        // round scalars. Bit-flipping any entry must cause the sumcheck-final
        // check to fail (running_claim ≠ Σ comb_partial · z_partial).
        let n_skip = 1usize << k_skip;
        let skip_idx = idx % n_skip;
        let zp_word = 2 * (k_log - k_skip) + skip_idx;
        for (label, hi) in [("lo", false), ("hi", true)] {
            let mut bad = proof_t.clone();
            if hi {
                bad.stream[zp_word].c1 ^= 1;
            } else {
                bad.stream[zp_word].c0 ^= 1;
            }
            let mut ch = fiat_shamir::transcript::VerifierState::from_label(b"flock-test-v0", &bad);
            let res = verify(m, k_log, k_skip, &circuit, &x_ab, v_a, v_b, v_c, &mut ch);
            assert!(
                matches!(res, Err(VerifyError::ConsistencyFailed { .. })),
                "verify did not reject z_partial[{skip_idx}].{label} bit-flip: got {res:?}"
            );
        }
    }

    /// Verify must reject shape errors.
    #[test]
    fn verify_rejects_shape_errors() {
        let m = 10;
        let k_log = 3;
        let k_skip = 1;
        let k = 1 << k_log;
        let mut rng = Rng::new(77);
        let a_0 = random_sparse_matrix(k, k, &mut rng);
        let b_0 = random_sparse_matrix(k, k, &mut rng);
        let z = pinned_bits(&mut rng, 1 << m, k_log);
        let a = apply_block_diag(&a_0, &z, k_log);
        let b = apply_block_diag(&b_0, &z, k_log);
        let z_packed = pack_z_lincheck(&z, m, k_log);
        let x_ab = random_quirky_point(m, k_log, k_skip, &mut rng);
        let v_a = mle_eval_bool_quirky(&a, m, k_log, k_skip, &x_ab);
        let v_b = mle_eval_bool_quirky(&b, m, k_log, k_skip, &x_ab);
        let v_c = mle_eval_bool_quirky(&z, m, k_log, k_skip, &x_ab);

        let circuit = SparseCircuit {
            a_0: a_0.clone(),
            b_0: b_0.clone(),
            pin: PIN_COL,
        };
        let mut ch_p = fiat_shamir::transcript::ProverState::from_label(b"flock-test-v0");
        let _ = prove(&z_packed, m, k_log, k_skip, &circuit, &x_ab, &mut ch_p);
        let proof_t = ch_p.into_proof();

        // Truncated stream (dropped last z_partial word): a clean Transcript error.
        let mut bad = proof_t.clone();
        bad.stream.pop();
        let mut ch = fiat_shamir::transcript::VerifierState::from_label(b"flock-test-v0", &bad);
        assert!(matches!(
            verify(m, k_log, k_skip, &circuit, &x_ab, v_a, v_b, v_c, &mut ch),
            Err(VerifyError::Transcript(_))
        ));

        // Wrong x_inner_rest length.
        let mut ch = fiat_shamir::transcript::VerifierState::from_label(b"flock-test-v0", &proof_t);
        let bad_x_ab = QuirkyPoint {
            z_skip: x_ab.z_skip,
            x_inner_rest: x_ab.x_inner_rest[..x_ab.x_inner_rest.len() - 1].to_vec(),
            x_outer: x_ab.x_outer.clone(),
        };
        assert!(matches!(
            verify(m, k_log, k_skip, &circuit, &bad_x_ab, v_a, v_b, v_c, &mut ch),
            Err(VerifyError::BadInnerRestLength { .. })
        ));

        // k_skip > k_log.
        let mut ch = fiat_shamir::transcript::VerifierState::from_label(b"flock-test-v0", &proof_t);
        assert!(matches!(
            verify(m, k_log, k_log + 1, &circuit, &x_ab, v_a, v_b, v_c, &mut ch),
            Err(VerifyError::KSkipExceedsKLog { .. })
        ));
    }
    /// AB-claim s_hat_v computed via `s_hat_v_from_z_vec` (reusing lincheck's
    /// pre-sumcheck partial fold of `z` at `x_outer`) is byte-identical to the
    /// general-purpose `fold_1b_rows` over the materialized suffix tensor.
    #[test]
    fn s_hat_v_from_z_vec_matches_fold_1b_rows_ab() {
        const K_SKIP: usize = 6;
        // (m, k_log), with K_SKIP fixed at 6 (so x_inner_rest has k_log − 6 coords;
        // x_inner_rest[0] becomes ring-switch's prefix0 because
        // K_SKIP + 1 = LOG_PACKING = 7). n_log = m − k_log must be ≥ 3 for
        // partial_fold_packed_z's stripe layout.
        let cases: &[(usize, usize)] = &[(13, 10), (15, 11), (17, 13)];
        for &(m, k_log) in cases {
            assert!(k_log >= pcs::pack::LOG_PACKING);
            assert!(k_log >= K_SKIP);
            let n_log = m - k_log;
            assert!(n_log >= 3);
            let mut rng = Rng::new(0xCAFE_u64.wrapping_add((m * 131 + k_log) as u64));

            // Boolean witness in standard logical (linear) layout.
            let z = rng.bits(1 << m);
            let packed = pcs::pack::pack_witness(&z, m);
            let z_packed_lincheck = pack_z_lincheck(&z, m, k_log);

            // AB-shaped quirky point: x_inner_rest has k_log − K_SKIP coords;
            // x_outer has n_log coords.
            let x_inner_rest: Vec<F192> = (0..(k_log - K_SKIP)).map(|_| rng.ext()).collect();
            let x_outer: Vec<F192> = (0..n_log).map(|_| rng.ext()).collect();

            // Reference: ring-switch's fold_1b_rows over the materialized
            // suffix tensor, exactly the path open_batch hits today.
            let mut x_outer_full = Vec::with_capacity(x_inner_rest.len() + x_outer.len());
            x_outer_full.extend_from_slice(&x_inner_rest);
            x_outer_full.extend_from_slice(&x_outer);
            let suffix_tensor = primitives::multilinear::eq_table(&x_outer_full);
            let want = pcs::ring_switch::fold_1b_rows(&packed, &suffix_tensor);

            // New path: lincheck-shaped partial fold of z at x_outer, then a
            // strided fold against the inner-rest tail.
            let eq_x_outer = primitives::multilinear::eq_table(&x_outer);
            let z_vec = partial_fold_packed_z(&z_packed_lincheck, m, k_log, &eq_x_outer);
            let got = pcs::ring_switch::s_hat_v_from_z_vec(&z_vec, &x_inner_rest);

            assert_eq!(got, want, "s_hat_v mismatch at m={m}, k_log={k_log}");
        }
    }
}
