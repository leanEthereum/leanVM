//! The Keccak step R1CS: one R1CS instance per VM `SHA3` instruction, encoding
//! `out = keccak_f(in ⊕ END_BIT·e₁₆)` ([`primitives::keccak::step`]), all 24 rounds
//! of Keccak-f\[1600\], in one sparse system.
//!
//! ## Why this shape
//!
//! θ, ρ, π and ι are linear over GF(2), so the only nonlinear gadget is χ: per
//! row of five bits, `a[x] = b[x] ⊕ (¬b[x+1] ∧ b[x+2])`. Its five outputs have
//! five distinct degree-two monomials as quadratic parts, which four products of
//! affine forms cannot span, so χ's multiplicative complexity is exactly one
//! product per bit: 1600 per round, 38,400 per permutation. With the 1600 input
//! bits, the 1600 output bits and the constant wire that is 41,601 slots, which
//! is why the block is `2^16` wide where BLAKE2s needed `2^14`.
//!
//! Each product is committed and every other wire is an affine form substituted
//! into its consumers, so the matrices are dense in their θ cascade, but they
//! are never built. The two directions a proof needs are walks of this circuit:
//! [`row_values_walk`] forwards (and [`bilinear_walk_pair`], the same pass
//! contracted against row weights) and [`marginal_walk`] backwards. See
//! doc/leanvm, Annex C "Evaluating the matrices".
//!
//! ## Witness layout per instance (`k_log = 16`, 1024 words of 64 bits)
//!
//! A Keccak lane is one 64-bit word, so every VM-visible value is a whole packed
//! word and the witness is written with whole-word stores.
//!
//! ```text
//!   words   0 ..  25     in[0..25]        the input lanes (free)
//!   words  25 ..  50     out[0..25]       the output lanes (lin-id)
//!   word   50, bit 0     1                the constant wire
//!   words  51 .. 651     p[r][j]          round r's χ products for lane j
//!   the rest             padding, forced to 0 by empty rows
//! ```
//!
//! ## Constraint shape (`C = I`)
//!
//! Every slot is the output of exactly one row `⟨A_k, z⟩·⟨B_k, z⟩ = z_k`:
//!
//! - the constant wire: `A = B = [1]`, pinned to one by lincheck;
//! - a free input: `A = [slot]`, `B = [1]`;
//! - a χ product of round `r`, lane `j = x + 5y`, bit `k`:
//!   `A = ¬b[x+1, y]ₖ`, `B = b[x+2, y]ₖ`, where `b` is the round's state after θ,
//!   ρ and π, an affine form in the inputs and the earlier products;
//! - an output: `A` = the final state's bit, `B = [1]`.
//!
//! ## What this does NOT enforce
//!
//! **Input binding**: the input lanes are free witness words. Pinning them to the
//! values the VM read is the embedding protocol's job, via PCS openings at fixed
//! slots.

use crate::gf2k::{
    LANE_BITS, MatrixSide, RowValues, WireLane, wire_from_slot_base, wire_rotl, wire_rotr, wire_xor, wire_xor_const,
};
use crate::verifier;
use crate::witness::drive_witness_packed_and_lincheck;
use crate::witness::packed_bytes;
use pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, RingSwitchVerify, RingSwitchVerifyClaim};
use primitives::field::F192;
use primitives::keccak::{END_BIT, END_LANE, PI, RC, RHO, ROUNDS, STATE_LANES};
use zk_alloc::ArenaVec;

// ---------------------------------------------------------------------------
// Public constants
// ---------------------------------------------------------------------------

/// Block dim: one Keccak step occupies `2^K_LOG = 65,536` z slots.
pub const K_LOG: usize = 16;
/// `k = 2^K_LOG`.
pub const K: usize = 1 << K_LOG;
/// Univariate-skip dim, must match [`crate::zerocheck::K_SKIP`].
pub const K_SKIP: usize = 6;

// A claim's `2^K_SKIP` slices are a ring-switch claim on `q_flock` only if that
// matches the packing width; otherwise `ring_claim` fails at run time.
const _: () = assert!(
    K_SKIP == LOG_PACKING,
    "the univariate skip must match the PCS packing width"
);

/// Rounds per permutation.
pub const N_ROUNDS: usize = ROUNDS;

/// One instance's input: the 25 lanes the VM reads, lane 16 before the step
/// XORs [`END_BIT`] into it.
pub type Instance = [u64; STATE_LANES];

// ---------------------------------------------------------------------------
// Layout positions (bit indices into the per-instance z slice of length K)
// ---------------------------------------------------------------------------

/// Word (packed-slot) index of input lane 0.
pub const IN_WORD: usize = 0;
/// Word index of output lane 0.
pub const OUT_WORD: usize = STATE_LANES;
/// Word holding the constant wire, in its bit 0.
const CONST_WORD: usize = 2 * STATE_LANES;
/// Word index of round 0's first product lane.
const PROD_WORD: usize = CONST_WORD + 1;

pub const Z_CONST_POS: usize = CONST_WORD * LANE_BITS; // 3200
/// Slots up to the last product; everything past is padding.
pub const USEFUL_BITS: usize = (PROD_WORD + N_ROUNDS * STATE_LANES) * LANE_BITS; // 41,664

const _: () = assert!(USEFUL_BITS <= K, "Keccak-f does not fit the 2^K_LOG block");

#[inline]
fn in_bit(lane: usize, k: usize) -> usize {
    (IN_WORD + lane) * LANE_BITS + k
}
#[inline]
fn out_bit(lane: usize, k: usize) -> usize {
    (OUT_WORD + lane) * LANE_BITS + k
}
/// Word of round `r`'s product lane `j`.
#[inline]
fn prod_word(r: usize, j: usize) -> usize {
    PROD_WORD + STATE_LANES * r + j
}

/// The two lanes χ reads for lane `j = x + 5y`: `(x+1, y)` negated, then `(x+2, y)`.
#[inline]
fn chi_operands(j: usize) -> (usize, usize) {
    let (x, y) = (j % 5, j / 5);
    ((x + 1) % 5 + 5 * y, (x + 2) % 5 + 5 * y)
}

/// The relation one instance proves, the witness oracle.
pub fn step(input: &Instance) -> [u64; STATE_LANES] {
    primitives::keccak::step(input)
}

/// The padding instance: the step of the all-zero state. Fills unused trailing
/// slots so every batched block is a valid instance with constant wire 1, as the
/// lincheck const-wire pin requires.
pub fn padding_instance() -> Instance {
    [0; STATE_LANES]
}

/// Domain separator for this circuit in the Fiat-Shamir seed (`lean_vm::cpu`):
/// the hash of [`R1CS_DIGEST_LABEL`], which names the relation and its layout.
/// A deliberate circuit change bumps the label, and the digest is mirrored in
/// `python-verifier/verifier.py` and in the recursion guest.
pub const R1CS_DIGEST: [u8; 32] = [
    0x3e, 0x1e, 0x2d, 0xd8, 0x64, 0xd8, 0xaa, 0xf3, 0x5a, 0xd3, 0x6e, 0x47, 0xd7, 0x64, 0x15, 0x22, 0xea, 0x04, 0x2e,
    0x54, 0x2c, 0x87, 0x0b, 0x9e, 0x94, 0xf4, 0xb0, 0x7d, 0x35, 0xb6, 0xee, 0x60,
];
/// What [`R1CS_DIGEST`] hashes.
pub const R1CS_DIGEST_LABEL: &[u8] = b"leanVM flock R1CS: keccak step, k_log 16, in 0, out 25, const 3200, products 51";

/// Minimum `n_blocks_log` needed to prove `n_blocks` steps, subject to the
/// lincheck floor of `n_blocks_log ≥ 3` (`n_outer ≥ 8`).
pub fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
    n_blocks.max(8).next_power_of_two().trailing_zeros() as usize
}

// ---------------------------------------------------------------------------
// Circuit-walk evaluation: `(uᵀ A_0 w, uᵀ B_0 w)` in O(circuit) field ops,
// over matrices that are never materialized. The row assignment these walks
// encode is specified in doc/leanvm, Annex C "Evaluating the matrices".
// ---------------------------------------------------------------------------

/// θ, ρ and π on wire lanes.
fn theta_rho_pi(a: &[WireLane; STATE_LANES]) -> [WireLane; STATE_LANES] {
    let c: [WireLane; 5] = std::array::from_fn(|x| {
        let mut col = a[x];
        for y in 1..5 {
            col = wire_xor(&col, &a[x + 5 * y]);
        }
        col
    });
    let d: [WireLane; 5] = std::array::from_fn(|x| wire_xor(&c[(x + 4) % 5], &wire_rotl(&c[(x + 1) % 5], 1)));
    let mut b = [[F192::ZERO; LANE_BITS]; STATE_LANES];
    for i in 0..STATE_LANES {
        b[PI[i]] = wire_rotl(&wire_xor(&a[i], &d[i % 5]), RHO[i] as usize);
    }
    b
}

/// One forward pass of the circuit against column weights `w`, storing every
/// row's operand pair.
fn forward_walk(sink: &mut RowValues, w: &[F192]) {
    let wc = w[Z_CONST_POS];
    sink.bconst(Z_CONST_POS, wc);
    let mut a: [WireLane; STATE_LANES] = std::array::from_fn(|i| wire_from_slot_base(w, in_bit(i, 0)));
    for (i, lane) in a.iter().enumerate() {
        for k in 0..LANE_BITS {
            sink.bconst(in_bit(i, k), lane[k]);
        }
    }
    wire_xor_const(&mut a[END_LANE], wc, END_BIT);
    for (r, &rc) in RC.iter().enumerate() {
        let b = theta_rho_pi(&a);
        for (j, lane) in a.iter_mut().enumerate() {
            let (j1, j2) = chi_operands(j);
            let base = prod_word(r, j) * LANE_BITS;
            for k in 0..LANE_BITS {
                sink.product(base + k, b[j1][k] + wc, b[j2][k]);
                lane[k] = b[j][k] + w[base + k];
            }
        }
        wire_xor_const(&mut a[0], wc, rc);
    }
    for (i, lane) in a.iter().enumerate() {
        for k in 0..LANE_BITS {
            sink.bconst(out_bit(i, k), lane[k]);
        }
    }
}

pub fn bilinear_walk_pair(u: &[F192], w: &[F192]) -> (F192, F192) {
    assert_eq!(u.len(), K);
    assert_eq!(w.len(), K);
    let (a, b) = row_values_walk(w);
    let mut va = F192::ZERO;
    let mut vb = F192::ZERO;
    for ((&ui, &ai), &bi) in u.iter().zip(&a).zip(&b) {
        va += ui * ai;
        vb += ui * bi;
    }
    (va, vb)
}

/// The matrix-vector products `(A_0 w, B_0 w)`, i.e. every row's inner product
/// with `w`, by one forward walk. Neither matrix is materialized.
pub fn row_values_walk(w: &[F192]) -> (Vec<F192>, Vec<F192>) {
    assert_eq!(w.len(), K);
    let mut sink = RowValues::new(K, w[Z_CONST_POS]);
    forward_walk(&mut sink, w);
    (sink.a, sink.b)
}

/// `(uᵀ A_0 w) + α·(uᵀ B_0 w)`, the α-batched form lincheck's verifier
/// consumes.
pub fn bilinear_walk(alpha: F192, u: &[F192], w: &[F192]) -> F192 {
    let (va, vb) = bilinear_walk_pair(u, w);
    va + alpha * vb
}

/// One matrix's column marginal, by one backward walk of the circuit.
///
/// ```text
///   M[j] = Σ_k D_0(k,j)·u[k],   j < K
/// ```
///
/// The forward walk evaluates `uᵀ D_0 w`, which is linear in `w`, so `M` is its
/// gradient: each step below is the transpose of the matching forward step, run
/// in reverse topological order.
fn marginal_walk_side(side: MatrixSide, u: &[F192]) -> Vec<F192> {
    assert_eq!(u.len(), K);
    let mut m = vec![F192::ZERO; K];
    // Everything that lands on the constant column: the constant row itself, the
    // B side of every free-input and output row, χ's negation and ι.
    let mut const_adj = u[Z_CONST_POS];

    // Output rows: A = the final state's bit, B = [1].
    let mut adj = [[F192::ZERO; LANE_BITS]; STATE_LANES];
    for (i, lane) in adj.iter_mut().enumerate() {
        for k in 0..LANE_BITS {
            let (a, b) = side.split(u[out_bit(i, k)]);
            lane[k] = a;
            const_adj += b;
        }
    }

    for r in (0..N_ROUNDS).rev() {
        // ι: a set round-constant bit reads the constant wire.
        for k in 0..LANE_BITS {
            if (RC[r] >> k) & 1 == 1 {
                const_adj += adj[0][k];
            }
        }
        // χ: a'[j] = b[j] + p[j], with product row A = b[j1] + 1, B = b[j2].
        let mut b_adj = [[F192::ZERO; LANE_BITS]; STATE_LANES];
        for j in 0..STATE_LANES {
            let (j1, j2) = chi_operands(j);
            let base = prod_word(r, j) * LANE_BITS;
            for k in 0..LANE_BITS {
                let g = adj[j][k];
                b_adj[j][k] += g;
                m[base + k] += g;
                let (pa, pb) = side.split(u[base + k]);
                b_adj[j1][k] += pa;
                const_adj += pa;
                b_adj[j2][k] += pb;
            }
        }
        // ρ and π: b[PI[i]] = rotl(a[i] + d[i mod 5], RHO[i]).
        let mut a_adj = [[F192::ZERO; LANE_BITS]; STATE_LANES];
        let mut d_adj = [[F192::ZERO; LANE_BITS]; 5];
        for i in 0..STATE_LANES {
            let t = wire_rotr(&b_adj[PI[i]], RHO[i] as usize);
            a_adj[i] = t;
            d_adj[i % 5] = wire_xor(&d_adj[i % 5], &t);
        }
        // θ: d[x] = c[x-1] + rotl(c[x+1], 1), c[x] = Σ_y a[x + 5y].
        let c_adj: [WireLane; 5] =
            std::array::from_fn(|x| wire_xor(&d_adj[(x + 1) % 5], &wire_rotr(&d_adj[(x + 4) % 5], 1)));
        for (i, lane) in a_adj.iter_mut().enumerate() {
            *lane = wire_xor(lane, &c_adj[i % 5]);
        }
        adj = a_adj;
    }

    // The input: a[i] = in[i], with END_BIT's constant on lane 16. Each input
    // slot is also its own row, A = [slot], B = [1].
    for (i, lane) in adj.iter().enumerate() {
        for k in 0..LANE_BITS {
            let s = in_bit(i, k);
            let (a, b) = side.split(u[s]);
            m[s] += lane[k] + a;
            const_adj += b;
        }
    }
    for k in 0..LANE_BITS {
        if (END_BIT >> k) & 1 == 1 {
            const_adj += adj[END_LANE][k];
        }
    }
    m[Z_CONST_POS] += const_adj;
    m
}

/// The two column marginals `(A_0ᵀ u, B_0ᵀ u)`, by one backward walk per matrix.
/// Neither matrix is materialized.
pub fn marginal_walk_pair(u: &[F192]) -> (Vec<F192>, Vec<F192>) {
    (
        marginal_walk_side(MatrixSide::A, u),
        marginal_walk_side(MatrixSide::B, u),
    )
}

/// The α-batched column marginal `(A_0 + α B_0)ᵀ u` used by lincheck.
pub fn marginal_walk(alpha: F192, u: &[F192]) -> Vec<F192> {
    let (mut a, b) = marginal_walk_pair(u);
    for (a, b) in a.iter_mut().zip(b) {
        *a += alpha * b;
    }
    a
}

/// Does `z` satisfy the block-diagonal R1CS, `(A_0 z) ⊙ (B_0 z) = z` per block?
/// `z` is the whole batch, `2^n_blocks_log` blocks of `K` bits.
pub fn satisfies(z: &[bool], n_blocks_log: usize) -> bool {
    assert_eq!(z.len(), K << n_blocks_log, "z must be one K-bit block per instance");
    let bit = |b: bool| if b { F192::ONE } else { F192::ZERO };
    (0..1usize << n_blocks_log).all(|t| {
        let block: Vec<F192> = z[t * K..(t + 1) * K].iter().map(|&b| bit(b)).collect();
        let (a, b) = row_values_walk(&block);
        (0..K).all(|k| a[k] * b[k] == block[k])
    })
}

/// Walk-capable [`crate::lincheck::LincheckCircuit`] over the Keccak R1CS: both
/// directions are circuit walks, so neither side needs a matrix.
pub struct WalkLincheckCircuit;

impl crate::lincheck::LincheckCircuit for WalkLincheckCircuit {
    fn n_cols(&self) -> usize {
        K
    }
    fn const_pin_col(&self) -> usize {
        Z_CONST_POS
    }
    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
        marginal_walk(alpha, eq_inner)
    }
    fn bilinear_form(&self, alpha: F192, u: &[F192], w: &[F192]) -> Option<F192> {
        Some(bilinear_walk(alpha, u, w))
    }
}

// ---------------------------------------------------------------------------
// Witness generation: emits the R1CS row-witnesses directly from the Keccak
// computation, one whole word per lane.
// ---------------------------------------------------------------------------

/// θ, ρ and π on native lanes.
#[inline(always)]
fn theta_rho_pi_native(a: &[u64; STATE_LANES]) -> [u64; STATE_LANES] {
    let c: [u64; 5] = std::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
    let d: [u64; 5] = std::array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1));
    let mut b = [0u64; STATE_LANES];
    for i in 0..STATE_LANES {
        b[PI[i]] = (a[i] ^ d[i % 5]).rotate_left(RHO[i]);
    }
    b
}

/// Build the (z, a, b) blocks for ONE instance, into this instance's `K / 64`
/// words of each packed table. Buffers must be zero on entry.
///
/// **No c buffer.** Since `C = I`, `c == z` word for word.
fn build_block_witness_ab_packed_into(input: &Instance, z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    debug_assert_eq!(z.len(), K / 64);
    debug_assert_eq!(a.len(), K / 64);
    debug_assert_eq!(b.len(), K / 64);

    z[CONST_WORD] = 1;
    a[CONST_WORD] = 1;
    b[CONST_WORD] = 1;
    for (i, &lane) in input.iter().enumerate() {
        z[IN_WORD + i] = lane;
        a[IN_WORD + i] = lane;
        b[IN_WORD + i] = u64::MAX;
    }

    let mut s = *input;
    s[END_LANE] ^= END_BIT;
    for (r, &rc) in RC.iter().enumerate() {
        let t = theta_rho_pi_native(&s);
        for (j, lane) in s.iter_mut().enumerate() {
            let (j1, j2) = chi_operands(j);
            let (left, right) = (!t[j1], t[j2]);
            let p = left & right;
            let w = prod_word(r, j);
            z[w] = p;
            a[w] = left;
            b[w] = right;
            *lane = t[j] ^ p;
        }
        s[0] ^= rc;
    }

    for (i, &lane) in s.iter().enumerate() {
        z[OUT_WORD + i] = lane;
        a[OUT_WORD + i] = lane;
        b[OUT_WORD + i] = u64::MAX;
    }
}

/// Produce `(z, a, b, z_lincheck)` for `instances.len()` steps padded to
/// `2^n_blocks_log` slots.
pub fn generate_witness_with_ab_packed_and_lincheck(
    instances: &[Instance],
    n_blocks_log: usize,
) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
    let padding = padding_instance();
    drive_witness_packed_and_lincheck(instances, Some(&padding), n_blocks_log, K_LOG, |input, z, a, b| {
        build_block_witness_ab_packed_into(input, z, a, b)
    })
}

// ---------------------------------------------------------------------------
// Convenience API: KeccakSetup
// ---------------------------------------------------------------------------

/// The Keccak step R1CS for the smallest supported power-of-two shape that can
/// hold `n_blocks` steps.
#[derive(Clone, Debug)]
pub struct KeccakSetup {
    n_blocks_log: usize,
}

impl KeccakSetup {
    /// Build a setup for `n_blocks` steps.
    pub fn new(n_blocks: usize) -> Self {
        Self {
            n_blocks_log: min_n_blocks_log(n_blocks),
        }
    }

    pub fn m(&self) -> usize {
        K_LOG + self.n_blocks_log
    }
    pub fn n_blocks_log(&self) -> usize {
        self.n_blocks_log
    }
    pub fn n_block_slots(&self) -> usize {
        1usize << self.n_blocks_log()
    }
}

/// The one claim on the committed witness `q_flock` left by the Flock
/// zerocheck + lincheck reduction, for the PCS to discharge: the `2^k_skip`
/// bit-slice values of `z` at `suffix_point`, transmitted and pinned inside the
/// reduction by lincheck's terminal identity (which batches A, B, the
/// constant-wire pin and C), so the PCS only has to bind them to the
/// commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim {
    pub suffix_point: Vec<F192>,
    pub s_hat_v: Vec<F192>,
}

/// The variable count (`log2` length) of the committed `q_flock` column for
/// `n_blocks` executed steps: `K_LOG + min_n_blocks_log − LOG_PACKING`. Always
/// at least one instance: `n_blocks = 0` still commits one padding instance,
/// keeping the proof shape uniform.
pub fn qflock_kappa(n_blocks: usize) -> usize {
    K_LOG + min_n_blocks_log(n_blocks.max(1)) - LOG_PACKING
}

/// One reduction claim as a tower [`RingSwitchClaim`]: the `2^k_skip` slices and
/// the suffix point they live at, which is the WHOLE multilinear tail of the
/// quirky point.
fn ring_claim(claim: &SliceClaim, qflock_vars: usize) -> RingSwitchClaim {
    assert_eq!(
        claim.suffix_point.len(),
        qflock_vars,
        "ring-switch suffix must span the q_flock cube"
    );
    assert_eq!(claim.s_hat_v.len(), PACKING_WIDTH);
    RingSwitchClaim {
        suffix_point: claim.suffix_point.clone(),
        s_hat_v: Some(claim.s_hat_v.clone()),
    }
}

/// Package the prover's reduction claim as a [`RingSwitchOpen`], so the PCS
/// discharges flock's validity in the same opening as the embedder's own point
/// claims. `offset` is `q_flock`'s slot in the committed stack.
pub fn ring_switch_open(n_blocks: usize, offset: usize, reduced: &SliceClaim) -> RingSwitchOpen {
    let qflock_vars = qflock_kappa(n_blocks);
    RingSwitchOpen {
        offset,
        qflock_vars,
        claims: vec![ring_claim(reduced, qflock_vars)],
    }
}

/// Verifier counterpart of [`ring_switch_open`].
pub fn ring_switch_verify(n_blocks: usize, offset: usize, claim: &SliceClaim) -> RingSwitchVerify<'_> {
    let qflock_vars = qflock_kappa(n_blocks);
    assert_eq!(
        claim.suffix_point.len(),
        qflock_vars,
        "ring-switch suffix must span the q_flock cube"
    );
    RingSwitchVerify {
        offset,
        qflock_vars,
        claims: vec![RingSwitchVerifyClaim {
            suffix_point: &claim.suffix_point,
            s_hat_v: claim.s_hat_v.as_slice().try_into().expect("ring-switch has 64 slices"),
        }],
    }
}

/// Everything [`KeccakSetup::verify_reduction`] recovers: the z-claim for the
/// PCS and the zerocheck / lincheck claims.
#[derive(Clone, Debug)]
pub struct ReductionReplay {
    pub claim: SliceClaim,
    pub zc_claim: crate::zerocheck::ZerocheckClaim,
    pub lc_claim: crate::lincheck::LincheckClaim,
}

/// The lincheck input point carried over from the zerocheck claim: the
/// univariate-skip coordinate, then the multilinear challenges split at
/// `inner_rest_len` into the inner-rest and outer halves.
fn x_ab_of(zc: &crate::zerocheck::ZerocheckClaim, inner_rest_len: usize) -> crate::lincheck::QuirkyPoint {
    crate::lincheck::QuirkyPoint {
        z_skip: zc.z,
        x_inner_rest: zc.mlv_challenges[..inner_rest_len].to_vec(),
        x_outer: zc.mlv_challenges[inner_rest_len..].to_vec(),
    }
}

/// The claim the reduction leaves for the PCS: lincheck's output point, whose
/// 64 slice values are `lc.s_hat_v`. Prover and verifier share this one
/// derivation.
fn reduction_claim(lc: &crate::lincheck::LincheckClaim, x_outer: &[F192]) -> SliceClaim {
    let mut suffix_point = lc.r_inner_rest.clone();
    suffix_point.extend_from_slice(x_outer);
    SliceClaim {
        suffix_point,
        s_hat_v: lc.s_hat_v.clone(),
    }
}

/// What the zerocheck stage hands the lincheck stage. Opaque; the two stages of
/// [`KeccakSetup::prove_reduction_precomputed`] are split only so a caller can
/// time or profile them apart.
#[derive(Clone, Debug)]
pub struct ZerocheckStage {
    x_ab: crate::lincheck::QuirkyPoint,
}

/// One `FLOCK_PROVE_TRACE` line. `label` carries its own colon so the stages
/// line up.
fn trace_stage(label: &str, t: std::time::Instant) {
    if std::env::var_os("FLOCK_PROVE_TRACE").is_some() {
        eprintln!("[flock prove] {label:<11}{:8.2} ms", t.elapsed().as_secs_f64() * 1e3);
    }
}

impl KeccakSetup {
    /// **Flock reduction (prover).** Run the zerocheck and lincheck on the
    /// shared transcript, reducing R1CS validity of `instances` to ONE evaluation
    /// claim on the committed packed witness `q_flock`. (The statement is already
    /// transcript-bound: the embedding protocol seeds with the R1CS digest and
    /// announces the count.) Returns the regenerated packed witness and the
    /// [`SliceClaim`] on `q_flock`.
    ///
    /// Does NOT open the PCS; the caller discharges the returned claim in the
    /// one stacked opening (`lean_vm`'s `pcs::open`).
    pub fn prove_reduction(
        &self,
        instances: &[Instance],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> (ArenaVec<u64>, SliceClaim) {
        assert!(
            instances.len() <= self.n_block_slots(),
            "{} steps exceed this setup's {} slots",
            instances.len(),
            self.n_block_slots()
        );
        let t_witness = std::time::Instant::now();
        let (z_packed, a_packed_words, b_packed_words, z_packed_lincheck) =
            generate_witness_with_ab_packed_and_lincheck(instances, self.n_blocks_log());
        trace_stage("witness:", t_witness);
        let reduced =
            self.prove_reduction_precomputed(&z_packed, &a_packed_words, &b_packed_words, &z_packed_lincheck, ps);
        (z_packed, reduced)
    }

    /// **Flock reduction from a prepared witness (prover)**: [`Self::prove_zerocheck`]
    /// then [`Self::prove_lincheck`], for embedders that generated the packed `z`,
    /// `A·z`, `B·z`, and lincheck-stripe buffers before committing.
    pub fn prove_reduction_precomputed(
        &self,
        z_packed: &[u64],
        a_packed_words: &[u64],
        b_packed_words: &[u64],
        z_packed_lincheck: &[u8],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> SliceClaim {
        let stage = self.prove_zerocheck(z_packed, a_packed_words, b_packed_words, ps);
        self.prove_lincheck(stage, z_packed_lincheck, ps)
    }

    /// **Flock reduction, first stage (prover): the zerocheck.** Reduces
    /// `a·b ⊕ c = 0` over the cube to evaluation claims on `(â, b̂, ĉ)`, all
    /// three at one point.
    pub fn prove_zerocheck(
        &self,
        z_packed: &[u64],
        a_packed_words: &[u64],
        b_packed_words: &[u64],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> ZerocheckStage {
        let t_zerocheck = std::time::Instant::now();
        let packed_len = 1usize << (self.m() - 6);
        assert_eq!(z_packed.len(), packed_len, "wrong packed witness length");
        assert_eq!(a_packed_words.len(), packed_len, "wrong packed A·z length");
        assert_eq!(b_packed_words.len(), packed_len, "wrong packed B·z length");

        let padding = crate::zerocheck::PaddingSpec {
            k_log: K_LOG,
            useful_bits_per_block: USEFUL_BITS,
        };
        let zc_claim = crate::zerocheck::prove_packed_padded(
            packed_bytes(a_packed_words),
            packed_bytes(b_packed_words),
            packed_bytes(z_packed), // C = I, so c == z
            self.m(),
            &padding,
            ps,
        );

        let x_ab = x_ab_of(&zc_claim, K_LOG - K_SKIP);
        trace_stage("zerocheck:", t_zerocheck);
        ZerocheckStage { x_ab }
    }

    /// **Flock reduction, second stage (prover): the lincheck.** Reduces the
    /// zerocheck's `(â, b̂, ĉ)` claims to the `2^k_skip` bit slices of `z` at
    /// one point, against the per-block matrices.
    pub fn prove_lincheck(
        &self,
        stage: ZerocheckStage,
        z_packed_lincheck: &[u8],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> SliceClaim {
        let t_lincheck = std::time::Instant::now();
        let packed_len = 1usize << (self.m() - 6);
        assert_eq!(z_packed_lincheck.len(), packed_len * 8, "wrong lincheck stripe length");

        let ZerocheckStage { x_ab } = stage;
        let lc_claim = crate::lincheck::prove_padded_capture_s_hat_v(
            z_packed_lincheck,
            self.m(),
            K_LOG,
            K_SKIP,
            USEFUL_BITS,
            &WalkLincheckCircuit,
            &x_ab,
            ps,
        );

        let claim = reduction_claim(&lc_claim, &x_ab.x_outer);
        trace_stage("lincheck:", t_lincheck);
        claim
    }

    /// **Flock reduction (verifier).** Replay the zerocheck and lincheck straight
    /// off the shared transcript stream, recovering the one evaluation claim on
    /// the committed witness `q_flock`.
    pub fn verify_reduction(
        &self,
        vs: &mut fiat_shamir::transcript::VerifierState<'_>,
    ) -> Result<ReductionReplay, verifier::VerifyError> {
        let zc_claim = crate::zerocheck::verify(self.m(), vs).map_err(verifier::VerifyError::Zerocheck)?;

        let inner_rest_len = K_LOG - K_SKIP;
        let x_ab = x_ab_of(&zc_claim, inner_rest_len);
        let lc_claim = crate::lincheck::verify(
            self.m(),
            K_LOG,
            K_SKIP,
            &WalkLincheckCircuit,
            &x_ab,
            zc_claim.a_eval,
            zc_claim.b_eval,
            zc_claim.c_eval,
            vs,
        )
        .map_err(verifier::VerifyError::Lincheck)?;

        let claim = reduction_claim(&lc_claim, &x_ab.x_outer);
        Ok(ReductionReplay {
            claim,
            zc_claim,
            lc_claim,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Unpack the first `n_bits` logical bits of a packed witness.
    fn unpack_bits(z: &[u64], n_bits: usize) -> Vec<bool> {
        (0..n_bits).map(|i| (z[i / 64] >> (i % 64)) & 1 == 1).collect()
    }

    fn generate_witness(instances: &[Instance], n_blocks_log: usize) -> Vec<bool> {
        let z = generate_witness_with_ab_packed_and_lincheck(instances, n_blocks_log).0;
        unpack_bits(&z, (1usize << n_blocks_log) * K)
    }

    fn random_instance(rng: &mut Rng) -> Instance {
        std::array::from_fn(|_| rng.next_u64())
    }

    #[test]
    fn r1cs_digest_matches_label() {
        assert_eq!(primitives::keccak::hash(R1CS_DIGEST_LABEL), R1CS_DIGEST);
    }

    /// Every slot a layout region claims is the output of one non-degenerate
    /// row, and every slot outside is padding. Guards the tiling: an overlap
    /// would leave a product unconstrained, and the overwritten row stays
    /// non-empty, so only the whole tiling catches it.
    #[test]
    fn constrained_rows_tile_the_layout() {
        let mut rng = Rng::new(0x7113D);
        let w: Vec<F192> = (0..K)
            .map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64()))
            .collect();
        let (va, vb) = row_values_walk(&w);
        let mut expected = vec![false; K];
        let mut claim = |base: usize, len: usize| {
            for s in base..base + len {
                assert!(!expected[s], "slot {s} is claimed by two layout regions");
                expected[s] = true;
            }
        };
        claim(in_bit(0, 0), STATE_LANES * LANE_BITS);
        claim(out_bit(0, 0), STATE_LANES * LANE_BITS);
        claim(Z_CONST_POS, 1);
        claim(prod_word(0, 0) * LANE_BITS, N_ROUNDS * STATE_LANES * LANE_BITS);
        for s in 0..K {
            // A row is empty exactly when it sums nothing; at a random `w` a
            // non-empty row is nonzero but for a `2^-192` accident.
            let constrained = va[s] != F192::ZERO || vb[s] != F192::ZERO;
            assert_eq!(
                constrained, expected[s],
                "slot {s} constrained={constrained}, want {}",
                expected[s]
            );
        }
    }

    #[test]
    fn witness_encodes_correct_output() {
        let mut rng = Rng::new(0x5AA3);
        let input = random_instance(&mut rng);
        let z = generate_witness_with_ab_packed_and_lincheck(&[input], 3).0;
        let expected = step(&input);
        for i in 0..STATE_LANES {
            assert_eq!(z[OUT_WORD + i], expected[i], "out[{i}] mismatch");
            assert_eq!(z[IN_WORD + i], input[i], "in[{i}] mismatch");
        }
    }

    #[test]
    fn honest_witness_satisfies_r1cs() {
        let mut rng = Rng::new(0x5A7157);
        for n in [1usize, 5, 8] {
            let instances: Vec<Instance> = (0..n).map(|_| random_instance(&mut rng)).collect();
            let z = generate_witness(&instances, 3);
            assert!(satisfies(&z, 3), "witness for {n} steps fails R1CS");
        }
    }

    #[test]
    fn mutated_witness_fails() {
        let mut rng = Rng::new(0x5ADEAD);
        let mut z = generate_witness(&[random_instance(&mut rng)], 3);
        assert!(satisfies(&z, 3));
        // A product in the first and in the last round, an output bit, an input
        // bit: each breaks some row.
        for bit in [
            prod_word(0, 3) * LANE_BITS + 5,
            prod_word(N_ROUNDS - 1, 24) * LANE_BITS + 63,
            out_bit(7, 11),
            in_bit(END_LANE, 63),
        ] {
            z[bit] ^= true;
            assert!(!satisfies(&z, 3), "tampered bit {bit} should violate R1CS");
            z[bit] ^= true;
        }
        assert!(satisfies(&z, 3), "restoring every bit should re-satisfy");
    }

    /// The all-zero witness must not satisfy the system: the constant-wire pin
    /// is what rules it out, and it is the reason padding slots carry a real
    /// instance.
    #[test]
    fn const_pin_all_zero_rejected() {
        use crate::lincheck::LincheckCircuit;
        assert_eq!(WalkLincheckCircuit.const_pin_col(), Z_CONST_POS);
        let z_zero = vec![false; K << 3];
        assert!(satisfies(&z_zero, 3), "homogeneous rows accept zero without the pin");
        let z = generate_witness(&[padding_instance()], 3);
        assert!(z[Z_CONST_POS], "the pinned constant wire must be 1 in every block");
    }

    /// The backward walk is the transpose of the forward one:
    /// `⟨A_0ᵀ u, w⟩ = uᵀ A_0 w` and likewise for B, at random `u` and `w`.
    #[test]
    fn marginal_walk_transposes_the_forward_walk() {
        let mut rng = Rng::new(0x7A25);
        let mut rand_vec = || -> Vec<F192> {
            (0..K)
                .map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64()))
                .collect()
        };
        let (u, w) = (rand_vec(), rand_vec());
        let (fa, fb) = bilinear_walk_pair(&u, &w);
        let (ma, mb) = marginal_walk_pair(&u);
        let dot = |m: &[F192]| m.iter().zip(&w).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
        assert_eq!(dot(&ma), fa, "A side");
        assert_eq!(dot(&mb), fb, "B side");
    }
}
