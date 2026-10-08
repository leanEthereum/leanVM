//! The BLAKE2s compression as one R1CS instance: the 16-word state set-up, all ten rounds, and the finalization.
//!
//! Each instance proves one `compress(h, m, t, f0, f1) -> h'`.
//!
//! BLAKE2s's G mixes the same lanes with the same rotations, 16, 12, 8 and 7, in each of its ten rounds.
//! Ten rounds make 80 G calls, and the block is `2^14` bits, so the slot budget is tight:
//!
//! ```text
//!     16,384 slots - 1,280 prefix                          = 15,104 for G blocks
//!     80 G x 250 (a stride pinning b and d)                 = 20,000   over by 4,896
//!     80 G x 186 (unpinned, chained three-operand adds)    = 14,880   fits, 224 spare
//!     80 G x 184 (unpinned, fused three-operand adds)      = 14,720   fits, 384 spare
//! ```
//!
//! `184 = 61 + 31 + 61 + 31` is the product floor for the four additions of one G.
//! A 32-bit two-operand addition needs 31 products at least, a three-operand one 61.
//! So this encoding is the smallest possible at ten rounds.
//!
//! No word is pinned between rounds: every lane's affine form cascades through all ten.
//! Pinning `b` and `d` per G would cost the 250-slot stride above.
//! Resetting the cascade at one round boundary would materialize 16 lanes, 512 slots against the 384 spare.
//! The substituted matrices are therefore far too dense to build, and nothing ever builds them.
//! The two directions a proof needs are walks of the circuit: forwards for the verifier, backwards for the prover.
//! So density costs nothing, which makes the slot-minimal encoding the right trade (doc/leanvm, Annex C).
//!
//! One compression's witness, `k_log = 14`:
//!
//! ```text
//!     z[0      ..    256)     h[0..8], the input chaining value (free)
//!     z[256    ..    512)     out[0..8] = h[i] ^ v[i] ^ v[i + 8]
//!     z[512]                  1, the constant wire
//!     z[513    ..    640)     padding, forced to zero by empty rows
//!     z[640    ..  1,152)     m[0..16], sixteen 32-bit words (free)
//!     z[1,152  ..  1,184)     t_lo (free)
//!     z[1,184  ..  1,216)     t_hi (free)
//!     z[1,216  ..  1,248)     f0 (free)
//!     z[1,248  ..  1,280)     f1 (free)
//!     z[1,280  .. 16,000)     80 G blocks of 184 bits each
//!     z[16,000 .. 16,384)     padding, forced to zero by empty rows
//! ```
//!
//! One G block, all products, no word materialized:
//!
//! ```text
//!     [0   .. 31)     majority products of a + b + mx            -> a_1
//!     [31  .. 61)     ripple products of the same addition
//!     [61  .. 92)     carry products of c + d_1                  -> c_1
//!     [92  .. 123)    majority products of a_1 + b_1 + my        -> a_new
//!     [123 .. 153)    ripple products of the same addition
//!     [153 .. 184)    carry products of c_1 + d_2                -> c_new
//! ```
//!
//! `h` and `out` each fill one aligned 256-bit slot, so an embedding protocol can open a chaining step with one tensor opening.
//! Nothing else is materialized: every intermediate word, state write and message schedule stays an affine form in its consumers.
//!
//! Every slot is the output of exactly one row, `C = I`.
//! The rows are the constant wire, the free inputs, the `out` words, and the additions' products.
//!
//! The inputs `h`, `m`, `t` and the flags are free witness bits.
//! Pinning them to a caller's values is the embedding protocol's job, by openings at fixed slots.

use primitives::field::F192;
use primitives::hash::{G_LANES, IV, SIGMA};

use crate::gf2::{ADD3_BITS, CARRY_BITS_PER_ADD, Marginal, MatrixSide, RowValues, WireWord};
use crate::lincheck::LincheckCircuit;
use crate::reduction::Block;
use crate::witness::{Batch, Witness};

pub use crate::zerocheck::K_SKIP;

/// The base-two logarithm of an instance's bits: one compression takes `2^14 = 16,384` slots.
pub const K_LOG: usize = 14;

/// The slots of one instance.
pub const K: usize = 1 << K_LOG;

/// BLAKE2s rounds.
pub(crate) const N_ROUNDS: usize = primitives::hash::ROUNDS;

/// G calls per round: four on the columns, four on the diagonals.
pub(crate) const N_G_PER_ROUND: usize = 8;

/// G calls per compression: 80.
pub(crate) const N_G: usize = N_ROUNDS * N_G_PER_ROUND;

/// Bits per BLAKE2s word.
pub(crate) const WORD_BITS: usize = crate::gf2::WORD_BITS;

/// Slots per G block: two fused three-operand additions and two two-operand ones, 184.
pub(crate) const G_STRIDE: usize = 2 * ADD3_BITS + 2 * CARRY_BITS_PER_ADD;

/// One 256-bit chaining value, a power of two, so `h` and `out` are aligned slots.
pub const SLOT_BITS: usize = 256;

/// The input chaining value, slot 0.
pub(crate) const CV_BASE: usize = 0;

/// The compression's result, slot 1.
pub(crate) const OUT_BASE: usize = SLOT_BITS;

/// The constant wire, 512.
pub(crate) const Z_CONST_POS: usize = 2 * SLOT_BITS;

/// The 512-bit message block, 128-aligned past the constant: 640.
pub(crate) const MSG_BASE: usize = (Z_CONST_POS + 1).div_ceil(128) * 128;

/// The low counter word, 1,152.
pub(crate) const COUNTER_LO_BASE: usize = MSG_BASE + 16 * WORD_BITS;

/// The high counter word, 1,184.
pub(crate) const COUNTER_HI_BASE: usize = COUNTER_LO_BASE + WORD_BITS;

/// The final-block flag, 1,216.
pub(crate) const FINAL_BASE: usize = COUNTER_HI_BASE + WORD_BITS;

/// The last-node flag, 1,248.
pub(crate) const LAST_NODE_BASE: usize = FINAL_BASE + WORD_BITS;

/// The first G block, 1,280.
pub(crate) const GS_BASE: usize = LAST_NODE_BASE + WORD_BITS;

/// The slots before the zero padding, 16,000.
pub(crate) const USEFUL_BITS: usize = GS_BASE + N_G * G_STRIDE;

const _: () = assert!(USEFUL_BITS <= K, "BLAKE2s does not fit the 2^K_LOG block");

// Sub-blocks of one G block: a fused addition owns two runs, majorities then ripple; a two-operand one owns one.

/// `a + b + mx -> a_1`.
const G_ADD3_A1: usize = 0;

/// `c + d_1 -> c_1`.
const G_ADD_C1: usize = G_ADD3_A1 + ADD3_BITS;

/// `a_1 + b_1 + my -> a_new`.
const G_ADD3_A2: usize = G_ADD_C1 + CARRY_BITS_PER_ADD;

/// `c_1 + d_2 -> c_new`.
const G_ADD_C2: usize = G_ADD3_A2 + ADD3_BITS;

/// The slot of bit `b` of chaining word `w`.
#[inline]
fn h_bit(w: usize, b: usize) -> usize {
    debug_assert!(w < 8 && b < WORD_BITS);
    CV_BASE + WORD_BITS * w + b
}

/// The slot of bit `b` of message word `i`.
#[inline]
fn m_bit(i: usize, b: usize) -> usize {
    debug_assert!(i < 16 && b < WORD_BITS);
    MSG_BASE + WORD_BITS * i + b
}

/// The slot of bit `b` of output word `w`.
#[inline]
fn out_bit(w: usize, b: usize) -> usize {
    debug_assert!(w < 8 && b < WORD_BITS);
    OUT_BASE + WORD_BITS * w + b
}

/// The first slot of sub-block `off` of G call `g`.
#[inline]
fn g_slot(g: usize, off: usize) -> usize {
    debug_assert!(g < N_G && off < G_STRIDE);
    GS_BASE + G_STRIDE * g + off
}

/// The working state a compression starts from.
///
/// ```text
///     v[0..8]     h
///     v[8..12]    IV[0..4]
///     v[12..16]   IV[4..8] ^ (t_lo, t_hi, f0, f1)
/// ```
fn initial_state(h: &[u32; 8], t: u64, f0: u32, f1: u32) -> [u32; 16] {
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..12].copy_from_slice(&IV[..4]);
    v[12] = IV[4] ^ (t as u32);
    v[13] = IV[5] ^ ((t >> 32) as u32);
    v[14] = IV[6] ^ f0;
    v[15] = IV[7] ^ f1;
    v
}

/// One compression's input: `(h, m, t, f0, f1)`.
pub type Compression = ([u32; 8], [u32; 16], u64, u32, u32);

/// BLAKE2s-256's initial chaining value: the IV with the parameter block folded into word 0.
///
/// The parameter block is a 32-byte digest, no key, fanout and depth one.
pub(crate) const fn param_iv() -> [u32; 8] {
    primitives::hash::PARAM_IV
}

/// The byte counter of a single 64-byte block.
pub(crate) const PINNED_T: u64 = 64;

/// The final-block flag: a one-block message is also its last block.
pub(crate) const PINNED_F0: u32 = u32::MAX;

/// The one-block standard hash of `m`: exactly `blake2s(m)` for a 64-byte message.
///
/// That is the configuration the VM's compression instruction and the transcript use.
/// The circuit itself takes any chaining value, counter and flags.
pub const fn pinned_compression(m: [u32; 16]) -> Compression {
    (param_iv(), m, PINNED_T, PINNED_F0, 0)
}

/// The padding instance, `blake2s(0^64)`.
///
/// It fills the slots past the rows, so every instance is a real one whose constant wire is one, as the lincheck's pin requires.
pub(crate) const fn padding_block() -> Compression {
    pinned_compression([0u32; 16])
}

/// The BLAKE2s circuit as the lincheck reads it: walked forwards for the verifier, backwards for the prover.
///
/// Neither side ever builds the substituted matrices.
/// The row assignment both walks encode is the one of doc/leanvm, Annex C, "Evaluating the matrices".
pub(crate) struct Blake2sCircuit;

impl Blake2sCircuit {
    /// The matrix-vector products `(A_0 w, B_0 w)`, every row's inner product with `w`, by one forward walk.
    ///
    /// That takes additions linear in the circuit, and neither matrix is built.
    pub(crate) fn row_values(w: &[F192]) -> (Vec<F192>, Vec<F192>) {
        assert_eq!(w.len(), K);
        let mut rows = RowValues::new(w, Z_CONST_POS);
        Self::walk_forward(&mut rows);
        (rows.a, rows.b)
    }

    /// One forward pass of the circuit against the column weights, storing every row's operand pair.
    fn walk_forward(rows: &mut RowValues<'_>) {
        // Phase 1: the constant and the free inputs, each a row `[slot] * [constant]`.
        for (base, len) in [
            (Z_CONST_POS, 1),
            (CV_BASE, 8 * WORD_BITS),
            (MSG_BASE, 16 * WORD_BITS),
            (COUNTER_LO_BASE, 4 * WORD_BITS),
        ] {
            for slot in base..base + len {
                rows.bconst(slot, rows.column(slot));
            }
        }

        // Phase 2: the initial state as affine words of the inputs and the constant.
        let mut state = [WireWord::ZERO; 16];
        for (wd, lane) in state[..8].iter_mut().enumerate() {
            *lane = rows.committed(h_bit(wd, 0));
        }
        for i in 0..4 {
            state[8 + i] = rows.constant(IV[i]);
        }
        for (i, base) in [COUNTER_LO_BASE, COUNTER_HI_BASE, FINAL_BASE, LAST_NODE_BASE]
            .into_iter()
            .enumerate()
        {
            state[12 + i] = rows.constant(IV[4 + i]) ^ rows.committed(base);
        }

        // Phase 3: the ten rounds; only the additions make rows, the XORs and rotations stay affine.
        for (r, sigma) in SIGMA.iter().enumerate() {
            for g_in_round in 0..N_G_PER_ROUND {
                let g = r * N_G_PER_ROUND + g_in_round;
                let [la, lb, lc, ld] = G_LANES[g_in_round];
                let (a, b, c, d) = (state[la], state[lb], state[lc], state[ld]);
                let mx = rows.committed(m_bit(sigma[2 * g_in_round], 0));
                let my = rows.committed(m_bit(sigma[2 * g_in_round + 1], 0));

                let a_1 = rows.add3(&a, &b, &mx, g_slot(g, G_ADD3_A1));
                let d_1 = (d ^ a_1).rotate_right(16);
                let c_1 = rows.add(&c, &d_1, g_slot(g, G_ADD_C1));
                let b_1 = (b ^ c_1).rotate_right(12);
                let a_2 = rows.add3(&a_1, &b_1, &my, g_slot(g, G_ADD3_A2));
                let d_2 = (d_1 ^ a_2).rotate_right(8);
                let c_2 = rows.add(&c_1, &d_2, g_slot(g, G_ADD_C2));
                let b_2 = (b_1 ^ c_2).rotate_right(7);

                state[la] = a_2;
                state[lb] = b_2;
                state[lc] = c_2;
                state[ld] = d_2;
            }
        }

        // Phase 4: the finalization `out[w] = h[w] ^ v[w] ^ v[w + 8]`, the only committed affine words.
        for wd in 0..8 {
            let out = state[wd] ^ state[wd + 8] ^ rows.committed(h_bit(wd, 0));
            for (i, &bit) in out.bits().iter().enumerate() {
                rows.bconst(out_bit(wd, i), bit);
            }
        }
    }

    /// One matrix's column marginal `D_0^T u`, by one backward walk of the circuit.
    ///
    /// ```text
    ///     M[j] = sum_k D_0(k, j) u[k],     j < K
    /// ```
    fn marginal(side: MatrixSide, u: &[F192]) -> Vec<F192> {
        assert_eq!(u.len(), K);
        let mut m = Marginal::new(side, u);
        // The row weights whose `B` side is the lone constant wire: the free inputs and the `out` words, added at the end.
        let mut u_bconst = F192::ZERO;

        // Phase 1: the free-input rows, `A = [slot]`, `B = [constant]`.
        for (base, len) in [
            (CV_BASE, 8 * WORD_BITS),
            (MSG_BASE, 16 * WORD_BITS),
            (COUNTER_LO_BASE, 4 * WORD_BITS),
        ] {
            for s in base..base + len {
                let (a, b) = m.row(s);
                m.deposit(s, a);
                u_bconst += b;
            }
        }

        // Phase 2: the finalization rows, `A = h[w] ^ v[w] ^ v[w + 8]`, `B = [constant]`.
        // Their `A` side seeds the lane adjoints, and reaches the `h` leaf directly.
        let mut adj = [WireWord::ZERO; 16];
        for wd in 0..8 {
            let seed = WireWord::from_fn(|i| {
                let (a, b) = m.row(out_bit(wd, i));
                u_bconst += b;
                a
            });
            adj[wd] ^= seed;
            adj[wd + 8] ^= seed;
            m.deposit_word(h_bit(wd, 0), &seed);
        }

        // Phase 3: the ten rounds backwards.
        // Within one G the reverse topological order is b_2, c_2, d_2, a_2, b_1, c_1, d_1, a_1.
        // So every lane's adjoint is complete before the gadget that produced it is transposed.
        for (r, sigma) in SIGMA.iter().enumerate().rev() {
            for g_in_round in (0..N_G_PER_ROUND).rev() {
                let g = r * N_G_PER_ROUND + g_in_round;
                let [la, lb, lc, ld] = G_LANES[g_in_round];
                let (mut aa2, ab2, mut ac2, mut ad2) = (adj[la], adj[lb], adj[lc], adj[ld]);

                // b_2 = rotr(b_1 ^ c_2, 7)
                let mut ab1 = ab2.rotate_left(7);
                ac2 ^= ab1;
                // c_2 = c_1 + d_2
                let (mut ac1, ad2_c2) = m.add(&ac2, g_slot(g, G_ADD_C2));
                ad2 ^= ad2_c2;
                // d_2 = rotr(d_1 ^ a_2, 8)
                let mut ad1 = ad2.rotate_left(8);
                aa2 ^= ad1;
                // a_2 = a_1 + b_1 + my
                let (mut aa1, ab1_a2, amy) = m.add3(&aa2, g_slot(g, G_ADD3_A2));
                ab1 ^= ab1_a2;
                m.deposit_word(m_bit(sigma[2 * g_in_round + 1], 0), &amy);
                // b_1 = rotr(b ^ c_1, 12)
                let mut ab = ab1.rotate_left(12);
                ac1 ^= ab;
                // c_1 = c + d_1
                let (ac, ad1_c1) = m.add(&ac1, g_slot(g, G_ADD_C1));
                ad1 ^= ad1_c1;
                // d_1 = rotr(d ^ a_1, 16)
                let ad = ad1.rotate_left(16);
                aa1 ^= ad;
                // a_1 = a + b + mx
                let (aa, ab_a1, amx) = m.add3(&aa1, g_slot(g, G_ADD3_A1));
                ab ^= ab_a1;
                m.deposit_word(m_bit(sigma[2 * g_in_round], 0), &amx);

                adj[la] = aa;
                adj[lb] = ab;
                adj[lc] = ac;
                adj[ld] = ad;
            }
        }

        // Phase 4: the initial state, whose set constant bits read the constant wire.
        for (wd, lane) in adj[..8].iter().enumerate() {
            m.deposit_word(h_bit(wd, 0), lane);
        }
        let mut const_adj = (0..4).fold(F192::ZERO, |acc, i| acc + adj[8 + i].at_constant(IV[i]));
        for (i, base) in [COUNTER_LO_BASE, COUNTER_HI_BASE, FINAL_BASE, LAST_NODE_BASE]
            .into_iter()
            .enumerate()
        {
            m.deposit_word(base, &adj[12 + i]);
            const_adj += adj[12 + i].at_constant(IV[4 + i]);
        }

        // The constant row itself, plus the `B` side every non-product row shares.
        let constant_row = m.weight(Z_CONST_POS);
        m.deposit(Z_CONST_POS, const_adj + constant_row + u_bconst);
        m.into_columns()
    }
}

impl LincheckCircuit for Blake2sCircuit {
    fn n_cols(&self) -> usize {
        K
    }

    fn const_pin_col(&self) -> usize {
        Z_CONST_POS
    }

    /// `(A_0 + alpha B_0)^T u`, one backward walk per matrix.
    fn fold_alpha_batched(&self, alpha: F192, u: &[F192]) -> Vec<F192> {
        let mut a = Self::marginal(MatrixSide::A, u);
        for (a, b) in a.iter_mut().zip(Self::marginal(MatrixSide::B, u)) {
            *a += alpha * b;
        }
        a
    }

    /// `u^T A_0 w + alpha u^T B_0 w`, by one forward walk contracted with the row weights.
    fn bilinear_form(&self, alpha: F192, u: &[F192], w: &[F192]) -> Option<F192> {
        assert_eq!(u.len(), K);
        let (a, b) = Self::row_values(w);
        Some((u.iter().zip(a.iter().zip(&b))).fold(F192::ZERO, |acc, (&u, (&a, &b))| acc + u * (a + alpha * b)))
    }
}

/// OR the low 32 bits of `val` into `buf` from bit `bit_off`, straddling two words when it must.
#[inline(always)]
const fn or_u32_at_bit(buf: &mut [u64], bit_off: usize, val: u32) {
    let u64_idx = bit_off >> 6;
    let shift = bit_off & 63;
    buf[u64_idx] |= (val as u64) << shift;
    // Past bit 32 of a word, the value's high bits spill into the next.
    if shift > 32 {
        buf[u64_idx + 1] |= (val as u64) >> (64 - shift);
    }
}

/// Set bit `bit_off` of `buf`, low bit first within each word.
#[inline(always)]
const fn or_bit_at(buf: &mut [u64], bit_off: usize) {
    buf[bit_off >> 6] |= 1u64 << (bit_off & 63);
}

/// A record of `64 NW` bits built in registers, then ORed into the block once.
struct BitRecord<const NW: usize> {
    w: [u64; NW],
}

impl<const NW: usize> BitRecord<NW> {
    #[inline(always)]
    const fn new() -> Self {
        Self { w: [0u64; NW] }
    }

    /// OR a masked value into the record from bit `POS`.
    ///
    /// `POS` is a constant, so the straddle branch and the shifts fold at compile time.
    #[inline(always)]
    const fn push<const POS: usize>(&mut self, val: u32) {
        let v = val as u64;
        let idx = POS >> 6;
        let s = POS & 63;
        self.w[idx] |= v << s;
        if s > 32 {
            self.w[idx + 1] |= v >> (64 - s);
        }
    }

    /// OR the record into `buf` from bit `base_bit`.
    #[inline(always)]
    pub(crate) fn flush(&self, buf: &mut [u64], base_bit: usize) {
        let bi = base_bit >> 6;
        let s = base_bit & 63;
        // Each word's high bits spill into the next.
        let mut spill = 0u64;
        for j in 0..NW {
            buf[bi + j] |= (self.w[j] << s) | spill;
            // `(x >> 1) >> (63 - s)` is `x >> (64 - s)` without a shift by 64 at `s = 0`.
            spill = (self.w[j] >> 1) >> (63 - s);
        }
        buf[bi + NW] |= spill;
    }
}

/// One two-operand addition's witness: `(sum, left, right, carry_aux)`.
///
/// The three row words are masked to bits 0 to 30: bit 31's carry-out falls off the modulus `2^32`.
#[inline(always)]
const fn add_carry_parts(x: u32, y: u32) -> (u32, u32, u32, u32) {
    const MASK_LO31: u32 = 0x7FFF_FFFF;
    let sum = x.wrapping_add(y);
    // Bit `i` of `sum ^ x ^ y` is the carry into bit `i`.
    let cin = sum ^ x ^ y;
    let left = (x ^ cin) & MASK_LO31;
    let right = (y ^ cin) & MASK_LO31;
    let carry_aux = left & right;
    (sum, left, right, carry_aux)
}

/// One fused three-operand addition's witness: the sum, then each layer's `(left, right, product)`.
///
/// - The majority layer is masked to bits 0 to 30.
/// - The ripple layer is masked to bits 1 to 30 and shifted down one, so its slot `j` holds bit `j + 1`.
#[inline(always)]
const fn add3_fused_parts(x: u32, y: u32, z: u32) -> (u32, (u32, u32, u32), (u32, u32, u32)) {
    const MASK_LO31: u32 = 0x7FFF_FFFF;
    const MASK_LO30: u32 = 0x3FFF_FFFF;
    let maj_left = (x ^ z) & MASK_LO31;
    let maj_right = (y ^ z) & MASK_LO31;
    let maj_aux = maj_left & maj_right;
    // The carry-save sum: `p + 2 maj`, where `maj_i = maj_aux_i ^ z_i` is the bitwise majority.
    let p = x ^ y ^ z;
    let q = (maj_aux ^ (z & MASK_LO31)) << 1;
    let sum = p.wrapping_add(q);
    let cin = sum ^ p ^ q;
    let rip_left = ((p ^ cin) >> 1) & MASK_LO30;
    let rip_right = ((q ^ cin) >> 1) & MASK_LO30;
    let rip_aux = rip_left & rip_right;
    (sum, (maj_left, maj_right, maj_aux), (rip_left, rip_right, rip_aux))
}

/// Write a 32-bit input or affine word: `z = a = val`, `b = 1`.
///
/// No `c` is written: `C = I`, so `c` is `z`.
#[inline]
const fn write_lin_word_ab_packed(bit_off: usize, val: u32, z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    or_u32_at_bit(z, bit_off, val);
    or_u32_at_bit(a, bit_off, val);
    or_u32_at_bit(b, bit_off, 0xFFFF_FFFF);
}

/// The majority rows of `a + b + mx`, inside one G's record.
const REC_MAJ_A1: usize = G_ADD3_A1;

/// The ripple rows of `a + b + mx`.
const REC_RIP_A1: usize = G_ADD3_A1 + CARRY_BITS_PER_ADD;

/// The carry rows of `c + d_1`.
const REC_C1: usize = G_ADD_C1;

/// The majority rows of `a_1 + b_1 + my`.
const REC_MAJ_A2: usize = G_ADD3_A2;

/// The ripple rows of `a_1 + b_1 + my`.
const REC_RIP_A2: usize = G_ADD3_A2 + CARRY_BITS_PER_ADD;

/// The carry rows of `c_1 + d_2`.
const REC_C2: usize = G_ADD_C2;

// One G's rows are built in three 192-bit records, so its stride and last sub-block fit 192 bits.
const _: () = assert!(G_STRIDE <= 3 * 64 && REC_C2 < 3 * 64);

/// One G's rows of `z`, `A z` and `B z`, built in registers.
struct GRecords {
    z: BitRecord<3>,
    a: BitRecord<3>,
    b: BitRecord<3>,
}

impl GRecords {
    #[inline(always)]
    const fn new() -> Self {
        Self {
            z: BitRecord::new(),
            a: BitRecord::new(),
            b: BitRecord::new(),
        }
    }

    /// One two-operand addition's carry rows from bit `POS`, returning its sum.
    #[inline(always)]
    const fn add<const POS: usize>(&mut self, x: u32, y: u32) -> u32 {
        let (sum, left, right, carry) = add_carry_parts(x, y);
        self.z.push::<POS>(carry);
        self.a.push::<POS>(left);
        self.b.push::<POS>(right);
        sum
    }

    /// One fused three-operand addition's majority rows from `MAJ` and ripple rows from `RIP`, returning its sum.
    #[inline(always)]
    const fn add3<const MAJ: usize, const RIP: usize>(&mut self, x: u32, y: u32, z: u32) -> u32 {
        let (sum, maj, rip) = add3_fused_parts(x, y, z);
        self.z.push::<MAJ>(maj.2);
        self.a.push::<MAJ>(maj.0);
        self.b.push::<MAJ>(maj.1);
        self.z.push::<RIP>(rip.2);
        self.a.push::<RIP>(rip.0);
        self.b.push::<RIP>(rip.1);
        sum
    }
}

/// One compression's `z`, `A z` and `B z`, into its instance's `K / 64` words of each table, zeroed on entry.
///
/// No `c` table is built: `C = I`, so `c` is `z`.
fn build_block_witness_ab_packed_into(
    &(ref h, ref m, t, f0, f1): &Compression,
    z: &mut [u64],
    a: &mut [u64],
    b: &mut [u64],
) {
    const U64_PER_BLOCK: usize = K / 64;
    debug_assert_eq!(z.len(), U64_PER_BLOCK);
    debug_assert_eq!(a.len(), U64_PER_BLOCK);
    debug_assert_eq!(b.len(), U64_PER_BLOCK);

    // Phase 1: the constant wire and the free inputs.
    or_bit_at(z, Z_CONST_POS);
    or_bit_at(a, Z_CONST_POS);
    or_bit_at(b, Z_CONST_POS);
    for (w, &word) in h.iter().enumerate() {
        write_lin_word_ab_packed(h_bit(w, 0), word, z, a, b);
    }
    for (i, &word) in m.iter().enumerate() {
        write_lin_word_ab_packed(m_bit(i, 0), word, z, a, b);
    }
    write_lin_word_ab_packed(COUNTER_LO_BASE, t as u32, z, a, b);
    write_lin_word_ab_packed(COUNTER_HI_BASE, (t >> 32) as u32, z, a, b);
    write_lin_word_ab_packed(FINAL_BASE, f0, z, a, b);
    write_lin_word_ab_packed(LAST_NODE_BASE, f1, z, a, b);

    // Phase 2: the ten rounds, each G's rows built in registers then ORed in at its block.
    let mut v = initial_state(h, t, f0, f1);
    for (r, sigma) in SIGMA.iter().enumerate() {
        for g_in_round in 0..N_G_PER_ROUND {
            let g = r * N_G_PER_ROUND + g_in_round;
            let [la, lb, lc, ld] = G_LANES[g_in_round];
            let mx = m[sigma[2 * g_in_round]];
            let my = m[sigma[2 * g_in_round + 1]];
            let (a_val, b_val, c_val, d_val) = (v[la], v[lb], v[lc], v[ld]);

            let mut rec = GRecords::new();
            let a_1 = rec.add3::<REC_MAJ_A1, REC_RIP_A1>(a_val, b_val, mx);
            let d_1 = (d_val ^ a_1).rotate_right(16);
            let c_1 = rec.add::<REC_C1>(c_val, d_1);
            let b_1 = (b_val ^ c_1).rotate_right(12);
            let a_2 = rec.add3::<REC_MAJ_A2, REC_RIP_A2>(a_1, b_1, my);
            let d_2 = (d_1 ^ a_2).rotate_right(8);
            let c_2 = rec.add::<REC_C2>(c_1, d_2);
            let b_2 = (b_1 ^ c_2).rotate_right(7);

            let g_base = GS_BASE + G_STRIDE * g;
            rec.z.flush(z, g_base);
            rec.a.flush(a, g_base);
            rec.b.flush(b, g_base);

            v[la] = a_2;
            v[lb] = b_2;
            v[lc] = c_2;
            v[ld] = d_2;
        }
    }

    // Phase 3: the finalization words.
    for w in 0..8 {
        write_lin_word_ab_packed(out_bit(w, 0), h[w] ^ v[w] ^ v[w + 8], z, a, b);
    }
}

/// The witness of `blocks.len()` compressions, padded to `2^n_blocks_log` instances.
pub fn witness(blocks: &[Compression], n_blocks_log: usize) -> Witness {
    let batch = Batch {
        n_blocks_log,
        k_log: K_LOG,
    };
    batch.witness(|z| {
        batch.fill_instances(
            z,
            blocks,
            &padding_block(),
            build_block_witness_ab_packed_into,
            |_, _| {},
        )
    })
}

/// The BLAKE2s circuit as the reduction sees it.
pub const BLOCK: Block<'static> = Block {
    k_log: K_LOG,
    useful_bits: USEFUL_BITS,
    circuit: &Blake2sCircuit,
};

#[cfg(test)]
mod tests {
    use primitives::hash::compress;
    use primitives::test_util::Rng;

    use super::*;

    /// Whether `z`, `2^n_blocks_log` blocks of `K` bits, satisfies `(A_0 z) * (B_0 z) = z` in every block.
    fn satisfies(z: &[bool], n_blocks_log: usize) -> bool {
        assert_eq!(z.len(), K << n_blocks_log, "z must be one K-bit block per instance");
        let bit = |b: bool| if b { F192::ONE } else { F192::ZERO };
        (0..1usize << n_blocks_log).all(|t| {
            // The forward walk gives each row's two factors; no matrix is built.
            let block: Vec<F192> = z[t * K..(t + 1) * K].iter().map(|&b| bit(b)).collect();
            let (a, b) = Blake2sCircuit::row_values(&block);
            (0..K).all(|k| a[k] * b[k] == block[k])
        })
    }

    /// The first `n_bits` bits of a packed witness.
    fn unpack_bits(z: &[u64], n_bits: usize) -> Vec<bool> {
        (0..n_bits).map(|i| (z[i / 64] >> (i % 64)) & 1 == 1).collect()
    }

    /// The witness bits of `blocks`, padded to `2^n_blocks_log` instances.
    fn witness_bits(blocks: &[Compression], n_blocks_log: usize) -> Vec<bool> {
        let z = witness(blocks, n_blocks_log).z;
        unpack_bits(&z, (1usize << n_blocks_log) * K)
    }

    #[test]
    fn constrained_rows_tile_the_layout() {
        // Invariant: every slot a layout region claims is the output of one non-empty row, every other slot padding.
        //
        // An overlap would leave a product unconstrained while the overwritten row stays non-empty.
        // Only the whole tiling catches it.
        let mut rng = Rng::new(0x7113D);
        let w: Vec<F192> = (0..K)
            .map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64()))
            .collect();
        let (va, vb) = Blake2sCircuit::row_values(&w);

        // Fixture state: the regions of the layout, none claimed twice.
        let mut expected = vec![false; K];
        let mut claim = |base: usize, len: usize| {
            for (offset, slot) in expected[base..base + len].iter_mut().enumerate() {
                let s = base + offset;
                assert!(!*slot, "slot {s} is claimed by two layout regions");
                *slot = true;
            }
        };
        claim(CV_BASE, 8 * WORD_BITS);
        claim(OUT_BASE, 8 * WORD_BITS);
        claim(Z_CONST_POS, 1);
        claim(MSG_BASE, 16 * WORD_BITS);
        claim(COUNTER_LO_BASE, 4 * WORD_BITS);
        claim(GS_BASE, N_G * G_STRIDE);

        // At a random `w`, a non-empty row is nonzero but with probability `2^-192`.
        for s in 0..K {
            let constrained = va[s] != F192::ZERO || vb[s] != F192::ZERO;
            assert_eq!(constrained, expected[s], "slot {s}");
        }
    }

    #[test]
    fn witness_encodes_correct_output() {
        // Invariant: the committed `out` words are the reference compression's result.
        let mut rng = Rng::new(0xB25C0DE);
        let h: [u32; 8] = std::array::from_fn(|_| rng.next_u32());
        let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
        let blocks = vec![(h, m, 0x1234_5678_9ABC_DEF0u64, u32::MAX, 0u32)];
        let z = witness_bits(&blocks, 3);
        let mut expected = h;
        compress(&mut expected, &m, 0x1234_5678_9ABC_DEF0, true);
        for (w, &want) in expected.iter().enumerate() {
            let got = (0..WORD_BITS).fold(0u32, |acc, b| acc | (u32::from(z[out_bit(w, b)]) << b));
            assert_eq!(got, want, "out[{w}]");
        }
    }

    #[test]
    fn honest_witness_satisfies_r1cs() {
        // Invariant: an honest batch satisfies every row, padding instances included.
        //
        // Fixture state: one, five and eight compressions in a batch of eight, mixed flags and counters.
        let mut rng = Rng::new(0xB25A7157);
        for n_blocks in [1usize, 5, 8] {
            let blocks: Vec<Compression> = (0..n_blocks)
                .map(|i| {
                    (
                        std::array::from_fn(|_| rng.next_u32()),
                        std::array::from_fn(|_| rng.next_u32()),
                        64 * (i as u64 + 1),
                        if i % 2 == 0 { u32::MAX } else { 0 },
                        0,
                    )
                })
                .collect();
            let z = witness_bits(&blocks, 3);
            assert_eq!(z.len(), K << 3);
            assert!(satisfies(&z, 3), "witness for {n_blocks} compressions fails R1CS");
        }
    }

    #[test]
    fn mutated_witness_fails() {
        // Invariant: one flipped product bit breaks a row.
        //
        // Mutation: a bit in each layer of a fused addition and one in a two-operand addition.
        // All sit in the last round, where the affine cascade is deepest.
        let mut rng = Rng::new(0xB2DEAD);
        let blocks = vec![(param_iv(), std::array::from_fn(|_| rng.next_u32()), 64, 0, 0)];
        let mut z = witness_bits(&blocks, 3);
        assert!(satisfies(&z, 3));
        for off in [G_ADD3_A2 + 5, G_ADD3_A2 + CARRY_BITS_PER_ADD + 5, G_ADD_C2 + 7] {
            z[g_slot(79, off)] ^= true;
            assert!(!satisfies(&z, 3), "a flipped product bit at {off} must break a row");
            z[g_slot(79, off)] ^= true;
        }
        assert!(satisfies(&z, 3), "restoring every bit satisfies again");
    }

    #[test]
    fn const_pin_all_zero_rejected() {
        // Invariant: every row is homogeneous, so the all-zero witness satisfies them.
        // The lincheck's constant-wire pin rules it out, which is why padding instances are real compressions.
        assert_eq!(Blake2sCircuit.const_pin_col(), Z_CONST_POS);
        let z_zero = vec![false; K << 3];
        assert!(satisfies(&z_zero, 3), "homogeneous rows accept zero without the pin");
        let z = witness_bits(&[padding_block()], 3);
        assert!(z[Z_CONST_POS], "the pinned constant wire must be one in every block");
    }
}
