//! Symbolic GF(2) words and the 32-bit adder gadgets the hash circuit uses.
//!
//! BLAKE2s is a 32-bit ARX round: its XORs and rotations are free over GF(2).
//! Its only nonlinear constraints are the product bits of the modular additions.
//! This module owns that adder algebra, apart from the hash's schedule and layout, because the subtlety lives there.
//! The fused three-operand gadget's bit-0 and bit-31 boundaries are what make the ten-round encoding fit.
//!
//! A word is 32 F192 values, one per bit.
//! Each gadget comes as a forward walk, threading the words, and a backward walk, threading their adjoints.
//! The matrices the two describe are never built:
//!
//! ```text
//!     forward    u^T A_0 w and u^T B_0 w, or per row A_0 w and B_0 w
//!     backward   the column marginal (A_0 + alpha B_0)^T u
//! ```
//!
//! The protocol cross-checks the pair: the lincheck's terminal identity is exactly the claim that the two agree.

use primitives::field::F192;

/// Bits per word.
pub(crate) const WORD_BITS: usize = 32;

/// Carry products per two-operand addition: bits 0 to 30.
///
/// Bit 31's carry-out falls off the modulus `2^32`, so it gets no slot.
pub(crate) const CARRY_BITS_PER_ADD: usize = WORD_BITS - 1;

/// Ripple products per fused three-operand addition: bits 1 to 30.
///
/// Bit 0's product is `p_0 * 0`, since the shifted majority word's bit 0 is zero.
pub(crate) const RIPPLE_BITS_PER_ADD3: usize = WORD_BITS - 2;

/// Product slots per fused three-operand addition: 31 majorities, then 30 ripple products.
pub(crate) const ADD3_BITS: usize = CARRY_BITS_PER_ADD + RIPPLE_BITS_PER_ADD3;

/// One word's wire values: bit `i` is the F192 combination `<lin_i, w>` of the column weights.
///
/// The forward walk evaluates the circuit before substitution, over F192 values.
/// A committed slot contributes `w[slot]`, an intermediate wire its running linear combination.
/// Each row's `<A_i, w>` is read off the threaded wires exactly where the row is made.
/// That costs field operations linear in the circuit, never its substituted nonzeros.
pub(crate) type WireWord = [F192; WORD_BITS];

/// The word committed at the 32 slots from `base`.
#[inline]
pub(crate) fn wire_from_slot_base(w: &[F192], base: usize) -> WireWord {
    std::array::from_fn(|i| w[base + i])
}

/// A constant word: a set bit is the constant wire's column, a clear bit nothing.
#[inline]
pub(crate) fn wire_from_const(w: &[F192], val: u32, const_pos: usize) -> WireWord {
    std::array::from_fn(|i| if (val >> i) & 1 == 1 { w[const_pos] } else { F192::ZERO })
}

/// The XOR of two words: their combinations added.
#[inline]
pub(crate) fn wire_xor(x: &WireWord, y: &WireWord) -> WireWord {
    std::array::from_fn(|i| x[i] + y[i])
}

/// A word rotated right by `n` bits.
#[inline]
pub(crate) fn wire_rotr(x: &WireWord, n: usize) -> WireWord {
    std::array::from_fn(|i| x[(i + n) % WORD_BITS])
}

/// The matrix-vector products `(A_0 w, B_0 w)`, filled row by row; a row with no gate keeps its zeros.
pub(crate) struct RowValues {
    /// `A_0 w`.
    pub(crate) a: Vec<F192>,

    /// `B_0 w`.
    pub(crate) b: Vec<F192>,

    /// The constant wire's column weight, which a row against the constant reads on its `B` side.
    wc: F192,
}

impl RowValues {
    /// `k` empty rows, the constant column weighing `wc`.
    pub(crate) fn new(k: usize, wc: F192) -> Self {
        Self {
            a: vec![F192::ZERO; k],
            b: vec![F192::ZERO; k],
            wc,
        }
    }

    /// Row `k` is the product `a * b`.
    #[inline]
    pub(crate) fn product(&mut self, k: usize, a: F192, b: F192) {
        self.a[k] = a;
        self.b[k] = b;
    }

    /// Row `k` is `a * 1`: an affine wire committed against the constant.
    #[inline]
    pub(crate) fn bconst(&mut self, k: usize, a: F192) {
        self.a[k] = a;
        self.b[k] = self.wc;
    }
}

/// Walk one 32-bit addition: report its 31 carry rows and return the sum word.
///
/// ```text
///     carry row cb + i    A = x_i + cin_i     B = y_i + cin_i
///     sum bit i           x_i + y_i + cin_i
///     cin_i               sum_{j < i} carry_aux[cb + j], a running prefix of w reads
/// ```
pub(crate) fn walk_add(sink: &mut RowValues, w: &[F192], x: &WireWord, y: &WireWord, carry_base: usize) -> WireWord {
    let mut out = [F192::ZERO; WORD_BITS];
    // The carry into the current bit, as a combination of the carry slots below it.
    let mut cin = F192::ZERO;
    for i in 0..WORD_BITS {
        let a_side = x[i] + cin;
        let b_side = y[i] + cin;
        out[i] = a_side + y[i];
        // Bit 31's carry falls off the modulus: no row, no slot.
        if i < CARRY_BITS_PER_ADD {
            sink.product(carry_base + i, a_side, b_side);
            cin += w[carry_base + i];
        }
    }
    out
}

/// Walk one fused three-operand addition: report its 31 majority rows and 30 ripple rows, and return the sum word.
///
/// ```text
///     majority row base + i        A = x_i + z_i      B = y_i + z_i      maj_i = maj_aux_i + z_i
///     ripple row rip + i - 1       A = p_i + cin_i    B = q_i + cin_i    p_i = x_i + y_i + z_i, q_i = maj_(i-1)
///     sum bit i                    p_i + q_i + cin_i
/// ```
pub(crate) fn walk_add3_fused(
    sink: &mut RowValues,
    w: &[F192],
    x: &WireWord,
    y: &WireWord,
    z: &WireWord,
    base: usize,
) -> WireWord {
    let rip_base = base + CARRY_BITS_PER_ADD;

    // Phase 1: the majority layer, the carry-save sum's carry word.
    let mut maj = [F192::ZERO; CARRY_BITS_PER_ADD];
    for i in 0..CARRY_BITS_PER_ADD {
        sink.product(base + i, x[i] + z[i], y[i] + z[i]);
        maj[i] = w[base + i] + z[i];
    }

    // Phase 2: the ripple layer adds the parity word and the majority word shifted up one bit.
    let mut out = [F192::ZERO; WORD_BITS];
    let mut cin = F192::ZERO;
    for i in 0..WORD_BITS {
        let q_i = if i == 0 { F192::ZERO } else { maj[i - 1] };
        let a_side = x[i] + y[i] + z[i] + cin;
        out[i] = a_side + q_i;
        // Bit 0 has no shifted majority to carry with, and bit 31's carry falls off the modulus.
        if (1..=RIPPLE_BITS_PER_ADD3).contains(&i) {
            sink.product(rip_base + i - 1, a_side, q_i + cin);
            cin += w[rip_base + i - 1];
        }
    }
    out
}

/// Which matrix the backward walk follows in each R1CS row.
///
/// For either matrix `D_0`, the forward walk evaluates `S(w) = u^T D_0 w`, linear in `w`.
/// So `S(w) = <M, w>` for the column marginal `M = D_0^T u`, the gradient of the walk in `w`.
/// Reverse-mode differentiation of the walk then gives the whole marginal, in field operations linear in the circuit.
///
/// Each backward gadget is the transpose of its forward one.
/// It takes the adjoint of the gadget's sum word, deposits the marginal entries of the gadget's own slots, and returns its operands' adjoints.
#[derive(Clone, Copy)]
pub(crate) enum MatrixSide {
    /// The left factors, `A_0`.
    A,

    /// The right factors, `B_0`.
    B,
}

impl MatrixSide {
    /// A row weight split onto its `(A, B)` sides: all of it on the followed side, nothing on the other.
    #[inline]
    pub(crate) const fn split(self, value: F192) -> (F192, F192) {
        match self {
            Self::A => (value, F192::ZERO),
            Self::B => (F192::ZERO, value),
        }
    }
}

/// A word rotated left by `n` bits: the transpose of the right rotation.
///
/// ```text
///     <rotr(x, n), a> = <x, rotl(a, n)>
/// ```
#[inline]
pub(crate) fn wire_rotl(x: &WireWord, n: usize) -> WireWord {
    std::array::from_fn(|i| x[(i + WORD_BITS - n) % WORD_BITS])
}

/// The transpose of the two-operand addition's walk, whose rows it must mirror exactly.
///
/// - `adj` is the adjoint of the sum word.
/// - The marginal entries of the 31 carry slots go into `m`.
/// - Returns the adjoints of `x` and `y`.
///
/// Slot `carry_base + j` is read by every `cin_i` with `i > j`.
/// So its marginal entry is the suffix sum of the `cin_i` adjoints, walked from the top bit down.
pub(crate) fn back_add(
    m: &mut [F192],
    u: &[F192],
    adj: &WireWord,
    carry_base: usize,
    side: MatrixSide,
) -> (WireWord, WireWord) {
    let mut ax = [F192::ZERO; WORD_BITS];
    let mut ay = [F192::ZERO; WORD_BITS];
    // The adjoint of every carry above the current bit, which each lower carry slot feeds.
    let mut suffix = F192::ZERO;
    for i in (0..WORD_BITS).rev() {
        // `cin_i` reaches the sum bit, then both sides of its carry row.
        let mut cin_adj = adj[i];
        if i < CARRY_BITS_PER_ADD {
            m[carry_base + i] += suffix;
            let p = u[carry_base + i];
            let (pa, pb) = side.split(p);
            ax[i] = adj[i] + pa;
            ay[i] = adj[i] + pb;
            cin_adj += pa + pb;
        } else {
            ax[i] = adj[i];
            ay[i] = adj[i];
        }
        suffix += cin_adj;
    }
    (ax, ay)
}

/// The transpose of the fused three-operand addition's walk.
///
/// - The marginal entries of the 31 majority slots and the 30 ripple slots go into `m`.
/// - Returns the adjoints of `x`, `y` and `z`.
///
/// `maj_i = maj_aux_i + z_i` feeds the ripple layer as `q_(i+1)`, so `z` and the majority slot both take its adjoint.
/// A ripple slot is read by every later `cin`, hence a suffix sum, as in the two-operand transpose.
pub(crate) fn back_add3_fused(
    m: &mut [F192],
    u: &[F192],
    adj: &WireWord,
    base: usize,
    side: MatrixSide,
) -> (WireWord, WireWord, WireWord) {
    let rip_base = base + CARRY_BITS_PER_ADD;
    let mut ax = [F192::ZERO; WORD_BITS];
    let mut ay = [F192::ZERO; WORD_BITS];
    let mut az = [F192::ZERO; WORD_BITS];
    // Ripple row weight at bit `i`, zero where the layer has no row.
    let rip = |i: usize| -> F192 {
        if (1..=RIPPLE_BITS_PER_ADD3).contains(&i) {
            u[rip_base + i - 1]
        } else {
            F192::ZERO
        }
    };
    // `q_i` is read by `out[i]` and by the ripple row's B side.
    let q_adj = |i: usize| -> F192 { adj[i] + side.split(rip(i)).1 };
    // The adjoint of every ripple carry above the current bit.
    let mut suffix = F192::ZERO;
    for i in (0..WORD_BITS).rev() {
        let ri = rip(i);
        if (1..=RIPPLE_BITS_PER_ADD3).contains(&i) {
            m[rip_base + i - 1] += suffix;
        }
        // `cin_i` reaches the sum bit and both sides of the ripple row.
        suffix += adj[i] + ri;
        // `p_i = x_i + y_i + z_i` reaches the sum bit and the ripple row's A side.
        let common = adj[i] + side.split(ri).0;
        let (mut xi, mut yi, mut zi) = (common, common, common);
        if i < CARRY_BITS_PER_ADD {
            // The majority row reads `x_i + z_i` on A and `y_i + z_i` on B.
            let mi = u[base + i];
            let (ma, mb) = side.split(mi);
            xi += ma;
            yi += mb;
            zi += ma + mb;
            // `maj_i = maj_aux_i + z_i` is the ripple layer's `q_(i+1)`.
            let qa = q_adj(i + 1);
            m[base + i] += qa;
            zi += qa;
        }
        ax[i] = xi;
        ay[i] = yi;
        az[i] = zi;
    }
    (ax, ay, az)
}
