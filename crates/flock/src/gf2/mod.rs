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

use std::ops::{BitXor, BitXorAssign, Index, IndexMut};

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
///
/// The backward walk threads adjoints through the same type: a word's adjoint is a word too.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct WireWord([F192; WORD_BITS]);

impl WireWord {
    /// The word of no wires.
    pub(crate) const ZERO: Self = Self([F192::ZERO; WORD_BITS]);

    /// The word whose bit `i` is `f(i)`.
    #[inline]
    pub(crate) fn from_fn(f: impl FnMut(usize) -> F192) -> Self {
        Self(std::array::from_fn(f))
    }

    /// The word committed at the 32 slots from `base`.
    #[inline]
    pub(crate) fn committed(w: &[F192], base: usize) -> Self {
        Self(std::array::from_fn(|i| w[base + i]))
    }

    /// A constant word: a set bit is the constant wire's column weight `wc`, a clear bit nothing.
    #[inline]
    pub(crate) fn constant(wc: F192, value: u32) -> Self {
        Self(std::array::from_fn(
            |i| if (value >> i) & 1 == 1 { wc } else { F192::ZERO },
        ))
    }

    /// The word rotated right by `n` bits, as `u32::rotate_right`.
    #[inline]
    pub(crate) fn rotate_right(self, n: usize) -> Self {
        Self(std::array::from_fn(|i| self.0[(i + n) % WORD_BITS]))
    }

    /// The word rotated left by `n` bits: the transpose of the right rotation.
    ///
    /// ```text
    ///     <x.rotate_right(n), a> = <x, a.rotate_left(n)>
    /// ```
    #[inline]
    pub(crate) fn rotate_left(self, n: usize) -> Self {
        Self(std::array::from_fn(|i| self.0[(i + WORD_BITS - n) % WORD_BITS]))
    }

    /// The constant wire's share of this adjoint word: the sum of its bits where `value` is set.
    #[inline]
    pub(crate) fn at_constant(&self, value: u32) -> F192 {
        (self.0.iter().enumerate())
            .filter(|&(i, _)| (value >> i) & 1 == 1)
            .fold(F192::ZERO, |acc, (_, &bit)| acc + bit)
    }

    /// The 32 bits, low first.
    #[inline]
    pub(crate) const fn bits(&self) -> &[F192; WORD_BITS] {
        &self.0
    }
}

/// The XOR of two words: their combinations added.
impl BitXor for WireWord {
    type Output = Self;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] + rhs.0[i]))
    }
}

impl BitXorAssign for WireWord {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl Index<usize> for WireWord {
    type Output = F192;

    #[inline]
    fn index(&self, bit: usize) -> &F192 {
        &self.0[bit]
    }
}

impl IndexMut<usize> for WireWord {
    #[inline]
    fn index_mut(&mut self, bit: usize) -> &mut F192 {
        &mut self.0[bit]
    }
}

/// The forward walk's output, the matrix-vector products `(A_0 w, B_0 w)`, filled row by row.
///
/// A row with no gate keeps its zeros.
pub(crate) struct RowValues<'a> {
    /// `A_0 w`.
    pub(crate) a: Vec<F192>,

    /// `B_0 w`.
    pub(crate) b: Vec<F192>,

    /// The column weights the walk evaluates the circuit at.
    w: &'a [F192],

    /// The constant wire's column weight, which a row against the constant reads on its `B` side.
    wc: F192,
}

impl<'a> RowValues<'a> {
    /// Empty rows, one per column weight, the constant wire at column `const_pos`.
    pub(crate) fn new(w: &'a [F192], const_pos: usize) -> Self {
        Self {
            a: vec![F192::ZERO; w.len()],
            b: vec![F192::ZERO; w.len()],
            w,
            wc: w[const_pos],
        }
    }

    /// Column `j`'s weight.
    #[inline]
    pub(crate) const fn column(&self, j: usize) -> F192 {
        self.w[j]
    }

    /// The word committed at the 32 slots from `base`.
    #[inline]
    pub(crate) fn committed(&self, base: usize) -> WireWord {
        WireWord::committed(self.w, base)
    }

    /// The constant word `value`, as the constant wire's column.
    #[inline]
    pub(crate) fn constant(&self, value: u32) -> WireWord {
        WireWord::constant(self.wc, value)
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

    /// Walk one 32-bit addition: report its 31 carry rows and return the sum word.
    ///
    /// ```text
    ///     carry row cb + i    A = x_i + cin_i     B = y_i + cin_i
    ///     sum bit i           x_i + y_i + cin_i
    ///     cin_i               sum_{j < i} carry_aux[cb + j], a running prefix of w reads
    /// ```
    pub(crate) fn add(&mut self, x: &WireWord, y: &WireWord, carry_base: usize) -> WireWord {
        let mut out = WireWord::ZERO;
        // The carry into the current bit, as a combination of the carry slots below it.
        let mut cin = F192::ZERO;
        for i in 0..WORD_BITS {
            let a_side = x[i] + cin;
            let b_side = y[i] + cin;
            out[i] = a_side + y[i];
            // Bit 31's carry falls off the modulus: no row, no slot.
            if i < CARRY_BITS_PER_ADD {
                self.product(carry_base + i, a_side, b_side);
                cin += self.w[carry_base + i];
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
    pub(crate) fn add3(&mut self, x: &WireWord, y: &WireWord, z: &WireWord, base: usize) -> WireWord {
        let rip_base = base + CARRY_BITS_PER_ADD;

        // Phase 1: the majority layer, the carry-save sum's carry word.
        let mut maj = [F192::ZERO; CARRY_BITS_PER_ADD];
        for i in 0..CARRY_BITS_PER_ADD {
            self.product(base + i, x[i] + z[i], y[i] + z[i]);
            maj[i] = self.w[base + i] + z[i];
        }

        // Phase 2: the ripple layer adds the parity word and the majority word shifted up one bit.
        let mut out = WireWord::ZERO;
        let mut cin = F192::ZERO;
        for i in 0..WORD_BITS {
            let q_i = if i == 0 { F192::ZERO } else { maj[i - 1] };
            let a_side = x[i] + y[i] + z[i] + cin;
            out[i] = a_side + q_i;
            // Bit 0 has no shifted majority to carry with, and bit 31's carry falls off the modulus.
            if (1..=RIPPLE_BITS_PER_ADD3).contains(&i) {
                self.product(rip_base + i - 1, a_side, q_i + cin);
                cin += self.w[rip_base + i - 1];
            }
        }
        out
    }
}

/// Which matrix the backward walk follows in each R1CS row.
///
/// For either matrix `D_0`, the forward walk evaluates `S(w) = u^T D_0 w`, linear in `w`.
/// So `S(w) = <M, w>` for the column marginal `M = D_0^T u`, the gradient of the walk in `w`.
/// Reverse-mode differentiation of the walk then gives the whole marginal, in field operations linear in the circuit.
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

/// The backward walk's output, one matrix's column marginal `D_0^T u`, filled column by column.
///
/// Each backward gadget is the transpose of its forward one.
/// It takes the adjoint of the gadget's sum word, deposits the marginal entries of its own slots, and returns its operands' adjoints.
pub(crate) struct Marginal<'a> {
    /// The marginal so far.
    m: Vec<F192>,

    /// The row weights.
    u: &'a [F192],

    /// The matrix followed.
    side: MatrixSide,
}

impl<'a> Marginal<'a> {
    /// An empty marginal of the matrix `side`, at the row weights `u`.
    pub(crate) fn new(side: MatrixSide, u: &'a [F192]) -> Self {
        Self {
            m: vec![F192::ZERO; u.len()],
            u,
            side,
        }
    }

    /// The followed side's share of row `k`'s weight, and the other's.
    #[inline]
    pub(crate) const fn row(&self, k: usize) -> (F192, F192) {
        self.side.split(self.u[k])
    }

    /// Row `k`'s own weight, whatever the side.
    #[inline]
    pub(crate) const fn weight(&self, k: usize) -> F192 {
        self.u[k]
    }

    /// Add `value` to column `j`.
    #[inline]
    pub(crate) fn deposit(&mut self, j: usize, value: F192) {
        self.m[j] += value;
    }

    /// Add an adjoint word to the 32 columns from `base`: the word committed there reaches them unchanged.
    #[inline]
    pub(crate) fn deposit_word(&mut self, base: usize, adj: &WireWord) {
        for (m, &bit) in self.m[base..base + WORD_BITS].iter_mut().zip(adj.bits()) {
            *m += bit;
        }
    }

    /// The finished marginal.
    pub(crate) fn into_columns(self) -> Vec<F192> {
        self.m
    }

    /// The transpose of the two-operand addition's walk, whose rows it must mirror exactly.
    ///
    /// - `adj` is the adjoint of the sum word.
    /// - The marginal entries of the 31 carry slots are deposited.
    /// - Returns the adjoints of `x` and `y`.
    ///
    /// Slot `carry_base + j` is read by every `cin_i` with `i > j`.
    /// So its marginal entry is the suffix sum of the `cin_i` adjoints, walked from the top bit down.
    pub(crate) fn add(&mut self, adj: &WireWord, carry_base: usize) -> (WireWord, WireWord) {
        let (mut ax, mut ay) = (WireWord::ZERO, WireWord::ZERO);
        // The adjoint of every carry above the current bit, which each lower carry slot feeds.
        let mut suffix = F192::ZERO;
        for i in (0..WORD_BITS).rev() {
            // `cin_i` reaches the sum bit, then both sides of its carry row.
            let mut cin_adj = adj[i];
            if i < CARRY_BITS_PER_ADD {
                self.deposit(carry_base + i, suffix);
                let (pa, pb) = self.row(carry_base + i);
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
    /// - The marginal entries of the 31 majority slots and the 30 ripple slots are deposited.
    /// - Returns the adjoints of `x`, `y` and `z`.
    ///
    /// `maj_i = maj_aux_i + z_i` feeds the ripple layer as `q_(i+1)`, so `z` and the majority slot both take its adjoint.
    /// A ripple slot is read by every later `cin`, hence a suffix sum, as in the two-operand transpose.
    pub(crate) fn add3(&mut self, adj: &WireWord, base: usize) -> (WireWord, WireWord, WireWord) {
        let rip_base = base + CARRY_BITS_PER_ADD;
        let (mut ax, mut ay, mut az) = (WireWord::ZERO, WireWord::ZERO, WireWord::ZERO);
        let ripples = 1..=RIPPLE_BITS_PER_ADD3;
        // Ripple row weight at bit `i`, zero where the layer has no row.
        let rip = |me: &Self, i: usize| -> F192 {
            if ripples.contains(&i) {
                me.weight(rip_base + i - 1)
            } else {
                F192::ZERO
            }
        };
        // The adjoint of every ripple carry above the current bit.
        let mut suffix = F192::ZERO;
        for i in (0..WORD_BITS).rev() {
            let ri = rip(self, i);
            if ripples.contains(&i) {
                self.deposit(rip_base + i - 1, suffix);
            }
            // `cin_i` reaches the sum bit and both sides of the ripple row.
            suffix += adj[i] + ri;
            // `p_i = x_i + y_i + z_i` reaches the sum bit and the ripple row's A side.
            let common = adj[i] + self.side.split(ri).0;
            let (mut xi, mut yi, mut zi) = (common, common, common);
            if i < CARRY_BITS_PER_ADD {
                // The majority row reads `x_i + z_i` on A and `y_i + z_i` on B.
                let (ma, mb) = self.row(base + i);
                xi += ma;
                yi += mb;
                zi += ma + mb;
                // `maj_i = maj_aux_i + z_i` is the ripple layer's `q_(i+1)`, read by its sum bit and its row's B side.
                let qa = adj[i + 1] + self.side.split(rip(self, i + 1)).1;
                self.deposit(base + i, qa);
                zi += qa;
            }
            ax[i] = xi;
            ay[i] = yi;
            az[i] = zi;
        }
        (ax, ay, az)
    }
}
