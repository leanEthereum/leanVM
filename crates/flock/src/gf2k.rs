//! Symbolic GF(2) lanes for the Keccak circuit.
//!
//! Keccak-f's θ, ρ, π and ι are linear over GF(2), so the only nonlinear
//! constraints are χ's products `¬b ∧ c`, one per state bit per round. Everything
//! else is carried symbolically: a [`WireLane`] is 64 `F192` values, bit `k` of a
//! state lane as the running linear combination of committed slots it equals,
//! evaluated against some column weights `w`.
//!
//! The matrices this describes are never built. A forward walk gives the row
//! values `A₀ w` and `B₀ w`; its transpose, walked backwards, gives the column
//! marginal `(A₀ + α B₀)ᵀ u`. The pair is cross-checked by the protocol itself:
//! lincheck's terminal identity is exactly the assertion that the backward walk's
//! marginal, contracted against the column weights, equals the forward walk's
//! bilinear form.

use primitives::field::F192;

/// Bits per lane.
pub(crate) const LANE_BITS: usize = 64;

/// One lane's wire values: bit `k` of the lane, as the F192 combination
/// `⟨lin_func_k, w⟩`.
pub(crate) type WireLane = [F192; LANE_BITS];

#[inline]
pub(crate) fn wire_from_slot_base(w: &[F192], base: usize) -> WireLane {
    std::array::from_fn(|k| w[base + k])
}

#[inline]
pub(crate) fn wire_xor(x: &WireLane, y: &WireLane) -> WireLane {
    std::array::from_fn(|k| x[k] + y[k])
}

/// XOR a constant into a lane in place.
#[inline]
pub(crate) fn wire_xor_const(x: &mut WireLane, wc: F192, val: u64) {
    for (k, xk) in x.iter_mut().enumerate() {
        if (val >> k) & 1 == 1 {
            *xk += wc;
        }
    }
}

/// `rotl(x, n)`: bit `k` of the result is bit `k - n` of `x`.
#[inline]
pub(crate) fn wire_rotl(x: &WireLane, n: usize) -> WireLane {
    std::array::from_fn(|k| x[(k + LANE_BITS - n) % LANE_BITS])
}

/// Transpose of [`wire_rotl`]: `⟨wire_rotl(x, n), a⟩ = ⟨x, wire_rotr(a, n)⟩`.
#[inline]
pub(crate) fn wire_rotr(x: &WireLane, n: usize) -> WireLane {
    std::array::from_fn(|k| x[(k + n) % LANE_BITS])
}

/// The matrix-vector products `(A_0 w, B_0 w)`. Rows with no wire keep their zeros.
pub(crate) struct RowValues {
    pub(crate) a: Vec<F192>,
    pub(crate) b: Vec<F192>,
    wc: F192,
}

impl RowValues {
    pub(crate) fn new(k: usize, wc: F192) -> Self {
        Self {
            a: vec![F192::ZERO; k],
            b: vec![F192::ZERO; k],
            wc,
        }
    }

    #[inline]
    pub(crate) fn product(&mut self, k: usize, a: F192, b: F192) {
        self.a[k] = a;
        self.b[k] = b;
    }

    /// A row whose B side is the lone constant wire: a free input, the constant
    /// itself, or a lin-id output.
    #[inline]
    pub(crate) fn bconst(&mut self, k: usize, a: F192) {
        self.a[k] = a;
        self.b[k] = self.wc;
    }
}

/// Which matrix operand the backward walk follows in each R1CS row.
#[derive(Clone, Copy)]
pub(crate) enum MatrixSide {
    A,
    B,
}

impl MatrixSide {
    #[inline]
    pub(crate) fn split(self, value: F192) -> (F192, F192) {
        match self {
            Self::A => (value, F192::ZERO),
            Self::B => (F192::ZERO, value),
        }
    }
}
