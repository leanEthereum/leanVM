//! The field the compiler folds constants in: the verifier's `K` and `E`, under the names the provers give them, with
//! the few operations the verifier does not need.

pub use verifier::{E as F128, K as F64};

/// Zero and one.
pub trait Consts {
    const ZERO: Self;
    const ONE: Self;
}

impl Consts for F64 {
    const ZERO: Self = F64(0);
    const ONE: Self = F64(1);
}

impl Consts for F128 {
    const ZERO: Self = F128::new(0, 0);
    const ONE: Self = F128::new(1, 0);
}

/// The generator `g = x` of `K` and its powers.
pub trait Base: Sized {
    const G: Self;
    fn pow(self, exponent: u128) -> Self;
}

impl Base for F64 {
    const G: Self = F64(2);

    fn pow(self, mut exponent: u128) -> Self {
        let (mut base, mut out) = (self, F64::ONE);
        while exponent != 0 {
            if exponent & 1 == 1 {
                out = out * base;
            }
            base = base * base;
            exponent >>= 1;
        }
        out
    }
}

/// `g^i`.
pub fn g_pow(i: usize) -> F64 {
    F64::G.pow(i as u128)
}

/// The base-field element a word is, or `None` when its `y` coefficient is nonzero.
pub fn as_base(word: F128) -> Option<F64> {
    (word.c1 == 0).then_some(F64(word.c0))
}

/// The word whose bits are `n`'s: `c0` its low 64 bits, `c1` its high.
pub const fn word(n: u128) -> F128 {
    F128::new(n as u64, (n >> 64) as u64)
}

/// The integer whose bits spell a word's coefficients, `c0` low: the inverse of [`word`].
pub const fn int(w: F128) -> u128 {
    w.c0 as u128 | (w.c1 as u128) << 64
}
