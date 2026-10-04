//! Arithmetic over `E`: the `EMUL` and `EXK` rows, with the units folded away.

use super::{Builder, e_limbs};
use crate::rec::circuit::{Ew, Kind, Kw};
use crate::rec::table::Table;
use primitives::field::{F64, F192};

impl Builder {
    fn emul(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        let c = Ew(self.wire(Kind::E, e_limbs(self.e(a) * self.e(b) + self.e(d))));
        self.row(Table::Emul, &[a.0, b.0, d.0, c.0]);
        c
    }

    /// `a·b + d`.
    pub fn mul_add(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        let u = self.units;
        if u.e_zero.is_some_and(|z| z == a.0 || z == b.0) {
            d
        } else if u.e_one == Some(b.0) {
            self.add(a, d)
        } else if u.e_one == Some(a.0) {
            self.add(b, d)
        } else {
            self.emul(a, b, d)
        }
    }

    /// `a·b`.
    pub fn mul(&mut self, a: Ew, b: Ew) -> Ew {
        let zero = self.zero();
        self.mul_add(a, b, zero)
    }

    /// `a + d`.
    pub fn add(&mut self, a: Ew, d: Ew) -> Ew {
        let zero = self.units.e_zero;
        if zero == Some(d.0) {
            a
        } else if zero == Some(a.0) {
            d
        } else {
            let one = self.one();
            self.emul(a, one, d)
        }
    }

    /// `a^2`.
    pub fn square(&mut self, a: Ew) -> Ew {
        self.mul(a, a)
    }

    /// `a·k + d`, `k` in `K`.
    pub fn mul_k_add(&mut self, a: Ew, k: Kw, d: Ew) -> Ew {
        let u = self.units;
        if u.e_zero == Some(a.0) || u.k_zero == Some(k.0) {
            return d;
        }
        if u.k_one == Some(k.0) {
            return self.add(a, d);
        }
        let c = Ew(self.wire(Kind::E, e_limbs(self.e(a).mul_base(F64(self.k(k))) + self.e(d))));
        self.row(Table::Exk, &[a.0, k.0, d.0, c.0]);
        c
    }

    /// `a·k`, `k` in `K`.
    pub fn mul_k(&mut self, a: Ew, k: Kw) -> Ew {
        let zero = self.zero();
        self.mul_k_add(a, k, zero)
    }

    /// `a·c + d` for a constant `c`, through the cheaper table when `c` is in `K`.
    pub fn mul_const_add(&mut self, a: Ew, c: F192, d: Ew) -> Ew {
        if c.c1 == 0 && c.c2 == 0 {
            let k = self.k_const(c.c0);
            return self.mul_k_add(a, k, d);
        }
        let c = self.e_const(c);
        self.mul_add(a, c, d)
    }

    /// `a·c` for a constant `c`.
    pub fn mul_const(&mut self, a: Ew, c: F192) -> Ew {
        let zero = self.zero();
        self.mul_const_add(a, c, zero)
    }

    /// `a + c` for a constant `c`.
    pub fn add_const(&mut self, a: Ew, c: F192) -> Ew {
        let c = self.e_const(c);
        self.add(a, c)
    }

    /// `1 / a`, zero for zero: a hint the prover supplies, held to `a·(1/a) = 1`.
    pub fn inv(&mut self, a: Ew) -> Ew {
        let v = self.e(a);
        let i = self.free_e(if v.is_zero() { F192::ZERO } else { v.inv() });
        let p = self.mul(a, i);
        self.eq_e_const(p, F192::ONE);
        i
    }

    /// `sum_i a_i·b_i + init`.
    ///
    /// # Panics
    ///
    /// Panics if the two lists differ in length.
    pub fn dot(&mut self, a: &[Ew], b: &[Ew], init: Ew) -> Ew {
        assert_eq!(a.len(), b.len(), "a dot product of unequal lengths");
        a.iter().zip(b).fold(init, |acc, (&x, &y)| self.mul_add(x, y, acc))
    }

    /// `sum_i terms_i`.
    pub fn sum(&mut self, terms: &[Ew]) -> Ew {
        let zero = self.zero();
        terms.iter().fold(zero, |acc, &t| self.add(acc, t))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn units_emit_no_row() {
        let mut b = Builder::new();
        let x = b.free_e(F192::new(3, 5, 7));
        let k = b.free_k(9);
        let (zero, one) = (b.zero(), b.one());
        let (k0, k1) = (b.k_const(0), b.k_const(1));
        assert_eq!(b.mul(x, one), x);
        assert_eq!(b.mul(one, x), x);
        assert_eq!(b.add(x, zero), x);
        assert_eq!(b.add(zero, x), x);
        assert_eq!(b.mul_add(x, zero, one), one);
        assert_eq!(b.mul_k_add(x, k1, zero), x);
        assert_eq!(b.mul_k_add(x, k0, one), one);
        assert_eq!(b.mul_k(zero, k), zero);
        assert_eq!(b.mul_const(x, F192::ONE), x);
        assert_eq!(b.add_const(x, F192::ZERO), x);
        assert_eq!(b.sum(&[x]), x);
        let finished = b.finish();
        assert!(finished.failures.is_empty(), "{:?}", finished.failures);
        assert_eq!(finished.circuit.row_counts(), [0, 0, 0, 0, 0, 4]);
    }
}
