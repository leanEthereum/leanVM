//! Arithmetic over `E`: the `EMUL` and `EXK` rows, with the units and repeated rows folded away.

#[cfg(feature = "circuit-trace")]
use super::list;
use super::{Builder, row_key};
use crate::rec::circuit::{Ew, Kw};
use crate::rec::clean::{ARITH_A, ARITH_B, ARITH_C, ARITH_D};
use crate::rec::table::Table;
use primitives::field::{F64, F192};

impl Builder {
    /// An `EMUL` or `EXK` row `c = a·b + d`.
    fn arith_row(&mut self, table: Table, [a, b, d, c]: [u32; 4]) {
        let mut slots = [0; 4];
        (slots[ARITH_A], slots[ARITH_B], slots[ARITH_D], slots[ARITH_C]) = (a, b, d, c);
        self.row(table, &slots);
    }

    fn emul(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        let key = row_key(Table::Emul, self.emul_key(a, b, d));
        if let Some(&c) = self.arith.get(&key) {
            return Ew(c);
        }
        let c = self.free_e(self.e(a) * self.e(b) + self.e(d));
        self.arith_row(Table::Emul, [a.0, b.0, d.0, c.0]);
        self.arith.insert(key, c.0);
        c
    }

    /// The inputs of `a·b + d` in one order for every order giving the same row: the factors in order, and for `1·x + d` the terms.
    fn emul_key(&self, a: Ew, b: Ew, d: Ew) -> [u32; 3] {
        let one = self.units.e_one;
        if one == Some(a.0) || one == Some(b.0) {
            let x = if one == Some(a.0) { b.0 } else { a.0 };
            [one.expect("the unit"), x.min(d.0), x.max(d.0)]
        } else {
            [a.0.min(b.0), a.0.max(b.0), d.0]
        }
    }

    /// `a·b + d`.
    pub fn mul_add(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        traced!(
            self,
            format!("mul_add {} {} {}", a.0, b.0, d.0),
            self.mul_add_rows(a, b, d)
        )
    }

    fn mul_add_rows(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
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
        traced!(self, format!("mul {} {}", a.0, b.0), self.mul_rows(a, b))
    }

    fn mul_rows(&mut self, a: Ew, b: Ew) -> Ew {
        let zero = self.zero();
        self.mul_add(a, b, zero)
    }

    /// `a + d`.
    pub fn add(&mut self, a: Ew, d: Ew) -> Ew {
        traced!(self, format!("add {} {}", a.0, d.0), self.add_rows(a, d))
    }

    fn add_rows(&mut self, a: Ew, d: Ew) -> Ew {
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
        traced!(self, format!("square {}", a.0), self.square_rows(a))
    }

    fn square_rows(&mut self, a: Ew) -> Ew {
        self.mul(a, a)
    }

    /// `a·k + d`, `k` in `K`.
    pub fn mul_k_add(&mut self, a: Ew, k: Kw, d: Ew) -> Ew {
        traced!(
            self,
            format!("mul_k_add {} {} {}", a.0, k.0, d.0),
            self.mul_k_add_rows(a, k, d)
        )
    }

    fn mul_k_add_rows(&mut self, a: Ew, k: Kw, d: Ew) -> Ew {
        let u = self.units;
        if u.e_zero == Some(a.0) || u.k_zero == Some(k.0) {
            return d;
        }
        if u.k_one == Some(k.0) {
            return self.add(a, d);
        }
        let key = row_key(Table::Exk, [a.0, k.0, d.0]);
        if let Some(&c) = self.arith.get(&key) {
            return Ew(c);
        }
        let c = self.free_e(self.e(a).mul_base(F64(self.k(k))) + self.e(d));
        self.arith_row(Table::Exk, [a.0, k.0, d.0, c.0]);
        self.arith.insert(key, c.0);
        c
    }

    /// `a·c + d` for a constant `c`, through the cheaper table when `c` is in `K`.
    pub fn mul_const_add(&mut self, a: Ew, c: F192, d: Ew) -> Ew {
        traced!(
            self,
            format!("mul_const_add {} {} {} {} {}", a.0, c.c0, c.c1, c.c2, d.0),
            self.mul_const_add_rows(a, c, d)
        )
    }

    fn mul_const_add_rows(&mut self, a: Ew, c: F192, d: Ew) -> Ew {
        if c.c1 == 0 && c.c2 == 0 {
            let k = self.k_const(c.c0);
            return self.mul_k_add(a, k, d);
        }
        let c = self.e_const(c);
        self.mul_add(a, c, d)
    }

    /// `1 / a`, zero for zero: a hint the prover supplies, held to `a·(1/a) = 1`.
    pub fn inv(&mut self, a: Ew) -> Ew {
        traced!(self, format!("inv {}", a.0), self.inv_rows(a))
    }

    fn inv_rows(&mut self, a: Ew) -> Ew {
        let v = self.e(a);
        let i = self.free_e(if v.is_zero() { F192::ZERO } else { v.inv() });
        let p = self.mul(a, i);
        self.eq_e_const(p, F192::ONE);
        i
    }

    /// `sum_i terms_i`.
    pub fn sum(&mut self, terms: &[Ew]) -> Ew {
        traced!(
            self,
            format!("sum {}", list(terms.iter().map(|w| w.0))),
            self.sum_rows(terms)
        )
    }

    fn sum_rows(&mut self, terms: &[Ew]) -> Ew {
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
        assert_eq!(b.mul_k_add(zero, k, zero), zero);
        assert_eq!(b.sum(&[x]), x);
        let finished = b.finish();
        assert!(finished.failures.is_empty(), "{:?}", finished.failures);
        assert_eq!(finished.circuit.row_counts().into_values(), [0, 0, 0, 0, 0, 4]);
    }

    #[test]
    fn a_repeated_row_is_the_earlier_one() {
        let mut b = Builder::new();
        let (x, y, z) = (
            b.free_e(F192::new(3, 5, 7)),
            b.free_e(F192::new(2, 0, 9)),
            b.free_e(F192::new(4, 1, 0)),
        );
        let k = b.free_k(9);
        let xy = b.mul_add(x, y, z);
        assert_eq!(b.mul_add(y, x, z), xy, "the factors commute");
        let xz = b.mul_add(x, z, y);
        assert_ne!(xz, xy, "a term is not a factor");
        assert_eq!(b.e(xz), b.e(x) * b.e(z) + b.e(y));
        let sum = b.add(x, y);
        assert_eq!(b.add(y, x), sum, "the terms of a sum commute");
        let one = b.one();
        assert_eq!(b.mul_add(one, y, x), sum, "a sum is a product by one");
        assert_ne!(b.mul_add(x, y, one), sum);
        let xk = b.mul_k_add(x, k, z);
        assert_eq!(b.mul_k_add(x, k, z), xk);
        assert_ne!(b.mul_k_add(z, k, x), xk, "a K row is not symmetric");
        assert_ne!(b.mul_add(x, y, y), xy, "another addend is another row");
        let (x_again, k_again) = (b.free_e(b.e(x)), b.free_k(b.k(k)));
        assert_ne!(
            b.mul_add(x_again, y, z),
            xy,
            "a row folds by its wires, never by their values"
        );
        assert_ne!(
            b.mul_k_add(x, k_again, z),
            xk,
            "a row folds by its wires, never by their values"
        );
        let finished = b.finish();
        assert!(finished.failures.is_empty(), "{:?}", finished.failures);
        let [emul, exk, ..] = finished.circuit.row_counts().into_values();
        assert_eq!(
            (emul, exk),
            (6, 3),
            "x·y + z, x·z + y, x + y, x·y + 1, x·y + y, x'·y + z; then x·k + z, z·k + x, x·k' + z"
        );
    }
}
