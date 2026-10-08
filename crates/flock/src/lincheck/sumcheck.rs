//! The lincheck's product sumcheck over two tables, binding the top variable first.
//!
//! ```text
//!     claim = sum_i comb[i] * z[i]
//! ```
//!
//! A round splits both tables at their top variable, `lo` the first half and `hi` the second:
//!
//! ```text
//!     q(1)   = sum_i comb_hi[i] * z_hi[i]
//!     q(inf) = sum_i (comb_lo[i] + comb_hi[i]) * (z_lo[i] + z_hi[i])      the leading coefficient
//! ```

use parallel::SendPtr;
use primitives::field::F192;

/// Half-table length above which a pass fans out to the pool; below it, a dispatch costs more than it saves.
const PAR_THRESHOLD: usize = 1 << 12;

/// The two tables of a product sumcheck, shrinking by half per bound variable.
#[derive(Clone, Debug)]
pub(super) struct ProductSumcheck {
    /// The batched column marginal of the circuit's matrices.
    comb: Vec<F192>,
    /// The witness, partially folded.
    z: Vec<F192>,
}

impl ProductSumcheck {
    /// The sumcheck of `sum_i comb[i] z[i]`.
    ///
    /// # Panics
    ///
    /// When the tables differ in length, or are not a power of two.
    pub(super) fn new(comb: Vec<F192>, z: Vec<F192>) -> Self {
        assert_eq!(comb.len(), z.len(), "one weight per witness value");
        assert!(z.len().is_power_of_two());
        Self { comb, z }
    }

    /// The whole sum, `sum_i comb[i] z[i]`.
    pub(super) fn claim(&self) -> F192 {
        primitives::multilinear::inner_product(&self.comb, &self.z)
    }

    /// The current round's `(q(1), q(inf))`.
    pub(super) fn round(&self) -> (F192, F192) {
        let half = self.z.len() / 2;
        let (c_lo, c_hi) = self.comb.split_at(half);
        let (z_lo, z_hi) = self.z.split_at(half);
        // One term of each coefficient at index `i`.
        let term = |i: usize| (c_hi[i] * z_hi[i], (c_lo[i] + c_hi[i]) * (z_lo[i] + z_hi[i]));
        let add = |x: (F192, F192), y: (F192, F192)| (x.0 + y.0, x.1 + y.1);
        if half < PAR_THRESHOLD {
            return (0..half).map(term).fold((F192::ZERO, F192::ZERO), add);
        }
        parallel::map_reduce(half, || (F192::ZERO, F192::ZERO), term, add)
    }

    /// Bind the top variable at `r`, and return the next round's `(q(1), q(inf))`.
    ///
    /// Binding produces exactly the halves the next round pairs up, so both happen in one pass:
    ///
    /// ```text
    ///     quarters    q0 q1 | q2 q3          (q0, q2) bind to the next lo, (q1, q3) to the next hi
    ///     lo' = q0 + r (q0 + q2)     hi' = q1 + r (q1 + q3)
    ///     q(1) += hi'_c hi'_z        q(inf) += (lo'_c + hi'_c) (lo'_z + hi'_z)
    /// ```
    ///
    /// Each index reads its four quarter entries before writing the two low ones, so binding in place is safe.
    ///
    /// # Panics
    ///
    /// When fewer than four values remain, which leaves no next round.
    pub(super) fn bind_and_round(&mut self, r: F192) -> (F192, F192) {
        let len = self.z.len();
        let (half, quarter) = (len / 2, len / 4);
        assert!(quarter >= 1, "a next round needs two values after binding");

        // The low half is written, the high half only read.
        let (c_lo, c_hi) = self.comb.split_at_mut(half);
        let (c0, c1) = c_lo.split_at_mut(quarter);
        let (c2, c3) = c_hi.split_at(quarter);
        let (z_lo, z_hi) = self.z.split_at_mut(half);
        let (z0, z1) = z_lo.split_at_mut(quarter);
        let (z2, z3) = z_hi.split_at(quarter);

        // Bind index `i` of every quarter, and return its two next-round terms.
        let step = |[c0, c1, z0, z1]: [&mut F192; 4], i: usize| {
            let lo = *c0 + r * (c2[i] + *c0);
            let hi = *c1 + r * (c3[i] + *c1);
            let z_lo = *z0 + r * (z2[i] + *z0);
            let z_hi = *z1 + r * (z3[i] + *z1);
            (*c0, *c1, *z0, *z1) = (lo, hi, z_lo, z_hi);
            (hi * z_hi, (hi + lo) * (z_hi + z_lo))
        };
        let add = |x: (F192, F192), y: (F192, F192)| (x.0 + y.0, x.1 + y.1);

        let next = if quarter < PAR_THRESHOLD {
            ((c0.iter_mut().zip(c1.iter_mut())).zip(z0.iter_mut().zip(z1.iter_mut())))
                .enumerate()
                .map(|(i, ((c0, c1), (z0, z1)))| step([c0, c1, z0, z1], i))
                .fold((F192::ZERO, F192::ZERO), add)
        } else {
            // Four written quarters cannot zip into one parallel loop, so each task indexes them.
            let ptrs = [c0, c1, z0, z1].map(|q| SendPtr(q.as_mut_ptr()));
            parallel::map_reduce(
                quarter,
                || (F192::ZERO, F192::ZERO),
                |i| {
                    // SAFETY: distinct `i` touch distinct slots of four disjoint quarters.
                    // All four stay borrowed for the dispatch.
                    let slots = ptrs.map(|p| unsafe { &mut *p.add(i) });
                    step(slots, i)
                },
                add,
            )
        };
        self.comb.truncate(half);
        self.z.truncate(half);
        next
    }

    /// Bind the last variable at `r`, in the witness only.
    ///
    /// Only the witness is read afterwards, so the marginal's last bind would be dead work: it is dropped instead.
    pub(super) fn bind_last(&mut self, r: F192) {
        // Each low entry takes its high partner: `lo + r (lo + hi)`.
        let half = self.z.len() / 2;
        let (lo, hi) = self.z.split_at_mut(half);
        let bind = |lo: &mut [F192], hi: &[F192]| {
            for (l, &h) in lo.iter_mut().zip(hi) {
                *l += r * (h + *l);
            }
        };
        if half < PAR_THRESHOLD {
            bind(lo, hi);
        } else {
            parallel::chunks_mut_zip(lo, hi, parallel::recommended_chunk_size(half), |_, lo, hi| bind(lo, hi));
        }
        self.z.truncate(half);
        self.comb = Vec::new();
    }

    /// The witness as it stands.
    pub(super) fn into_z(self) -> Vec<F192> {
        self.z
    }
}

#[cfg(test)]
mod tests {
    use primitives::test_util::Rng;

    use super::*;

    /// One top-variable bind of a table, the definition.
    fn bind_top(v: &[F192], r: F192) -> Vec<F192> {
        let (lo, hi) = v.split_at(v.len() / 2);
        lo.iter().zip(hi).map(|(&l, &h)| l + r * (l + h)).collect()
    }

    #[test]
    fn the_fused_bind_is_a_bind_then_a_round() {
        // Invariant: binding and the next round in one pass equal a plain bind followed by a plain round.
        //
        // Fixture state: tables below and above the parallel threshold, down to the last round.
        let mut rng = Rng::new(0x5C_0B1D);
        for log in [2, 5, 15] {
            let (comb, z) = (rng.ext_vec(1 << log), rng.ext_vec(1 << log));
            let mut fused = ProductSumcheck::new(comb.clone(), z.clone());
            let (mut comb, mut z) = (comb, z);
            for _ in 0..log - 1 {
                let r = rng.ext();
                let next = fused.bind_and_round(r);
                (comb, z) = (bind_top(&comb, r), bind_top(&z, r));
                let plain = ProductSumcheck::new(comb.clone(), z.clone());
                assert_eq!(next, plain.round(), "log={log}, len={}", z.len());
                assert_eq!(fused.claim(), plain.claim(), "log={log}, len={}", z.len());
            }
            let r = rng.ext();
            fused.bind_last(r);
            assert_eq!(fused.into_z(), bind_top(&z, r), "log={log}");
        }
    }
}
