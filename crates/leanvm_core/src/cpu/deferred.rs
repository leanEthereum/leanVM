//! The claims a proof leaves on polynomials that only the program or the VM's circuits fix.
//!
//! The verifier's core runs every check that depends on the proof and returns these claims.
//! Settling them is the rest of verification.
//! Their points are challenges and stream scalars, and nothing is absorbed after them, so a recursive verifier can carry them out of the proof and settle them later.
//!
//! Each completes an identity the full verifier checks whole:
//!
//! - the table sumcheck's final identity, short of the bytecode producer's program columns and of RAM's image in its target;
//! - each flock circuit's lincheck terminal identity, short of the bilinear form `u^T (A_0 + alpha B_0) w` of its matrices.
//!
//! Lincheck's `C` is the identity, whose form is closed and stays in the core.

use super::batch::FormPowers;
use super::layout::{Lookup, ProgramView};
use super::{CpuError, Program};
use crate::class_flock::{FlockId, N_FLOCKS};
use crate::constraints::{ConstraintError, Final};
use crate::leaf;
use crate::leaf::{BusVerify, N_TUPLE_BITS, SparseColumn};
use crate::tables::{N_TABLES, Part};
use fiat_shamir::arith::Arith;
use flock::FlockError;
use flock::lincheck::{LincheckError, MatrixClaim, MatrixForm};
use primitives::field::F192;
use thiserror::Error;

/// One fixed polynomial `f` claimed to take `value` at `point`.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim<P, E = F192> {
    /// Where the polynomial is evaluated.
    pub point: P,
    /// The value the proof claims it takes there.
    pub value: E,
}

/// A point of the program's fixed polynomials, at which they take the value
///
/// ```text
/// sum_i mu_i sum_x eq(chi, x) T(x, alpha)^(2^i) + image_weight image(image_point)
/// ```
///
/// - `T(x, alpha) = sum_s eq(alpha, s) T(x, s)` is the stacked bytecode table at entry `x`.
/// - `image` is RAM's image, then zeros.
///
/// The first sum is the bytecode producer's program columns, bit `i`'s raised to `2^i`.
/// Raising to `2^i` is the Frobenius automorphism `phi^i`, so bit `i`'s column is `phi^i(T(phi^(-i)(chi), alpha))`.
/// The weights `mu_i` batch every bit's into one claim on the table at `(chi, alpha)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramPoint<E = F192> {
    /// The table sumcheck's point on the entries `chi`, then the bus fingerprint's `alpha`.
    pub bytecode: Vec<E>,
    /// The weight `mu_i` of each multiplicity bit, lowest first.
    pub twist: Vec<E>,
    /// The weight of the image's term.
    pub image_weight: E,
    /// The point at which the image is evaluated.
    pub image_point: Vec<E>,
}

impl<E: Copy> ProgramPoint<E> {
    /// The same point, each element mapped by `f`.
    pub fn map<T>(&self, mut f: impl FnMut(E) -> T) -> ProgramPoint<T> {
        ProgramPoint {
            bytecode: self.bytecode.iter().map(|&x| f(x)).collect(),
            twist: self.twist.iter().map(|&x| f(x)).collect(),
            image_weight: f(self.image_weight),
            image_point: self.image_point.iter().map(|&x| f(x)).collect(),
        }
    }
}

/// Everything the verifier's core leaves to the program and to the VM's circuits.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeferredClaims<E = F192> {
    /// The claim on the program's bytecode table and RAM image.
    pub program: Claim<ProgramPoint<E>, E>,
    /// One claim per packed witness, class circuits then clock circuits, on its circuit's matrix form.
    pub circuits: Vec<Claim<MatrixForm<E>, E>>,
}

impl<E: Copy> DeferredClaims<E> {
    /// The same claims, each element mapped by `f`.
    pub fn map<T>(&self, mut f: impl FnMut(E) -> T) -> DeferredClaims<T> {
        DeferredClaims {
            program: Claim {
                point: self.program.point.map(&mut f),
                value: f(self.program.value),
            },
            circuits: (self.circuits.iter())
                .map(|c| Claim {
                    point: c.point.map(&mut f),
                    value: f(c.value),
                })
                .collect(),
        }
    }
}

/// Why a set of deferred claims has no shape the program and its circuits give claims.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum MalformedClaim {
    /// Not one claim per packed witness.
    #[error("{got} circuit claims, for {expected} circuits")]
    CircuitCount {
        /// The number of packed witnesses.
        expected: usize,
        /// The number of claims.
        got: usize,
    },
    /// The program claim's point does not fit the program's table and RAM.
    #[error("the program claim's point does not fit the program")]
    ProgramPoint,
    /// A circuit claim's point does not fit its circuit.
    #[error("the {table} table's {part:?} circuit claim's point does not fit the circuit")]
    MatrixForm {
        /// The table.
        table: &'static str,
        /// Which of its circuits.
        part: Part,
    },
}

impl ProgramPoint {
    /// The value of the program's fixed polynomials at this point, if the point has the program's shape.
    fn evaluate(&self, view: &ProgramView<'_>) -> Option<F192> {
        let rv = view.rv;
        let kbc = crate::log2_strict_usize(rv.entries().len());
        // A multiplicity is one word, so it has at most 64 bits.
        if self.bytecode.len() != kbc + N_TUPLE_BITS || self.image_point.len() != rv.log_ram() || self.twist.len() > 64
        {
            return None;
        }
        let (chi, alphas) = self.bytecode.split_at(kbc);
        let weights = leaf::fingerprint_weights(alphas);
        let bytecode = leaf::producer_public_twist(&Lookup::Bytecode.tuple(view), &weights, chi, &self.twist);
        let image = SparseColumn::new(rv.log_ram(), &[(0, rv.image())]);
        Some(bytecode + self.image_weight * image.eval(&self.image_point))
    }
}

impl<E: Copy> Claim<ProgramPoint<E>, E> {
    /// The claim the table sumcheck's final identity leaves to the program.
    ///
    /// - The producer's summand `sum_i c_i (1 + b_i P'_i)` takes each program column `P'_i` at weight `c_i b_i`.
    /// - RAM's image is out of the bus target, and reaches the final claim at the target's weight.
    pub(crate) fn from_table_sumcheck<A: Arith<E = E>>(
        a: &mut A,
        bus: &BusVerify<E>,
        table_sumcheck: &Final<E>,
        powers: FormPowers<E>,
    ) -> Self {
        // The bytecode's producer is the first, whose program columns the claim takes: the padding producer's are the
        // verifier's own.
        let coefficients = &bus.producers[Lookup::Bytecode as usize];
        // The producer's air follows the tables'.
        let air = N_TABLES;
        let (weight, producer) = (table_sumcheck.weights[air], &table_sumcheck.claims[air]);
        let twist = (coefficients.iter().zip(&producer.evals))
            .map(|(&c, &b)| {
                let wc = a.mul(weight, c);
                let pushed = a.mul(wc, powers.push());
                a.mul(pushed, b)
            })
            .collect();
        let mut shares = (0..2).flat_map(|s| bus.sparse[s].iter().map(move |share| (s, share)));
        let (Some((side, image)), None) = (shares.next(), shares.next()) else {
            unreachable!("RAM's image is the one sparse column, seeded once")
        };
        let sided = a.mul(table_sumcheck.target_weight, powers.side(side));
        Self {
            point: ProgramPoint {
                bytecode: [&producer.chi[..], &bus.alphas[..]].concat(),
                twist,
                image_weight: a.mul(sided, image.weight),
                image_point: image.point.clone(),
            },
            value: table_sumcheck.residual,
        }
    }
}

impl<E> From<MatrixClaim<E>> for Claim<MatrixForm<E>, E> {
    fn from(claim: MatrixClaim<E>) -> Self {
        Self {
            point: claim.form,
            value: claim.value,
        }
    }
}

impl Program {
    /// Settle the claims the verifier's core left, on the program's bytecode table and RAM image, and on each circuit's matrices.
    ///
    /// # Errors
    ///
    /// - A malformed claim: one whose shape no proof of this program gives.
    /// - A false claim: the stage whose identity it completes, the table constraints or the circuit's lincheck.
    #[tracing::instrument(name = "Check deferred", skip_all)]
    #[doc(hidden)]
    pub fn check_deferred(&self, claims: &DeferredClaims) -> Result<(), CpuError> {
        if claims.circuits.len() != N_FLOCKS {
            return Err(CpuError::MalformedClaim(MalformedClaim::CircuitCount {
                expected: N_FLOCKS,
                got: claims.circuits.len(),
            }));
        }

        let program = (claims.program.point)
            .evaluate(&self.view())
            .ok_or(CpuError::MalformedClaim(MalformedClaim::ProgramPoint))?;
        if program != claims.program.value {
            return Err(CpuError::Constraint(ConstraintError::FinalMismatch));
        }

        for (f, claim) in FlockId::ALL.into_iter().zip(&claims.circuits) {
            let (table, part) = (f.table().name(), f.part());
            if !f.shape().fits(&claim.point) {
                return Err(CpuError::MalformedClaim(MalformedClaim::MatrixForm { table, part }));
            }
            if claim.point.evaluate(f.circuit()) != claim.value {
                return Err(CpuError::Flock {
                    table,
                    part,
                    error: FlockError::Lincheck(LincheckError::SumcheckMismatch),
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Region;
    use crate::rv::asm::*;
    use primitives::multilinear::{eq_table, mle_eval};
    use primitives::test_util::Rng;

    #[test]
    fn the_twisted_bytecode_claim_is_the_per_bit_claims() {
        // Bit i's claim is the table at (phi^(-i)(chi), alpha) twisted by phi^i, and the batch is their sum.
        let text = Asm::new()
            .li(Reg::T0, 0x0123_4567_89ab_cdef)
            .i(Addi, Reg::T1, Reg::T0, -77)
            .r(Xor, Reg::A0, Reg::T0, Reg::T1)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let rv = program.rv();
        let kbc = crate::log2_strict_usize(rv.entries().len());
        let mut rng = Rng::new(5);
        let (chi, alphas) = (rng.ext_vec(kbc), rng.ext_vec(N_TUPLE_BITS));
        let weights = leaf::fingerprint_weights(&alphas);
        let tuple = Lookup::Bytecode.tuple(&program.view());
        let table = Lookup::Bytecode.table(&program.view());

        // `c(x) = T(x, alpha)`, raised to `2^i` entry by entry: bit `i`'s public column.
        let eq = eq_table(&chi);
        let mut c: Vec<F192> = (0..rv.entries().len())
            .map(|x| (0..1 << N_TUPLE_BITS).fold(F192::ZERO, |acc, s| acc + weights[s].mul_base(table[(s << kbc) + x])))
            .collect();
        let frobenius = |y: F192, times: usize| (0..times).fold(y, |y, _| y.square());
        let bits = 7;
        let mut per_bit = Vec::with_capacity(bits);
        for i in 0..bits {
            let d = eq.iter().zip(&c).fold(F192::ZERO, |acc, (&e, &v)| acc + e * v);
            let unit: Vec<F192> = (0..=i).map(|j| if j == i { F192::ONE } else { F192::ZERO }).collect();
            assert_eq!(leaf::producer_public_twist(&tuple, &weights, &chi, &unit), d, "bit {i}");
            let twisted: Vec<F192> = chi
                .iter()
                .map(|&z| frobenius(z, 192 - i))
                .chain(alphas.clone())
                .collect();
            assert_eq!(frobenius(mle_eval(&table, &twisted), i), d, "bit {i} at one point");
            per_bit.push(d);
            c.iter_mut().for_each(|v| *v = v.square());
        }
        let twist = rng.ext_vec(bits);
        let batched = (twist.iter().zip(&per_bit)).fold(F192::ZERO, |acc, (&mu, &d)| acc + mu * d);
        assert_eq!(leaf::producer_public_twist(&tuple, &weights, &chi, &twist), batched);
    }
}
