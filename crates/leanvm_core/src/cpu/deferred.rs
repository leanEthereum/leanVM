//! The claims a proof leaves on polynomials that only the program or the VM's circuits
//! fix. [`Program::verify_core`] runs every check that depends on the proof and returns
//! them; [`Program::check_deferred`] evaluates them. Nothing they hold is bound into the
//! transcript, so a recursive verifier can carry them out of the proof it verifies and
//! leave them to whoever holds the program, merging the claims of many proofs into one
//! ([`DeferredClaims::merge`]).
//!
//! Two kinds, each the completion of an identity [`Program::verify`] checks whole:
//!
//! - the table sumcheck's final identity, short of the bytecode producer's public
//!   columns and of RAM's image in its target, which only the program fixes
//!   ([`ProgramPoint`]);
//! - each flock circuit's lincheck terminal identity, short of the bilinear form of its
//!   matrices `A`, `B`, which only the circuit fixes ([`MatrixForm`]). Its `C` is the
//!   identity, whose form is closed and stays in the core.

use super::batch::FormPowers;
use super::layout::Lookup;
use super::{CpuError, Program};
use crate::class_flock;
use crate::constraints;
use crate::leaf::{self, BusVerify, N_TUPLE_BITS, SparseColumn};
use crate::tables;
use flock::lincheck::{self, MatrixForm};
use primitives::field::F192;

/// `Σ_j c_j·f(p_j) = value`: weighted evaluations of one fixed polynomial `f`. One
/// proof's claim has one point of weight one; [`Claim::merge`] makes the claims of
/// several proofs on the same `f` one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim<P> {
    pub terms: Vec<(F192, P)>,
    pub value: F192,
}

impl<P: Clone> Claim<P> {
    /// `f(point) = value`.
    pub fn new(point: P, value: F192) -> Self {
        Self {
            terms: vec![(F192::ONE, point)],
            value,
        }
    }

    /// `Σ_k γ^k·claims[k]`: one claim on their polynomial for all of them. If any of them
    /// is false, so is the merged claim, except with probability `(n − 1)/|E|` over
    /// `gamma`, which the caller draws once the claims are fixed (a recursive verifier
    /// from a transcript that has absorbed them).
    pub fn merge(claims: &[Self], gamma: F192) -> Self {
        let mut power = F192::ONE;
        let mut merged = Self {
            terms: Vec::new(),
            value: F192::ZERO,
        };
        for claim in claims {
            merged
                .terms
                .extend(claim.terms.iter().map(|(c, p)| (power * *c, p.clone())));
            merged.value += power * claim.value;
            power *= gamma;
        }
        merged
    }

    /// The claim against `evaluate`, `None` at a malformed point.
    fn holds(&self, mut evaluate: impl FnMut(&P) -> Option<F192>) -> bool {
        (self.terms.iter())
            .try_fold(F192::ZERO, |acc, (c, p)| Some(acc + *c * evaluate(p)?))
            .is_some_and(|sum| sum == self.value)
    }
}

/// A point of the program's fixed polynomials, at which they take the value
///
/// `Σ_i μ_i·Σ_x eq(χ, x)·T(x, α⃗)^{2^i} + image_weight·image(image_point)`,
///
/// `T(x, α⃗) = Σ_s eq(α⃗, s)·T(x, s)` the stacked bytecode table
/// ([`Lookup::table`]) at entry `x`, and `image` RAM's image then zeros.
///
/// The first sum is the bytecode producer's public columns, multiplicity bit `i`'s
/// being `Σ_x eq(χ, x)·T(x, α⃗)^{2^i}`. Raising to `2^i` is the Frobenius automorphism
/// `φ^i`, so that is `φ^i(T̂(φ^{-i}(χ), α⃗))`, the table at one point twisted by `φ^i`, and
/// the weights `μ_i` take every bit's into one claim on the table at `(χ, α⃗)`.
/// [`leaf::producer_public_twist`] evaluates it through the bits of the table at `χ`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramPoint {
    /// `χ ‖ α⃗`: the table sumcheck's point on the entries, then the bus fingerprint's.
    pub bytecode: Vec<F192>,
    /// `μ_i` per multiplicity bit, lowest first.
    pub twist: Vec<F192>,
    pub image_weight: F192,
    pub image_point: Vec<F192>,
}

impl ProgramPoint {
    /// The value at this point of the program whose bytecode tuple is `tuple`, `None` if
    /// the point is not of its shape.
    fn evaluate(&self, tuple: &[leaf::Coord], kbc: usize, image: &SparseColumn, log_ram: usize) -> Option<F192> {
        if self.bytecode.len() != kbc + N_TUPLE_BITS || self.image_point.len() != log_ram || self.twist.len() > 64 {
            return None;
        }
        let (chi, alphas) = self.bytecode.split_at(kbc);
        let weights = leaf::fingerprint_weights(alphas);
        let bytecode = leaf::producer_public_twist(tuple, &weights, chi, &self.twist);
        Some(bytecode + self.image_weight * image.eval(&self.image_point))
    }
}

/// Everything [`Program::verify_core`] leaves to the program and to the VM's circuits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeferredClaims {
    pub program: Claim<ProgramPoint>,
    /// Per packed witness, in [`class_flock::flock`] order, its circuit's matrix form.
    pub circuits: Vec<Claim<MatrixForm>>,
}

impl DeferredClaims {
    /// [`Claim::merge`] of each claim of proofs of one program, under one `gamma`.
    pub fn merge(claims: &[Self], gamma: F192) -> Self {
        let program: Vec<_> = claims.iter().map(|c| c.program.clone()).collect();
        Self {
            program: Claim::merge(&program, gamma),
            circuits: (0..class_flock::N_FLOCKS)
                .map(|f| {
                    let circuit: Vec<_> = claims.iter().map(|c| c.circuits[f].clone()).collect();
                    Claim::merge(&circuit, gamma)
                })
                .collect(),
        }
    }
}

/// What the table sumcheck's final identity leaves to the program: the bytecode
/// producer's public columns, each multiplicity bit's weighted by what the identity
/// gives it, and RAM's image, which the bus left out of the target and which reaches the
/// final claim through every round's challenge.
pub(super) fn program_claim(
    bus: &BusVerify,
    table_sumcheck: &constraints::Final,
    powers: FormPowers,
) -> Claim<ProgramPoint> {
    let [coefficients] = &bus.producers[..] else {
        unreachable!("one lookup array, the bytecode")
    };
    // The producer's air follows the tables'; its sent columns are its bits `b_i`, and
    // its summand `Σ_i c_i·(1 + b_i·P'_i)` takes each `P'_i` at `c_i·b_i`.
    let air = tables::N_TABLES;
    let (weight, producer) = (table_sumcheck.weights[air], &table_sumcheck.claims[air]);
    let twist = (coefficients.iter().zip(&producer.evals))
        .map(|(&c, &b)| weight * c * powers.push() * b)
        .collect();
    let mut shares = (0..2).flat_map(|s| bus.sparse[s].iter().map(move |share| (s, share)));
    let (Some((side, image)), None) = (shares.next(), shares.next()) else {
        unreachable!("RAM's image is the one sparse column, seeded once")
    };
    Claim::new(
        ProgramPoint {
            bytecode: [&producer.chi[..], &bus.alphas[..]].concat(),
            twist,
            image_weight: table_sumcheck.target_weight * powers.side(side) * image.weight,
            image_point: image.point.clone(),
        },
        table_sumcheck.residual,
    )
}

impl Program {
    /// Evaluate the claims [`Program::verify_core`] left: on the program's bytecode table and
    /// RAM image, and on each flock circuit's matrices. Each is refused as the stage whose
    /// identity it completes, the table constraints or the circuit's lincheck.
    ///
    /// # Errors
    ///
    /// Returns the stage whose identity a false claim completes.
    #[tracing::instrument(name = "Check deferred", skip_all)]
    pub fn check_deferred(&self, claims: &DeferredClaims) -> Result<(), CpuError> {
        let rv = self.rv();
        let tuple = Lookup::Bytecode.tuple(rv);
        let kbc = crate::log2_strict_usize(rv.entries().len());
        let image = SparseColumn::new(rv.log_ram(), &[(0, rv.image())]);
        if !(claims.program).holds(|p| p.evaluate(&tuple, kbc, &image, rv.log_ram())) {
            return Err(CpuError::Constraint(constraints::Error::FinalMismatch));
        }
        assert_eq!(claims.circuits.len(), class_flock::N_FLOCKS, "one claim per circuit");
        for (f, claim) in claims.circuits.iter().enumerate() {
            let circuit = class_flock::circuit(f);
            let rest = circuit.block().k_log - flock::zerocheck::K_SKIP;
            let well_formed = |form: &MatrixForm| {
                form.s_hat_v.len() == 1 << flock::zerocheck::K_SKIP
                    && form.x_inner_rest.len() == rest
                    && form.r_inner_rest.len() == rest
            };
            if !claim.holds(|form| well_formed(form).then(|| form.evaluate(circuit))) {
                let (t, part) = class_flock::flock(f);
                return Err(CpuError::Flock {
                    table: tables::CLASSES[t].name,
                    part,
                    error: flock::verifier::VerifyError::Lincheck(lincheck::VerifyError::SumcheckMismatch),
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::asm::*;
    use primitives::multilinear::{eq_table, mle_eval};

    /// The bytecode claim, taken through the bits of the table at `χ`, is the per-bit
    /// claims it replaces, each the table at `(φ^{-i}(χ), α⃗)` twisted by `φ^i`.
    #[test]
    fn the_twisted_bytecode_claim_is_the_per_bit_claims() {
        let text = Asm::new()
            .li(Reg::T0, 0x0123_4567_89ab_cdef)
            .i(Addi, Reg::T1, Reg::T0, -77)
            .r(Xor, Reg::A0, Reg::T0, Reg::T1)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        let program =
            Program::new(&text, crate::rv::Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let rv = program.rv();
        let kbc = crate::log2_strict_usize(rv.entries().len());
        let mut rng = primitives::test_rng::Rng::new(5);
        let (chi, alphas) = (rng.ext_vec(kbc), rng.ext_vec(N_TUPLE_BITS));
        let weights = leaf::fingerprint_weights(&alphas);
        let tuple = Lookup::Bytecode.tuple(rv);
        let table = Lookup::Bytecode.table(rv);

        // `c(x) = T(x, α⃗)`, raised to `2^i` entry by entry: bit `i`'s public column.
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
