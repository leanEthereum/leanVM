//! The verifier of a leanVM proof as a RISC-V program: recursion on the machine itself.
//!
//! The verifier is written once over an arithmetic and a transcript (`fiat_shamir::arith`).
//!
//! Run over [`record::Gen`], it leaves the list of its steps, which [`lower`] turns into instructions: products on the
//! extension registers, hashes by the compression instruction, the proof read off the advice.
//!
//! The program depends on the shape of the proof it verifies alone, the advice on the proof.

mod lower;
mod record;

use crate::ProgramError;
use crate::cpu::{Announcement, CpuError, DeferredClaims, Layout, Output, Program, Proof};
use crate::pcs::Rate;
use crate::rec::circuit::chain;
use crate::rec::transcript::ProofSource;
use crate::tables::{PerTable, TableId};
use fiat_shamir::arith::Verifier;
use record::Gen;

/// A program verifying proofs of given shapes, and the advice of one such list of proofs.
pub struct VerifierProgram {
    /// The verifier.
    pub program: Program,
    /// The advice: each verified run's output and proof, and the hints.
    pub advice: Vec<u64>,
    /// What the run outputs: the hash of every verified output and of the claims each core leaves.
    pub output: [u64; 4],
    /// What the output is the hash of: each verified run's output, and the claims its proof's core leaves.
    pub verified: Vec<Verified>,
}

/// What a verifier program's run establishes of one proof, short of the claims only that proof's program settles.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verified {
    /// The output of the run the proof is of.
    pub output: Output,
    /// The claims the verifier's core leaves on that run's program and on the circuits.
    pub claims: DeferredClaims,
}

/// The hash a verifier program outputs of what it verified: every output's words, then every claim's limbs.
#[must_use]
pub fn statement_hash(verified: &[Verified]) -> [u64; 4] {
    let mut words: Vec<u64> = verified.iter().flat_map(|v| *v.output.words()).collect();
    for v in verified {
        v.claims.map(|e| words.extend([e.c0, e.c1, e.c2]));
    }
    chain(&words)
}

/// Settle what a verifier program's run leaves open: `output` is the hash of `verified`, and each claim holds on its program.
///
/// A proof of the verifier program with this output, and this check, say every proof it verified is valid.
///
/// # Errors
///
/// Returns an error if the output is not the hash, or a claim is false.
pub fn settle(output: Output, verified: &[(&Program, Verified)]) -> Result<(), SettleError> {
    let all: Vec<Verified> = verified.iter().map(|(_, v)| v.clone()).collect();
    if *output.words() != statement_hash(&all) {
        return Err(SettleError::Output);
    }
    verified
        .iter()
        .try_for_each(|(program, v)| program.check_deferred(&v.claims).map_err(SettleError::Claim))
}

/// One proof to verify: the program it is of, the shape it announces, and the proof itself or nothing.
pub struct Child<'a> {
    /// The program the proof is of.
    pub program: &'a Program,
    /// The base-two logarithm of each table's height.
    pub taus: PerTable<usize>,
    /// The proof's rate.
    pub rate: Rate,
    /// The output of the run the proof is of.
    pub output: Output,
    /// The proof, or its shape alone.
    pub source: ProofSource<'a>,
}

impl VerifierProgram {
    /// The verifier of these proofs, in order.
    ///
    /// With proofs as sources, the advice is theirs; with shapes, it is zeros of the right length and the program is the same.
    ///
    /// # Errors
    ///
    /// Returns an error if a child's heights are not ones its program can announce, or the verifier does not fit a program.
    pub fn build(children: &[Child<'_>]) -> Result<Self, BuildError> {
        let mut g = Gen::new();
        let (mut words, mut left, mut verified) = (Vec::new(), Vec::new(), Vec::new());
        for child in children {
            let layout = Layout::announced(child.program.rv(), child.taus)?;
            let output = g.start(
                child.source,
                child.program.fs_seed().map(|w| w.0),
                *child.output.words(),
            );
            for size in Announcement::sizes(&child.taus, child.rate) {
                g.expect_scalar(size);
            }
            let clock = g.clock();
            let elements = output.map(|k| g.k_to_e(k));
            let claims = layout.verify_core(&mut g, clock, &elements, child.rate)?;
            g.finish().expect("the recorder reads no value");
            debug_assert!(g.finished(), "the verifier read the whole proof");
            words.extend(output);
            claims.map(|e| left.push(e));
            verified.push(Verified {
                output: child.output,
                claims: claims.map(|e| g.e(e)),
            });
        }

        // The output binds what was verified: each run's output and every claim its core leaves.
        let output = g.commit(&words, &left);
        let lowered = lower::lower(&g);
        let advice = g.advice.clone();
        let log_advice = advice.len().next_power_of_two().trailing_zeros() as usize;
        let program = Program::new(
            &lowered.text,
            crate::rv::Region::TEXT.base(),
            Vec::new(),
            lowered.log_ram,
            log_advice,
        )?;
        Ok(Self {
            program,
            advice,
            output,
            verified,
        })
    }

    /// The verifier of these proofs, each a proof at its rate that its program ran to its output.
    ///
    /// # Errors
    ///
    /// Returns an error if a proof does not verify, or the verifier does not fit a program.
    pub fn of(proofs: &[(&Program, Rate, Output, &Proof)]) -> Result<Self, BuildError> {
        let raws = (proofs.iter())
            .map(|&(program, _, output, proof)| program.verify_to_raw(output, proof))
            .collect::<Result<Vec<_>, _>>()?;
        let children: Vec<Child<'_>> = (proofs.iter().zip(&raws))
            .map(|(&(program, rate, output, proof), raw)| Child {
                program,
                taus: heights(proof),
                rate,
                output,
                source: ProofSource::Proof(raw),
            })
            .collect();
        Self::build(&children)
    }
}

/// The table heights a proof announces: its first scalars.
fn heights(proof: &Proof) -> PerTable<usize> {
    PerTable::from_fn(|t: TableId| proof.0.stream.get(t.index()).map_or(0, |s| s.c0 as usize))
}

/// Why what a verifier program's run leaves open does not settle.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SettleError {
    /// The verifier program's output is not the hash of what it is said to have verified.
    #[error("the output is not the hash of the verified outputs and claims")]
    Output,
    /// A claim a verified proof leaves is false.
    #[error("a deferred claim is false: {0}")]
    Claim(CpuError),
}

/// Why a verifier program could not be built.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BuildError {
    /// The shape is not one the verified program can announce, or the recorder's run of the verifier failed.
    #[error(transparent)]
    Shape(#[from] CpuError),
    /// The verifier does not fit a program.
    #[error(transparent)]
    Program(#[from] ProgramError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::{ProvenRun, Prover};
    use crate::rv::asm::*;
    use crate::rv::{Machine, Region};

    // A program with a loop, so that every framework block is read.
    fn small_program() -> Program {
        let text = Asm::new()
            .li(Reg::T0, 0x0123_4567_89ab_cdef)
            .li(Reg::T1, 9)
            .r(Xor, Reg::A0, Reg::T0, Reg::T1)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
    }

    #[test]
    fn the_verifier_program_accepts_an_honest_proof_and_its_run_proves() {
        // Fixture: a proof of the small program, and the verifier program of its shape, built from the proof and from the shape alone.
        let program = small_program();
        let prover = Prover::new(Rate::MIN);
        let ProvenRun { proof, output, .. } = prover.prove(&program, &[]).expect("the run halts");
        let raw = program.verify_to_raw(output, &proof).expect("an honest proof");
        let taus = heights(&proof);
        let child = |source| Child {
            program: &program,
            taus,
            rate: Rate::MIN,
            output,
            source,
        };
        let v = VerifierProgram::build(&[child(ProofSource::Proof(&raw))]).expect("a verifier");
        let shape = VerifierProgram::build(&[child(ProofSource::Shape)]).expect("a verifier");
        assert_eq!(v.program.digest(), shape.program.digest(), "the program is the shape's");

        // The verifier runs to its exit on the honest proof, and outputs the hash of what it verified.
        let stats = v.program.measure(&v.advice).expect("the verifier accepts");
        eprintln!(
            "verifier program: {} cycles, 2^{:.2} committed words, {:?}",
            stats.cycles(),
            (stats.committed as f64).log2(),
            TableId::ALL.map(|t| (t.spec().name, stats.base_counts[t]))
        );

        // Mutation: one bit of each of a few advice words, across the proof: the verifier traps.
        //
        // A slot's fourth word is padding, which nothing reads, so each word taken is a slot's first.
        for at in [4, 40, v.advice.len() / 3, v.advice.len() / 2, v.advice.len() - 4] {
            let at = at - at % 4;
            let mut forged = v.advice.clone();
            forged[at] ^= 1;
            let mut m = Machine::new(v.program.rv(), &forged);
            let outcome = m.run();
            assert!(outcome != Ok(v.output), "advice word {at}: {outcome:?}");
        }

        // The run of the verifier is proven, and that proof verifies: a proof that a proof exists.
        let run = prover.prove(&v.program, &v.advice).expect("the verifier halts");
        assert_eq!(*run.output.words(), v.output);
        assert!(v.program.verify(run.output, &run.proof).is_ok());

        // What the run leaves open is settled against the verified program: the claims are the native core's.
        assert_eq!(
            v.verified[0].claims,
            program.verify_core(output, &proof).expect("an honest proof")
        );
        let verified = [(&program, v.verified[0].clone())];
        assert_eq!(settle(run.output, &verified), Ok(()));

        // Mutation: a claim's value, which the output's hash refuses, and the same with the hash recomputed, which the program refuses.
        let mut forged = v.verified[0].clone();
        forged.claims.program.value += primitives::field::F192::ONE;
        assert!(settle(run.output, &[(&program, forged.clone())]).is_err());
        let rehashed = Output::new(statement_hash(std::slice::from_ref(&forged)));
        assert!(settle(rehashed, &[(&program, forged)]).is_err());
    }
}
