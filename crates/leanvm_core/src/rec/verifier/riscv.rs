//! The verifier's core of one RISC-V proof, in rows: every check that depends on the proof.

use super::{Rows, infallible};
use crate::cpu::{Announcement, CpuError, DeferredClaims, Layout, Program};
use crate::rec::circuit::{Builder, Dw, Ew, Kw};
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rec::tree::LeafShape;
use crate::tables::Clock;
use fiat_shamir::arith::Verifier;
use zk::{Recorder, Value};

/// What fixes the rows of a RISC-V proof's verifier: the program, and the shape its proofs announce.
///
/// Two proofs of one shape are verified by one circuit.
pub struct ProofShape<'p> {
    /// The program.
    program: &'p Program,
    /// Each table's height, the commitment's rate, and whether the proofs are zero knowledge.
    shape: LeafShape,
    /// The layout the shape announces.
    layout: Layout,
}

/// What the core leaves as wires.
pub struct CoreRows {
    /// The claims on the program's fixed polynomials and on each circuit's matrices, which the core does not settle.
    pub claims: DeferredClaims<Ew>,
    /// A digest the transcript draws once the proof is read, which binds every message the proof sent.
    pub state: Dw,
}

impl<'p> ProofShape<'p> {
    /// The rows' shape for proofs of a program of the given shape.
    ///
    /// # Errors
    ///
    /// Refuses what the native verifier refuses of an announcement: a height out of range, or a witness the commitment does not take.
    pub fn new(program: &'p Program, shape: LeafShape) -> Result<Self, CpuError> {
        let layout = Layout::announced(program.rv(), *shape.taus(), shape.kind())?;
        Ok(Self { program, shape, layout })
    }

    /// The program.
    pub const fn program(&self) -> &'p Program {
        self.program
    }

    /// The shape the proofs announce.
    pub const fn shape(&self) -> LeafShape {
        self.shape
    }

    /// The verifier's core of a proof of this shape returning `output`, read from `source`, as rows of `b`.
    ///
    /// The rows check everything the native core checks, and leave its deferred claims as wires.
    pub fn verify_core(&self, b: &mut Builder, output: [Kw; 4], source: ProofSource<'_>) -> CoreRows {
        if self.shape.is_zero_knowledge() {
            return self.verify_core_zk(b, output, source);
        }
        let mut t = Transcript::new(b, &self.program.session(), &output, source);
        let mut r = Rows::new(b, &mut t);

        let clock = {
            r.begin_scope(fiat_shamir::arith::Stage::Announcement);
            let scoped_result = self.read_announcement(&mut r);
            r.end_scope();
            scoped_result
        };
        let output = output.map(|o| r.b.k_to_e1(o));
        let claims = infallible(self.layout.verify_core(&mut r, clock, &output, self.shape.rate()));
        CoreRows {
            claims,
            state: t.digest(b),
        }
    }

    /// The verifier's core of a zero-knowledge proof, as rows: the native recorder's own code over the rows' arithmetic.
    ///
    /// The recorder makes the same record from wires as from values, so the outer proof is checked in rows as natively.
    ///
    /// It leaves the batched claims of the plain shape, which the tree carries as a plain leaf's.
    fn verify_core_zk(&self, b: &mut Builder, output: [Kw; 4], source: ProofSource<'_>) -> CoreRows {
        let mut t = Transcript::new(b, &self.program.zk_session(), &output, source);
        let (claims, fits) = {
            let mut r = Rows::new(b, &mut t);
            r.begin_scope(fiat_shamir::arith::Stage::Announcement);
            self.read_shape(&mut r);
            r.end_scope();
            let output = output.map(|o| Value::Public(r.b.k_to_e1(o)));
            let mut rec = Recorder::new(r);
            let core = infallible(self.layout.record_core(&mut rec, self.shape.rate(), &output));
            let claims = infallible(core.claims.into_plain(&mut rec));
            // A record too large for the key commitment has no outer proof: the rows then refuse every proof.
            let fits = core.keys.verify_outer(rec).map(|mut r| infallible(r.check_eof()));
            (claims, fits.is_ok())
        };
        if !fits {
            b.fail("the record outgrows the key commitment");
        }
        CoreRows {
            claims,
            state: t.digest(b),
        }
    }

    /// The announced shape: every height and the rate the shape's.
    fn read_shape(&self, r: &mut Rows<'_, '_>) {
        for size in Announcement::sizes(self.shape.taus(), self.shape.rate()) {
            let x = infallible(r.prover_message());
            r.b.eq_e_const(x, size);
        }
    }

    /// The announced sizes: the shape, then the final clock, a live clock at slot zero.
    ///
    /// Returns the clock, which closes the run's last state on the bus.
    fn read_announcement(&self, r: &mut Rows<'_, '_>) -> Ew {
        self.read_shape(r);
        let clock = infallible(r.prover_message());
        let [word, high, top] = r.b.e_to_k(clock);
        r.b.eq_k_const(high, 0);
        r.b.eq_k_const(top, 0);
        // Bit 40 set, every bit above it clear, and the slot bits below the cycle clear.
        let slot_bits = Clock::CYCLE.trailing_zeros() as usize;
        for (i, bit) in r.b.split(word).into_iter().enumerate() {
            if i == Clock::LIVE_BIT as usize {
                r.b.eq_k_const(bit, 1);
            } else if i > Clock::LIVE_BIT as usize || i < slot_bits {
                r.b.eq_k_const(bit, 0);
            }
        }
        clock
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bus::BusError;
    use crate::commitment::Rate;
    use crate::cpu::{
        CpuError, DeferredClaims, Output, Program, Proof, ProofKind, ProvenRun, Prover, UNGROUND_LOG_BYTECODE,
    };
    use crate::rec::circuit::{Builder, Ew, Finished, Unsatisfied};
    use crate::rec::verifier::tests::{scalar, set_scalar};
    use crate::tables::{N_TABLES, PerTable, TableId};

    use crate::rec::transcript::ProofSource;
    use crate::rv::Region;
    use crate::rv::asm::*;
    use fiat_shamir::{ProofTranscript, TranscriptError};

    use pcs::merkle::Openings;

    use primitives::field::F192;

    use std::sync::OnceLock;
    use zk::Randomness;

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

    // One honest proof of the small program.
    struct Fixture {
        program: Program,
        proof: ProofTranscript,
        openings: Vec<Openings>,
        output: Output,
        taus: PerTable<usize>,
        kind: ProofKind,
        native: DeferredClaims,
    }

    // Proven once, shared by every test.
    fn fixture() -> &'static Fixture {
        static FIXTURE: OnceLock<Fixture> = OnceLock::new();
        FIXTURE.get_or_init(|| {
            let program = small_program();
            let run = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");
            Fixture::new(program, run)
        })
    }

    // Proven once, shared by the zero-knowledge tests.
    fn zk_fixture() -> &'static Fixture {
        static FIXTURE: OnceLock<Fixture> = OnceLock::new();
        FIXTURE.get_or_init(|| {
            let program = small_program();
            let run = Prover::new(Rate::MIN)
                .zero_knowledge(Randomness::Fixed([11; 32]))
                .prove(&program, &[])
                .expect("the run halts");
            Fixture::new(program, run)
        })
    }

    // The table heights a proof announces, its first messages.
    fn heights(proof: &ProofTranscript) -> PerTable<usize> {
        PerTable::from_fn(|t: TableId| usize::try_from(scalar(proof, t.index()).c0).expect("a height"))
    }

    // The byte where the flock reductions' first message starts: past the announcement, three anchor-frame constants, the raw root and the anchor value.
    const FLOCK_START: usize = 24 * (N_TABLES + 6) + 32;

    impl Fixture {
        // An honest run of a program, verified natively: its claims, its openings, and the heights it announces.
        //
        // A zero-knowledge proof announces its heights first too.
        fn new(program: Program, run: ProvenRun) -> Self {
            let ProvenRun { proof, output, .. } = run;
            let kind = if proof.is_zero_knowledge() {
                ProofKind::ZeroKnowledge
            } else {
                ProofKind::Plain
            };
            Self {
                native: program.verify_core(output, &proof).expect("an honest proof"),
                openings: program.verify_recording(output, &proof).expect("an honest proof"),
                taus: heights(&proof.0),
                proof: proof.0,
                program,
                output,
                kind,
            }
        }

        // The core's rows over `source`: the builder, holding the wires' values, and the claims the core leaves.
        fn build(&self, source: ProofSource<'_>) -> (Builder, DeferredClaims<Ew>) {
            let leaf = LeafShape::new(self.taus, Rate::MIN, self.kind);
            let shape = ProofShape::new(&self.program, leaf).expect("an honest shape");
            let mut b = Builder::new();
            let output = self.output.words().map(|o| b.free_k(o));
            let core = shape.verify_core(&mut b, output, source);
            (b, core.claims)
        }

        // The byte where the bus's first message starts: the shortest prefix of the proof the flock reductions read whole.
        fn bus_start(&self) -> usize {
            let messages: Vec<usize> = (0..(self.proof.narg.len() - FLOCK_START) / 24).collect();
            FLOCK_START
                + 24 * messages.partition_point(|&m| {
                    let mut prefix = Proof(self.proof.clone(), ProofKind::Plain);
                    prefix.0.narg.truncate(FLOCK_START + 24 * m);
                    matches!(
                        self.program.verify_core(self.output, &prefix),
                        Err(CpuError::Reductions(_))
                    )
                })
        }

        // The checks a forged proof or forged openings fail, in the order the rows meet them.
        fn failures(&self, proof: &ProofTranscript, openings: &[Openings]) -> Vec<String> {
            let failures = self.build(ProofSource::Proof(proof, openings)).0.finish().failures;
            failures.iter().map(Unsatisfied::to_string).collect()
        }
    }

    fn values(b: &Builder, claims: &DeferredClaims<Ew>) -> DeferredClaims {
        claims.map(|w| b.e(w))
    }

    #[test]
    fn the_core_leaves_the_native_deferred_claims() {
        let f = fixture();
        let (b, claims) = f.build(ProofSource::Proof(&f.proof, &f.openings));
        let got = values(&b, &claims);
        assert_eq!(got.program, f.native.program, "the program claim");
        for (i, (got, native)) in got.circuits.iter().zip(&f.native.circuits).enumerate() {
            assert_eq!(got, native, "circuit {i}'s matrix claim");
        }
        assert_eq!(got, f.native);
        f.program.check_deferred(&got).expect("the rows' claims settle");
        let Finished { circuit, failures, .. } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        assert!(
            circuit == f.build(ProofSource::Shape).0.finish().circuit,
            "the shape builds another circuit"
        );
    }

    #[test]
    fn a_tampered_proof_fails_where_the_native_verifier_does() {
        let f = fixture();
        let first = |proof: &ProofTranscript, openings: &[Openings]| {
            f.failures(proof, openings).into_iter().next().unwrap_or_default()
        };

        // The GKR's root, the bus's first message: one bit of its second limb.
        let mut forged = f.proof.clone();
        forged.narg[f.bus_start() + 8] ^= 1;
        let failure = first(&forged, &f.openings);
        assert!(failure.starts_with("bus and tables"), "{failure}");

        // The openings are the rows' witness: a sibling or the last leaf word of the first and the last phase.
        for phase in [0, f.openings.len() - 1] {
            let mut forged = f.openings.clone();
            forged[phase].paths[1][0] ^= 1;
            let failure = first(&f.proof, &forged);
            assert!(failure.starts_with("opening / whir / rows"), "{failure}");

            let mut forged = f.openings.clone();
            let last = forged[phase].leaf_words - 1;
            forged[phase].images[last].0 ^= 1;
            let failure = first(&f.proof, &forged);
            assert!(failure.starts_with("opening / whir / rows"), "{failure}");
        }
    }

    #[test]
    fn a_forged_announcement_is_refused_first() {
        let f = fixture();
        let clock = N_TABLES + 1;
        let ts = scalar(&f.proof, clock);
        let forge = |edit: &dyn Fn(&mut ProofTranscript)| {
            let mut forged = f.proof.clone();
            edit(&mut forged);
            f.failures(&forged, &f.openings).into_iter().next().unwrap_or_default()
        };
        for t in 0..N_TABLES {
            let failure = forge(&|p| set_scalar(p, t, F192::new(scalar(p, t).c0 + 1, 0, 0)));
            assert!(failure.starts_with("announcement"), "height {t}: {failure}");
        }
        let edits: [(&str, F192); 7] = [
            ("the rate", F192::new(2, 0, 0)),
            ("a slot bit", F192::new(ts.c0 | 1, 0, 0)),
            ("no live bit", F192::new(ts.c0 & !(1 << 40), 0, 0)),
            ("a failure bit", F192::new(ts.c0 | 1 << 41, 0, 0)),
            ("the top bit", F192::new(ts.c0 | 1 << 63, 0, 0)),
            ("the second limb", F192::new(ts.c0, 1, 0)),
            ("the third limb", F192::new(ts.c0, 0, 1)),
        ];
        for (i, (what, value)) in edits.into_iter().enumerate() {
            let at = if i == 0 { N_TABLES } else { clock };
            let failure = forge(&|p| set_scalar(p, at, value));
            assert!(failure.starts_with("announcement"), "{what}: {failure}");
        }
        // A live clock at slot zero passes the announcement; the transcript then differs, and the first stage, flock, refuses it.
        let failure = forge(&|p| set_scalar(p, clock, F192::new(ts.c0 + 32, 0, 0)));
        assert!(failure.starts_with("flock"), "a later clock: {failure}");
    }

    // A program past the unground bytecode: its rows check the bus's proof of work, which a smaller program's never meet.
    #[test]
    fn a_large_programs_rows_check_its_grinding() {
        // The exit, then nops nothing runs, enough for one bit of grinding.
        let mut a = Asm::new();
        a.li(Reg::A0, 7).exit();
        for _ in 0..1 << UNGROUND_LOG_BYTECODE {
            a.i(Addi, Reg::ZERO, Reg::ZERO, 0);
        }
        let program = Program::new(&a.finish(), Region::TEXT.base(), vec![], 0, 0).expect("a valid program");
        let run = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");
        let proof = run.proof.clone();
        let f = Fixture::new(program, run);

        // The rows leave the native claims, and the shape builds the same circuit.
        let (b, claims) = f.build(ProofSource::Proof(&f.proof, &f.openings));
        assert_eq!(values(&b, &claims), f.native);
        let Finished { circuit, failures, .. } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        assert!(circuit == f.build(ProofSource::Shape).0.finish().circuit);

        // The nonce is the bus's first message: one the native verifier refuses for missing the work fails at the bus.
        let missed = CpuError::Bus(BusError::Transcript(TranscriptError::PowFailed { bits: 1 }));
        let nonce = f.bus_start();
        let forged = (1..64)
            .map(|step| {
                let mut forged = proof.clone();
                forged.0.narg[nonce] ^= step;
                forged
            })
            .find(|forged| f.program.verify_core(f.output, forged).err() == Some(missed.clone()))
            .expect("half the nonces miss one bit of work");
        let failure = f
            .failures(&forged.0, &f.openings)
            .into_iter()
            .next()
            .unwrap_or_default();
        assert!(failure.starts_with("bus and tables"), "{failure}");
    }

    #[test]
    fn a_zero_knowledge_core_leaves_the_native_deferred_claims() {
        // Invariant: the recorder over rows makes the record the native recorder makes, so the rows leave its claims.
        //
        // Those claims are already batched into the plain shape, and settle as a plain proof's.
        let f = zk_fixture();
        let (b, claims) = f.build(ProofSource::Proof(&f.proof, &f.openings));
        let got = values(&b, &claims);
        assert_eq!(got, f.native);
        f.program.check_deferred(&got).expect("the rows' claims settle");
        let Finished { circuit, failures, .. } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");

        // The record depends on the shape alone: zeros in place of the proof build the same circuit.
        assert!(
            circuit == f.build(ProofSource::Shape).0.finish().circuit,
            "the shape builds another circuit"
        );
    }

    #[test]
    fn a_tampered_zero_knowledge_proof_fails_in_rows() {
        // Mutation: one bit of a hidden scalar, the first past the shape and the two roots; then one of the key opening's.
        //
        //     narg = [N_TABLES + 1 sizes | stack root | key root | hidden scalars ... | outer proof, key opening]
        let f = zk_fixture();
        let first_hidden = 24 * (N_TABLES + 1) + 2 * 32;
        for at in [first_hidden + 8, f.proof.narg.len() - 24] {
            let mut forged = f.proof.clone();
            forged.narg[at] ^= 1;
            let failures = f.build(ProofSource::Proof(&forged, &f.openings)).0.finish().failures;
            assert!(!failures.is_empty(), "byte {at} tampered and the rows hold");
        }
    }
}
