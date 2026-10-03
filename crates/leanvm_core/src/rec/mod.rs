//! Recursion as a circuit: a machine whose program is the fixed list of rows that verify leanVM proofs of
//! given shapes, proven with the same bus, table sumcheck, flock and stacked WHIR as the RISC-V machine.
//!
//! The rows run `cpu::Program::verify_core` on each inner proof ([`inner`]); the outer statement is each
//! inner proof's output, shape and [`DeferredClaims`], which [`verify`] settles natively after the outer
//! proof, exactly as `cpu::Program::verify` settles its own. [`tree`] composes recursion proofs into aggregation
//! trees, whose nodes reduce those claims rather than handing them up.

pub mod circuit;
pub mod inner;
pub mod machine;
pub mod proof;
pub mod transcript;
pub mod tree;

use crate::class_flock;
use crate::cpu::{Claim, CpuError, DeferredClaims, Layout, Program, ProgramPoint};
use crate::pcs::Rate;
use crate::tables::{self, N_TABLES};
use circuit::{Builder, Circuit, Ew, Limbs};
use fiat_shamir::transcript::{Proof, RawProof};
use flock::lincheck::MatrixForm;
use inner::core::{Shape, verify_core};
use primitives::field::{F64, F192};
use transcript::Source;

/// The domain of the outer transcript's seed, versioned with the circuit.
const DOMAIN: &[u8] = b"leanvm-recursion-1";

/// An inner proof as the recursion prover takes it: its program, its proof with every Merkle path written
/// out, and the output it claims.
pub struct InnerProof<'a> {
    pub program: &'a Program,
    pub proof: RawProof,
    pub output: [u64; 4],
}

impl<'a> InnerProof<'a> {
    /// An inner proof, verified natively to write its Merkle paths out.
    ///
    /// # Errors
    ///
    /// Refuses a proof the native verifier refuses.
    pub fn new(program: &'a Program, proof: &Proof, output: [u64; 4]) -> Result<Self, CpuError> {
        Ok(Self {
            program,
            proof: program.verify_to_raw(&output, proof)?,
            output,
        })
    }
}

/// What the outer proof states about one inner proof: that a proof of this shape verifies to `output`, up to
/// `claims`, which the outer verifier settles against the program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InnerStatement {
    pub output: [u64; 4],
    pub taus: [usize; N_TABLES],
    pub log_inv_rate: usize,
    pub claims: DeferredClaims,
    pub ring: RingClaims,
}

/// What the ring-switched claims of an inner proof's opening put into its target and its terminal weight,
/// which the outer verifier recomputes from the claims (`pcs::stack_open`): the map's and the batching
/// challenges, the terminal point, both shares, and what locates the claims beyond the deferred claims (each
/// flock claim's outer coordinates, the bytecode multiplicities' bits).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingClaims {
    pub map: [F192; 6],
    pub lambda: F192,
    pub point: Vec<F192>,
    pub target: F192,
    pub weight: F192,
    pub x_outer: Vec<Vec<F192>>,
    pub bits: Vec<F192>,
}

impl InnerStatement {
    /// How many words of the outer statement it is.
    pub fn n_words(&self) -> usize {
        4 + claim_words(&self.claims).len() + ring_words(&self.ring).len()
    }
}

/// A proof that every inner proof verifies, and what it states about each.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursionProof {
    pub inners: Vec<InnerStatement>,
    pub proof: Proof,
}

/// Why recursion refuses.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RecursionError {
    /// An inner proof's announcement names no shape a proof can have.
    #[error("inner proof {index} has no valid shape")]
    Shape { index: usize },
    /// An inner proof does not verify: the circuit's check named here fails on it.
    #[error("inner proof does not verify: {0}")]
    Unsatisfied(String),
    /// The outer proof does not verify.
    #[error(transparent)]
    Outer(#[from] proof::RecError),
    /// An inner proof's deferred claims are false.
    #[error("inner proof {index}: {error}")]
    Deferred { index: usize, error: CpuError },
    /// An inner proof's ring-switched claims do not put what the statement says into its opening.
    #[error("inner proof {index}: the ring-switched claims' shares are wrong")]
    Ring { index: usize },
    /// The statement does not match the programs it is checked against.
    #[error("the statement names {got} inner proofs, and {expected} programs are given")]
    Arity { expected: usize, got: usize },
}

/// The shape a proof announces: its tables' heights and its rate, the first scalars of its stream.
pub fn announced_shape(stream: &[F192]) -> Option<([usize; N_TABLES], usize)> {
    let word = |i: usize| -> Option<usize> {
        let x = stream.get(i)?;
        (x.c1 == 0 && x.c2 == 0).then_some(())?;
        usize::try_from(x.c0).ok()
    };
    let mut taus = [0; N_TABLES];
    for (i, tau) in taus.iter_mut().enumerate() {
        *tau = word(i)?;
    }
    Some((taus, word(N_TABLES)?))
}

/// Whether a proof of `program` can have this shape (`cpu::Announcement::read` and `layout`).
pub fn valid_shape(program: &Program, taus: &[usize; N_TABLES], log_inv_rate: usize) -> bool {
    let heights = tables::CLASSES
        .iter()
        .zip(taus)
        .all(|(spec, &tau)| (class_flock::n_blocks_log(spec, 1)..=crate::cpu::MAX_LOG_ROWS).contains(&tau));
    let rate = u8::try_from(log_inv_rate).is_ok_and(|r| Rate::new(r).is_ok());
    heights && rate && {
        let mu = Layout::new(program.rv(), *taus, 0).shape.mu;
        (crate::pcs::MIN_MU..=crate::pcs::MAX_MU).contains(&mu)
    }
}

/// Whether `claims` have the one term and the lengths a proof of this shape leaves, so that their words
/// parse one way.
fn well_formed(program: &Program, taus: &[usize; N_TABLES], claims: &DeferredClaims, ring: &RingClaims) -> bool {
    let l = Layout::new(program.rv(), *taus, 0);
    let [p] = &l.producers[..] else {
        unreachable!("one lookup array, the bytecode")
    };
    let program_ok = match &claims.program.terms[..] {
        [(one, point)] => {
            *one == F192::ONE
                && point.bytecode.len() == p.kappa + crate::leaf::N_TUPLE_BITS
                && point.twist.len() == p.bits
                && point.image_point.len() == program.rv().log_ram()
        }
        _ => false,
    };
    let ring_ok = ring.point.len() == l.shape.mu
        && ring.bits.len() == p.bits
        && ring.x_outer.len() == class_flock::N_FLOCKS
        && ring.x_outer.iter().enumerate().all(|(f, x)| {
            let rest = class_flock::shape(f).k_log - flock::zerocheck::K_SKIP;
            rest + x.len() == l.witness_window(f).n_vars
        });
    program_ok
        && ring_ok
        && claims.circuits.len() == class_flock::N_FLOCKS
        && claims.circuits.iter().enumerate().all(|(f, c)| match &c.terms[..] {
            [(one, form)] => {
                let rest = class_flock::shape(f).k_log - flock::zerocheck::K_SKIP;
                *one == F192::ONE
                    && form.x_inner_rest.len() == rest
                    && form.r_inner_rest.len() == rest
                    && form.s_hat_v.len() == 1 << flock::zerocheck::K_SKIP
            }
            _ => false,
        })
}

/// Whether the ring claims' shares are what their claims put into the opening: the flock claims at their
/// matrix forms' column points then their outer coordinates, with their slices; then the bytecode
/// multiplicities' bits at the table sumcheck's point. `s` is well formed.
fn ring_shares_hold(program: &Program, s: &InnerStatement) -> bool {
    let l = Layout::new(program.rv(), s.taus, 0);
    let [p] = &l.producers[..] else {
        unreachable!("one lookup array, the bytecode")
    };
    let r = &s.ring;
    let mut bits = r.bits.clone();
    bits.resize(::pcs::pack::PACKING_WIDTH, F192::ZERO);
    let flocks = s.claims.circuits.iter().zip(&r.x_outer).map(|(c, x)| {
        let form = &c.terms[0].1;
        ([&form.r_inner_rest[..], x].concat(), &form.s_hat_v[..])
    });
    let producer = (s.claims.program.terms[0].1.bytecode[..p.kappa].to_vec(), &bits[..]);
    let claims: Vec<(Vec<F192>, &[F192])> = flocks.chain(std::iter::once(producer)).collect();
    let windows = (0..class_flock::N_FLOCKS)
        .map(|f| l.witness_window(f))
        .chain(std::iter::once(l.multiplicity_window(p)));
    let regions: Vec<(usize, usize, Vec<&[F192]>)> = windows
        .zip(&claims)
        .map(|(w, (point, _))| (w.offset, w.n_vars, vec![&point[..]]))
        .collect();
    let slices: Vec<&[F192]> = claims.iter().map(|(_, s)| *s).collect();
    inner::pcs::ring_target(&r.map, r.lambda, &slices) == r.target
        && inner::pcs::ring_weight(&r.map, r.lambda, &regions, &r.point) == r.weight
}

/// The deferred claims' wires, in statement order after the output.
fn claim_wires(core: &inner::core::Core) -> Vec<Ew> {
    let p = &core.program;
    let mut w: Vec<Ew> = p.bytecode.clone();
    w.extend(&p.twist);
    w.push(p.image_weight);
    w.extend(&p.image_point);
    w.push(p.value);
    for c in &core.circuits {
        w.push(c.alpha);
        w.push(c.z_skip);
        w.extend(&c.x_inner_rest);
        w.extend(&c.r_inner_rest);
        w.extend(&c.s_hat_v);
        w.push(c.value);
    }
    let r = core
        .ring
        .as_ref()
        .expect("the single-level circuit hints the ring share");
    w.extend(&r.map);
    w.push(r.lambda);
    w.extend(&r.point);
    w.push(r.target);
    w.push(r.weight);
    for x in &core.x_outer {
        w.extend(x);
    }
    w.extend(&core.bits);
    w
}

/// The ring claims as statement words, in [`claim_wires`]' order after the deferred claims.
fn ring_words(r: &RingClaims) -> Vec<F192> {
    let mut w = r.map.to_vec();
    w.push(r.lambda);
    w.extend(&r.point);
    w.push(r.target);
    w.push(r.weight);
    for x in &r.x_outer {
        w.extend(x);
    }
    w.extend(&r.bits);
    w
}

/// The deferred claims as statement words, in [`claim_wires`]' order.
fn claim_words(claims: &DeferredClaims) -> Vec<F192> {
    let mut w = Vec::new();
    for (_, p) in &claims.program.terms {
        w.extend(&p.bytecode);
        w.extend(&p.twist);
        w.push(p.image_weight);
        w.extend(&p.image_point);
    }
    w.push(claims.program.value);
    for c in &claims.circuits {
        for (_, f) in &c.terms {
            w.push(f.alpha);
            w.push(f.z_skip);
            w.extend(&f.x_inner_rest);
            w.extend(&f.r_inner_rest);
            w.extend(&f.s_hat_v);
        }
        w.push(c.value);
    }
    w
}

/// Every word of the statement, in the order the circuit exposes them.
fn statement_words(inners: &[InnerStatement]) -> Vec<Limbs> {
    let mut words = Vec::new();
    for s in inners {
        words.extend(s.output.map(|o| [o, 0, 0, 0]));
        words.extend(
            claim_words(&s.claims)
                .into_iter()
                .chain(ring_words(&s.ring))
                .map(|x| [x.c0, x.c1, x.c2, 0]),
        );
    }
    words
}

/// The outer transcript's seed: the circuit's identity (each inner program and shape), then the statement.
fn seed(programs: &[&Program], inners: &[InnerStatement], statement: &[Limbs]) -> ([F64; 4], [F64; 4]) {
    let mut h = primitives::hash::Hasher::new();
    h.update(DOMAIN);
    h.update(&(inners.len() as u64).to_le_bytes());
    for (program, s) in programs.iter().zip(inners) {
        h.update(program.digest());
        for &tau in &s.taus {
            h.update(&(tau as u64).to_le_bytes());
        }
        h.update(&(s.log_inv_rate as u64).to_le_bytes());
    }
    let iv = fiat_shamir::digest_words(&h.finalize());
    let mut h = primitives::hash::Hasher::new();
    h.update(&(statement.len() as u64).to_le_bytes());
    for word in statement {
        for limb in word {
            h.update(&limb.to_le_bytes());
        }
    }
    (iv, fiat_shamir::digest_words(&h.finalize()))
}

/// The circuit verifying one proof of each shape, and the builder holding its values.
fn build(shapes: &[Shape], sources: &[Source], outputs: &[[u64; 4]]) -> (Builder, Vec<inner::core::Core>) {
    let mut b = Builder::new();
    let mut cores = Vec::with_capacity(shapes.len());
    for (i, ((shape, &source), output)) in shapes.iter().zip(sources).zip(outputs).enumerate() {
        let output = output.map(|o| b.free_k(o));
        for &o in &output {
            b.expose_k(o);
        }
        let core = b.scope(format!("inner {i}"), |b| {
            verify_core(b, shape, output, source, inner::pcs::RingMode::Hint)
        });
        for w in claim_wires(&core) {
            b.expose_e(w);
        }
        cores.push(core);
    }
    (b, cores)
}

/// The native ring claims the core's wires hold.
fn ring_of(b: &Builder, core: &inner::core::Core) -> RingClaims {
    let e = |ws: &[Ew]| ws.iter().map(|&w| b.e(w)).collect::<Vec<_>>();
    let r = core
        .ring
        .as_ref()
        .expect("the single-level circuit hints the ring share");
    RingClaims {
        map: std::array::from_fn(|i| b.e(r.map[i])),
        lambda: b.e(r.lambda),
        point: e(&r.point),
        target: b.e(r.target),
        weight: b.e(r.weight),
        x_outer: core.x_outer.iter().map(|x| e(x)).collect(),
        bits: e(&core.bits),
    }
}

/// The native claims the core's wires hold.
fn claims_of(b: &Builder, core: &inner::core::Core) -> DeferredClaims {
    let e = |ws: &[Ew]| ws.iter().map(|&w| b.e(w)).collect::<Vec<_>>();
    let p = &core.program;
    DeferredClaims {
        program: Claim::new(
            ProgramPoint {
                bytecode: e(&p.bytecode),
                twist: e(&p.twist),
                image_weight: b.e(p.image_weight),
                image_point: e(&p.image_point),
            },
            b.e(p.value),
        ),
        circuits: core
            .circuits
            .iter()
            .map(|c| {
                Claim::new(
                    MatrixForm {
                        alpha: b.e(c.alpha),
                        z_skip: b.e(c.z_skip),
                        x_inner_rest: e(&c.x_inner_rest),
                        r_inner_rest: e(&c.r_inner_rest),
                        s_hat_v: e(&c.s_hat_v),
                    },
                    b.e(c.value),
                )
            })
            .collect(),
    }
}

/// The shapes of the inner proofs, from their announcements.
fn shapes_of<'p>(inners: &[InnerProof<'p>]) -> Result<Vec<Shape<'p>>, RecursionError> {
    inners
        .iter()
        .enumerate()
        .map(|(index, p)| {
            let (taus, log_inv_rate) = announced_shape(&p.proof.stream).ok_or(RecursionError::Shape { index })?;
            if !valid_shape(p.program, &taus, log_inv_rate) {
                return Err(RecursionError::Shape { index });
            }
            Ok(Shape {
                program: p.program,
                taus,
                log_inv_rate,
            })
        })
        .collect()
}

/// The circuit verifying `inners`, and what it states about them.
///
/// # Errors
///
/// Refuses an inner proof with no valid shape, and one that does not verify.
pub fn circuit_of(
    inners: &[InnerProof],
) -> Result<(Circuit, circuit::Assignment, Vec<InnerStatement>), RecursionError> {
    let shapes = shapes_of(inners)?;
    let sources: Vec<Source> = inners.iter().map(|p| Source::Proof(&p.proof)).collect();
    let outputs: Vec<[u64; 4]> = inners.iter().map(|p| p.output).collect();
    let (b, cores) = build(&shapes, &sources, &outputs);
    let statements = shapes
        .iter()
        .zip(&cores)
        .zip(&outputs)
        .map(|((shape, core), &output)| InnerStatement {
            output,
            taus: shape.taus,
            log_inv_rate: shape.log_inv_rate,
            claims: claims_of(&b, core),
            ring: ring_of(&b, core),
        })
        .collect();
    let (circuit, assignment, failures) = b.finish();
    if let Some(first) = failures.into_iter().next() {
        return Err(RecursionError::Unsatisfied(first));
    }
    Ok((circuit, assignment, statements))
}

/// Prove that every inner proof verifies, at the outer rate `rate`.
///
/// # Errors
///
/// Refuses an inner proof with no valid shape, and one that does not verify.
pub fn prove(inners: &[InnerProof], rate: Rate) -> Result<RecursionProof, RecursionError> {
    let (circuit, assignment, statements) = circuit_of(inners)?;
    let programs: Vec<&Program> = inners.iter().map(|p| p.program).collect();
    let words = statement_words(&statements);
    debug_assert_eq!(words, assignment.statement, "the statement is what the circuit exposes");
    let (iv, public_input) = seed(&programs, &statements, &words);
    let proof = proof::prove(&circuit, &assignment, iv, public_input, rate);
    Ok(RecursionProof {
        inners: statements,
        proof,
    })
}

/// The circuit verifying proofs of these programs and shapes, built from the shapes alone.
///
/// # Errors
///
/// Refuses a shape no proof can have.
pub fn circuit_for(programs: &[&Program], inners: &[InnerStatement]) -> Result<Circuit, RecursionError> {
    let shapes = programs
        .iter()
        .zip(inners)
        .enumerate()
        .map(|(index, (&program, s))| {
            (valid_shape(program, &s.taus, s.log_inv_rate) && well_formed(program, &s.taus, &s.claims, &s.ring))
                .then_some(Shape {
                    program,
                    taus: s.taus,
                    log_inv_rate: s.log_inv_rate,
                })
                .ok_or(RecursionError::Shape { index })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let sources = vec![Source::Shape; shapes.len()];
    let outputs = vec![[0; 4]; shapes.len()];
    Ok(build(&shapes, &sources, &outputs).0.finish().0)
}

/// Verify that proofs of `programs` verify to the outputs `proof` states, the outer proof at
/// `log_inv_rate`: the outer proof, then each inner proof's deferred claims against its program.
///
/// # Errors
///
/// Returns the first check that refuses.
pub fn verify(programs: &[&Program], proof: &RecursionProof, log_inv_rate: usize) -> Result<(), RecursionError> {
    if programs.len() != proof.inners.len() {
        return Err(RecursionError::Arity {
            expected: programs.len(),
            got: proof.inners.len(),
        });
    }
    let circuit = circuit_for(programs, &proof.inners)?;
    let words = statement_words(&proof.inners);
    let (iv, public_input) = seed(programs, &proof.inners, &words);
    proof::verify(&circuit, &words, iv, public_input, log_inv_rate, &proof.proof)?;
    for (index, (program, s)) in programs.iter().zip(&proof.inners).enumerate() {
        program
            .check_deferred(&s.claims)
            .map_err(|error| RecursionError::Deferred { index, error })?;
        if !ring_shares_hold(program, s) {
            return Err(RecursionError::Ring { index });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::asm::*;

    fn program() -> Program {
        let text = Asm::new()
            .li(Reg::T0, 7)
            .li(Reg::T1, 9)
            .r(Xor, Reg::A0, Reg::T0, Reg::T1)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        Program::new(&text, crate::rv::Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
    }

    /// Two proofs of one program verify in one outer proof, and a statement or an outer proof changed
    /// anywhere is refused.
    #[test]
    fn an_outer_proof_verifies_and_binds_its_statement() {
        let program = program();
        let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
        let inner = || InnerProof::new(&program, &proof, output).expect("an honest proof");
        let rec = prove(&[inner(), inner()], Rate::MIN).expect("honest inner proofs");
        let programs = [&program, &program];
        verify(&programs, &rec, 1).expect("the outer proof verifies");

        let mut wrong_output = rec.clone();
        wrong_output.inners[1].output[0] ^= 1;
        assert!(verify(&programs, &wrong_output, 1).is_err());

        let mut wrong_ring = rec.clone();
        wrong_ring.inners[0].ring.target += F192::ONE;
        assert!(verify(&programs, &wrong_ring, 1).is_err());

        let mut wrong_claim = rec.clone();
        wrong_claim.inners[0].claims.circuits[3].value += F192::ONE;
        assert!(verify(&programs, &wrong_claim, 1).is_err());

        let mut wrong_proof = rec.clone();
        wrong_proof.proof.stream[5] += F192::ONE;
        assert!(verify(&programs, &wrong_proof, 1).is_err());

        assert!(matches!(
            verify(&programs[..1], &rec, 1),
            Err(RecursionError::Arity { .. })
        ));
    }

    /// A forged inner proof leaves the circuit unsatisfied: the outer prover has nothing to prove.
    #[test]
    fn a_forged_inner_proof_has_no_outer_proof() {
        let program = program();
        let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
        let honest = InnerProof::new(&program, &proof, output).expect("an honest proof");
        let forge = |f: &dyn Fn(&mut InnerProof)| {
            let mut forged = InnerProof {
                program: &program,
                proof: honest.proof.clone(),
                output,
            };
            f(&mut forged);
            matches!(prove(&[forged], Rate::MIN), Err(RecursionError::Unsatisfied(_)))
        };
        let scalar = honest.proof.stream.len() / 2;
        assert!(forge(&|p| p.proof.stream[scalar] += F192::ONE), "a tampered scalar");
        assert!(forge(&|p| p.output[0] ^= 1), "a wrong output");
        assert!(forge(&|p| p.proof.merkle[7].path[3][0] ^= 1), "a tampered Merkle path");
        assert!(forge(&|p| p.proof.merkle[2].leaf_data[40].0 ^= 1), "a tampered leaf");
    }
}
