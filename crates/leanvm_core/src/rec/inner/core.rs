//! `cpu::Program::verify_core` as rows: every check that depends on the proof, leaving the program's and
//! the circuits' claims as wires.

use super::bus::{opening_claims, read_announcement, table_sumcheck, verify_balance};
use super::pcs::{RingMode, RingShare};
use super::{MatrixClaim, ProgramClaim, RingRegion, SliceClaim};
use crate::class_flock;
use crate::cpu::{Layout, Program};
use crate::rec::circuit::{Builder, Dw, Ew, Kw};
use crate::rec::transcript::{Source, Transcript};
use crate::tables::{self, N_TABLES};

/// What fixes an inner proof's circuit: its program, its tables' heights and its rate.
#[derive(Clone, Copy)]
pub struct Shape<'p> {
    pub program: &'p Program,
    pub taus: [usize; N_TABLES],
    pub log_inv_rate: usize,
}

/// What the core leaves: the claims on the program and on the circuits, the ring-switched claims' share of
/// the opening when the circuit leaves it as a hint, with what locates those claims beyond the deferred claims
/// (each flock claim's outer coordinates and the bytecode multiplicities' bits), and the transcript's final
/// state, which binds every scalar the proof sent.
pub struct Core {
    pub program: ProgramClaim,
    pub circuits: Vec<MatrixClaim>,
    pub ring: Option<RingShare>,
    pub x_outer: Vec<Vec<Ew>>,
    pub bits: Vec<Ew>,
    pub state: Dw,
}

/// The transcript seeded with the program's digest and the output, the four words `output`.
fn seed<'a>(b: &mut Builder, program: &Program, output: [Kw; 4], source: Source<'a>) -> Transcript<'a> {
    let iv = b.d_const(program.fs_seed().map(|w| w.0));
    let first = b.k_to_e([output[0], output[1], output[2]]);
    Transcript::new(b, iv, (first, output[3]), source)
}

/// The core of the verifier of one inner proof of `shape`, read from `source`, run against `output`, the
/// opening's ring-switched share settled as `ring` says.
pub fn verify_core(b: &mut Builder, shape: &Shape, output: [Kw; 4], source: Source, ring: RingMode) -> Core {
    let mut t = seed(b, shape.program, output, source);
    let ts = b.scope("announcement", |b| {
        read_announcement(b, &mut t, &shape.taus, shape.log_inv_rate)
    });
    let l = Layout::new(shape.program.rv(), shape.taus, 0);
    let root = t.next_root(b);
    let bus = b.scope("bus", |b| verify_balance(b, &mut t, &l, ts));
    let (tables_claims, program) = b.scope("table sumcheck", |b| table_sumcheck(b, &mut t, &l, &bus));
    let output_e: [Ew; 4] = output.map(|o| b.k_to_e1(o));
    let slots = opening_claims(b, &l, bus.claims, &tables_claims, &output_e);

    let mut slices: Vec<SliceClaim> = Vec::with_capacity(class_flock::N_FLOCKS);
    let mut circuits = Vec::with_capacity(class_flock::N_FLOCKS);
    let mut x_outer = Vec::with_capacity(class_flock::N_FLOCKS);
    for f in 0..class_flock::N_FLOCKS {
        let (table, part) = class_flock::flock(f);
        let (slice, matrix) = b.scope(format!("flock {} {part:?}", tables::CLASSES[table].name), |b| {
            super::flock::verify_reduction(b, &mut t, class_flock::shape(f), l.taus[table])
        });
        x_outer.push(slice.suffix_point[matrix.r_inner_rest.len()..].to_vec());
        slices.push(slice);
        circuits.push(matrix);
    }

    // The ring-switched regions: each packed witness, then the bytecode's multiplicity column.
    let mut rings: Vec<RingRegion> = slices
        .into_iter()
        .enumerate()
        .map(|(f, slice)| {
            let window = l.witness_window(f);
            RingRegion {
                offset: window.offset,
                qflock_vars: window.n_vars,
                claims: vec![slice],
            }
        })
        .collect();
    let zero = b.zero();
    for (p, (chi, bits)) in l.producers.iter().zip(&tables_claims.claims[N_TABLES..]) {
        let window = l.multiplicity_window(p);
        let mut s_hat_v = bits.clone();
        s_hat_v.resize(::pcs::pack::PACKING_WIDTH, zero);
        rings.push(RingRegion {
            offset: window.offset,
            qflock_vars: window.n_vars,
            claims: vec![SliceClaim {
                suffix_point: chi.clone(),
                s_hat_v,
            }],
        });
    }

    let share = b.scope("opening", |b| {
        super::pcs::verify(b, &mut t, &slots, &rings, l.shape, shape.log_inv_rate, root, ring)
    });
    if !t.finished() {
        b.scope("transcript", |b| b.fail("the proof has data the verifier never reads"));
    }
    let bits = tables_claims.claims[N_TABLES].1.clone();
    Core {
        program,
        circuits,
        ring: share,
        x_outer,
        bits,
        state: t.state(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::Rate;
    use crate::rv::asm::*;

    /// The whole core in rows leaves the native core's claims, on the proof and from the shape alike.
    #[test]
    fn the_circuit_leaves_the_native_deferred_claims() {
        let text = Asm::new()
            .li(Reg::T0, 7)
            .li(Reg::T1, 9)
            .r(Xor, Reg::A0, Reg::T0, Reg::T1)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        let program = Program::new(&text, crate::rv::Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program");
        let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
        let native = program.verify_core(&output, &proof).expect("an honest proof");
        let raw = program.verify_to_raw(&output, &proof).expect("an honest proof");
        let shape = Shape {
            program: &program,
            taus: std::array::from_fn(|i| proof.stream[i].c0 as usize),
            log_inv_rate: 1,
        };
        let build = |source: Source| {
            let mut b = Builder::new();
            let out = output.map(|o| b.free_k(o));
            let core = verify_core(&mut b, &shape, out, source, RingMode::Prove);
            (b, core)
        };
        let (b, core) = build(Source::Proof(&raw));
        let e = |ws: &[Ew]| ws.iter().map(|&w| b.e(w)).collect::<Vec<_>>();
        assert_eq!(b.e(core.program.value), native.program.value);
        assert_eq!(e(&core.program.twist), native.program.terms[0].1.twist);
        for (c, n) in core.circuits.iter().zip(&native.circuits) {
            assert_eq!(b.e(c.value), n.value);
            assert_eq!(e(&c.s_hat_v), n.terms[0].1.s_hat_v);
            assert_eq!(e(&c.r_inner_rest), n.terms[0].1.r_inner_rest);
        }
        let (circuit, _, failures) = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        assert_eq!(circuit, build(Source::Shape).0.finish().0);
    }
}
