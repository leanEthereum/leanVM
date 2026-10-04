//! The verifier's core of one RISC-V proof, in rows: every check that depends on the proof.

use super::flock::Reduction;
use super::whir::Opening;
use super::{Rows, infallible};
use crate::arith::{Arith, Verifier};
use crate::class_flock;
use crate::cpu::{CpuError, DeferredClaims, Layout, Program, TableReduction};
use crate::pcs::Rate;
use crate::rec::circuit::{Builder, Dw, Ew, Kw};
use crate::rec::transcript::{ProofSource, Transcript};
use crate::tables::{self, Clock, N_TABLES};
use ::pcs::pack::PACKING_WIDTH;
use ::pcs::stack_open::{RingSwitchVerify, RingSwitchVerifyClaim};
use primitives::field::F192;

/// What fixes the rows of a RISC-V proof's verifier: the program, each table's height, and the commitment's rate.
///
/// Two proofs of one shape are verified by one circuit.
pub struct ProofShape<'p> {
    program: &'p Program,
    taus: [usize; N_TABLES],
    rate: Rate,
    layout: Layout,
}

/// What the core leaves as wires.
pub struct CoreRows {
    /// The claims on the program's fixed polynomials and on each circuit's matrices, which the core does not settle.
    pub claims: DeferredClaims<Ew>,
    /// The transcript's final state, which binds every scalar the proof sent.
    pub state: Dw,
}

impl<'p> ProofShape<'p> {
    /// The shape of a proof of a program, from its tables' base-two logarithms of rows and its rate.
    ///
    /// # Errors
    ///
    /// Refuses what the native verifier refuses of an announcement: a height out of range, or a witness the commitment does not take.
    pub fn new(program: &'p Program, taus: [usize; N_TABLES], rate: Rate) -> Result<Self, CpuError> {
        let layout = Layout::announced(program.rv(), taus)?;
        Ok(Self {
            program,
            taus,
            rate,
            layout,
        })
    }

    /// The program.
    pub const fn program(&self) -> &'p Program {
        self.program
    }

    /// Each table's base-two logarithm of rows.
    pub const fn taus(&self) -> &[usize; N_TABLES] {
        &self.taus
    }

    /// The commitment's rate.
    pub const fn rate(&self) -> Rate {
        self.rate
    }

    /// The verifier's core of a proof of this shape returning `output`, read from `source`, as rows of `b`.
    ///
    /// The rows check everything the native core checks, and leave its deferred claims as wires.
    pub fn verify_core(&self, b: &mut Builder, output: [Kw; 4], source: ProofSource<'_>) -> CoreRows {
        let iv = b.d_const(self.program.fs_seed().map(|w| w.0));
        let first = b.k_to_e([output[0], output[1], output[2]]);
        let mut t = Transcript::new(b, iv, (first, output[3]), source);
        let mut r = Rows::new(b, &mut t);

        let clock = r.scope("announcement", |r| self.read_announcement(r));
        let root = r.t.next_root(r.b);
        let output = output.map(|o| r.b.k_to_e1(o));
        let reduced = r.scope("bus and tables", |r| {
            infallible(self.layout.reduce_tables(r, clock, &output))
        });
        let reductions: Vec<Reduction> = (0..class_flock::N_FLOCKS)
            .map(|f| {
                let (table, part) = class_flock::flock(f);
                let name = format!("flock {} {part:?}", tables::ClassSpec::ALL[table].name);
                r.scope(name, |r| Reduction::replay(r, class_flock::shape(f), self.taus[table]))
            })
            .collect();

        r.scope("opening", |r| self.open(r, root, &reductions, &reduced));
        if !r.t.finished() {
            r.scope("transcript", |r| {
                r.b.fail("the proof has data the verifier never reads");
            });
        }

        let circuits = reductions.into_iter().map(|reduction| reduction.matrix).collect();
        CoreRows {
            claims: DeferredClaims {
                program: reduced.program,
                circuits,
            },
            state: t.state(),
        }
    }

    /// The one opening: the point claims, then the ring-switched regions, each packed witness then each producer's multiplicity column.
    fn open(&self, r: &mut Rows<'_, '_>, root: Dw, reductions: &[Reduction], reduced: &TableReduction<Ew>) {
        let zero = r.zero();
        let bits: Vec<Vec<Ew>> = (reduced.producers.iter())
            .map(|claims| claims.evals_padded_with(PACKING_WIDTH, zero))
            .collect();
        let witnesses = reductions.iter().enumerate().map(|(f, reduction)| {
            let window = self.layout.witness_window(f);
            ::flock::reduction::ring_switch_verify(window.n_vars, window.offset, &reduction.slice)
        });
        let producers = (self.layout.producers.iter().zip(&reduced.producers).zip(&bits)).map(|((p, claims), bits)| {
            let window = self.layout.multiplicity_window(p);
            RingSwitchVerify {
                offset: window.offset,
                qflock_vars: window.n_vars,
                claims: vec![RingSwitchVerifyClaim {
                    suffix_point: &claims.chi,
                    s_hat_v: bits.as_slice().try_into().expect("a multiplicity has at most 64 bits"),
                }],
            }
        });
        let rings: Vec<RingSwitchVerify<'_, Ew>> = witnesses.chain(producers).collect();
        let opening = Opening {
            slots: &reduced.slots,
            rings: &rings,
            shape: self.layout.shape,
            log_inv_rate: self.rate.log_inv_rate().into(),
        };
        opening.verify(r, root);
    }

    /// The announced sizes: every height and the rate the shape's, the final clock a live clock at slot zero.
    ///
    /// Returns the clock, which closes the run's last state on the bus.
    fn read_announcement(&self, r: &mut Rows<'_, '_>) -> Ew {
        let sizes = self.taus.into_iter().chain([usize::from(self.rate.log_inv_rate())]);
        for size in sizes {
            let x = infallible(r.next_scalar());
            r.b.eq_e_const(x, F192::new(size as u64, 0, 0));
        }
        let clock = infallible(r.next_scalar());
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
