//! The verifier's core of one RISC-V proof, in rows: every check that depends on the proof.

use super::{Rows, infallible};
use crate::cpu::{Announcement, CpuError, DeferredClaims, Layout, Program};
use crate::pcs::Rate;
use crate::rec::circuit::{Builder, Dw, Ew, Kw};
use crate::rec::transcript::{ProofSource, Transcript};
use crate::tables::{Clock, PerTable};
use fiat_shamir::arith::Verifier;

/// What fixes the rows of a RISC-V proof's verifier: the program, each table's height, and the commitment's rate.
///
/// Two proofs of one shape are verified by one circuit.
pub struct ProofShape<'p> {
    program: &'p Program,
    taus: PerTable<usize>,
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
    pub fn new(program: &'p Program, taus: PerTable<usize>, rate: Rate) -> Result<Self, CpuError> {
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
    pub const fn taus(&self) -> &PerTable<usize> {
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

        let clock = {
            r.begin_scope(fiat_shamir::arith::Stage::Announcement);
            let scoped_result = self.read_announcement(&mut r);
            r.end_scope();
            scoped_result
        };
        let output = output.map(|o| r.b.k_to_e1(o));
        let claims = infallible(self.layout.verify_core(&mut r, clock, &output, self.rate));
        CoreRows {
            claims,
            state: t.commitment(b),
        }
    }

    /// The announced sizes: every height and the rate the shape's, the final clock a live clock at slot zero.
    ///
    /// Returns the clock, which closes the run's last state on the bus.
    fn read_announcement(&self, r: &mut Rows<'_, '_>) -> Ew {
        for size in Announcement::sizes(&self.taus, self.rate) {
            let x = infallible(r.next_scalar());
            r.b.eq_e_const(x, size);
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
