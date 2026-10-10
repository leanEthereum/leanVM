//! The verifier's core of one RISC-V proof, in rows: every check that depends on the proof.

use super::{Rows, infallible};
use crate::cpu::{Announcement, CpuError, DeferredClaims, Layout, Program};
use crate::pcs::Rate;
use crate::rec::circuit::{Builder, Dw, Ew, Kw};
use crate::rec::transcript::{ProofSource, Transcript};
use crate::tables::{Clock, PerTable};
use fiat_shamir::arith::{Arith, Verifier};

/// What fixes the rows of a RISC-V proof's verifier: the program, each table's height, the register log's, and the
/// commitment's rate.
///
/// Two proofs of one shape are verified by one circuit.
pub struct ProofShape<'p> {
    program: &'p Program,
    taus: PerTable<usize>,
    log_cycles: usize,
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
    /// The shape of a proof of a program, from its tables' and its register log's base-two logarithms of rows and its
    /// rate.
    ///
    /// # Errors
    ///
    /// Refuses what the native verifier refuses of an announcement: a height out of range, or a witness the commitment does not take.
    pub fn new(program: &'p Program, taus: PerTable<usize>, log_cycles: usize, rate: Rate) -> Result<Self, CpuError> {
        let layout = Layout::announced(&program.view(), taus, log_cycles)?;
        Ok(Self {
            program,
            taus,
            log_cycles,
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

    /// The register log's base-two logarithm of rows.
    pub const fn log_cycles(&self) -> usize {
        self.log_cycles
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

        let (clock, cycles) = r.scope("announcement", |r| self.read_announcement(r));
        let output = output.map(|o| r.b.k_to_e1(o));
        let claims = infallible(self.layout.verify_core(&mut r, clock, &cycles, &output, self.rate));
        CoreRows {
            claims,
            state: t.commitment(b),
        }
    }

    /// The announced sizes: every height and the rate the shape's, the final clock a live clock at slot zero, the
    /// cycles a count the register log holds.
    ///
    /// Returns the clock, which closes the run's last state on the bus, and the cycles' bits, lowest first, one past the
    /// log's.
    fn read_announcement(&self, r: &mut Rows<'_, '_>) -> (Ew, Vec<Ew>) {
        for size in Announcement::sizes(&self.taus, self.log_cycles, self.rate) {
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

        // The cycles: no bit above the log's height, and a full log no other bit.
        let cycles = infallible(r.next_scalar());
        let [word, high, top] = r.b.e_to_k(cycles);
        r.b.eq_k_const(high, 0);
        r.b.eq_k_const(top, 0);
        let bits = r.b.split(word);
        for &bit in &bits[self.log_cycles + 1..] {
            r.b.eq_k_const(bit, 0);
        }
        let full = r.b.k_to_e1(bits[self.log_cycles]);
        let bits: Vec<Ew> = (bits[..=self.log_cycles].iter()).map(|&b| r.b.k_to_e1(b)).collect();
        for &bit in &bits[..self.log_cycles] {
            let both = r.mul(full, bit);
            let zero = r.zero();
            r.b.eq_e(both, zero);
        }
        (clock, bits)
    }
}
