//! The verifier's core from the commitment to the end of the proof, written once over the verifier's arithmetic.

use super::batch::{FormPowers, VerifierBatch};
use super::deferred::{Claim, DeferredClaims, ProgramPoint};
use super::error::CpuError;
use super::layout::{Framework, Layout, Log, Schema};
use crate::class_flock::FlockId;
use crate::constraints::Claims;
use crate::leaf::PublicColumns;
use crate::memory::{self, LinkShare, LogOpening, Statement};
use crate::pcs::{Commitment, Rate, StackClaim};
use crate::rv::Syscall;
use crate::tables::{ClassTable, N_TABLES};
use crate::{constraints, leaf};
use fiat_shamir::arith::{Arith, Verifier};
use flock::reduction;
use pcs::verifier::OpeningVerifier;
use primitives::field::{F64, F192, G};

/// What the bus, the table sumcheck and the memory logs leave to the rest of the verifier.
pub(crate) struct TableReduction<E> {
    /// The opening's point claims: the bus's framework claims, each table's columns, then the logs'.
    pub(crate) slots: Vec<StackClaim<E>>,
    /// What each memory log leaves the opening.
    pub(crate) logs: Vec<LogOpening<E>>,
    /// Each producer's multiplicity bits at its point, which the opening ring-switches.
    pub(crate) producers: Vec<Claims<E>>,
    /// Each table's claims in the table sumcheck, whose register numbers' bits the opening ring-switches.
    pub(crate) tables: Vec<Claims<E>>,
    /// The claim on the program's bytecode table and RAM image.
    pub(crate) program: Claim<ProgramPoint<E>, E>,
}

/// `g^n` for the count `n` given by its bits: `prod_b (1 + n_b (g^(2^b) + 1))`.
fn generator_power<A: Arith>(a: &mut A, bits: &[A::E]) -> A::E {
    let mut power = G;
    bits.iter().fold(a.one(), |acc, &bit| {
        let step = a.mul_const(bit, F192::from(power + F64::ONE));
        let one = a.one();
        let factor = a.add(step, one);
        power = power * power;
        a.mul(acc, factor)
    })
}

/// The claims the tables' columns are left with, prover and verifiers alike.
pub(crate) struct TableClaims<E> {
    /// Each table's column claims: a settled table's at the bus point, another's at the table sumcheck's.
    pub(crate) columns: Vec<Claims<E>>,
    /// Each table's claims in the table sumcheck: a settled table's on its register numbers alone.
    pub(crate) summed: Vec<Claims<E>>,
    /// Each producer's claims in the table sumcheck.
    pub(crate) producers: Vec<Claims<E>>,
}

impl<E: Clone> TableClaims<E> {
    /// Split the table sumcheck's claims, the settled tables' at the bus point leading the column claims.
    pub(crate) fn new(settled: Vec<Claims<E>>, mut summed: Vec<Claims<E>>) -> Self {
        let producers = summed.split_off(N_TABLES);
        let mut columns = settled;
        columns.extend_from_slice(&summed[columns.len()..]);
        Self {
            columns,
            summed,
            producers,
        }
    }
}

impl Layout {
    /// The verifier's core past the announcement, for a run of these logs' live rows, by their bits, returning `output`.
    ///
    /// It reads the commitment, verifies the bus and the tables, the flock reductions and the opening, then checks nothing is left to read.
    /// It returns the claims the proof leaves on the program's polynomials and on each circuit's matrices.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    pub(crate) fn verify_core<V: OpeningVerifier + PublicColumns>(
        &self,
        v: &mut V,
        live: [&[V::E]; 2],
        output: &[V::E; 4],
        rate: Rate,
    ) -> Result<DeferredClaims<V::E>, CpuError> {
        let commitment = Commitment::read(v, self.shape, rate)?;
        let reduced = v.scope("bus and tables", |v| self.reduce_tables(v, live, output))?;

        // Flock's reductions, batched over every table's circuit, each leaving its matrices' form to its circuit.
        let batches = FlockId::batches(&self.taus);
        let replays = v
            .scope("flock", |v| reduction::verify(&batches, v))
            .map_err(CpuError::Reductions)?;
        let (slices, circuits): (Vec<_>, Vec<_>) = (replays.into_iter())
            .map(|replay| (replay.claim, replay.matrices.into()))
            .unzip();

        // The one opening, its ring-switched regions each packed witness, each producer's multiplicity column and each table's register numbers.
        v.scope("opening", |v| {
            let zero = v.zero();
            let rings = self.rings(slices, &reduced.producers, &reduced.tables, &reduced.logs, zero);
            commitment.verify(v, &reduced.slots, &rings)
        })
        .map_err(CpuError::Open)?;
        v.finish()?;
        Ok(DeferredClaims {
            program: reduced.program,
            circuits,
        })
    }

    /// Verify the bus, the table sumcheck and the memory logs of a run of these logs' live rows returning `output`.
    ///
    /// The layout's final state has zero positions: a leaf is affine in each coordinate, so the announced positions'
    /// share joins the pull side's total here.
    ///
    /// A table with a class circuit puts linear forms on the bus, so its columns' values at the bus's point settle its share.
    ///
    /// The table sumcheck then proves what the other tables and the producers owe, and each log's argument its block.
    ///
    /// # Errors
    ///
    /// Returns the bus's, the table sumcheck's or a log's refusal.
    pub(crate) fn reduce_tables<V: Verifier + PublicColumns>(
        &self,
        v: &mut V,
        live: [&[V::E]; 2],
        output: &[V::E; 4],
    ) -> Result<TableReduction<V::E>, CpuError> {
        let mut bus = leaf::verify_balance(
            v,
            &self.push,
            &self.pull,
            &self.producers,
            self.grinding,
            Schema::get().spans.as_slice(),
        )
        .map_err(CpuError::Bus)?;
        let end = bus.selectors[1][Framework::State as usize];
        for (slot, bits) in Framework::FINAL_POSITIONS.into_iter().zip(live) {
            let position = generator_power(v, bits);
            let weight = v.mul(end, bus.weights[slot]);
            bus.totals[1] = v.mul_add(weight, position, bus.totals[1]);
        }

        // Each settled table's columns at the bus point `zeta[..tau]`, which the opening checks, short of its register
        // numbers, which the batch folds.
        //
        // Its forms there, its register numbers taken as zero, are its share of each side short of their part, which
        // leaves the rest owed: in characteristic two, the sum.
        let mut settled = Vec::with_capacity(N_TABLES);
        for (t, table) in ClassTable::all().iter() {
            if !table.settled_at_bus() {
                continue;
            }
            let (registers, n) = (table.summed_columns(), table.n_committed_columns());
            let mut sent = v.next_scalars(n - registers.len())?.into_iter();
            let zero = v.zero();
            let evals: Vec<V::E> = (0..n)
                .map(|c| {
                    if registers.contains(&c) {
                        zero
                    } else {
                        sent.next().expect("a sent value per column")
                    }
                })
                .collect();
            for (total, forms) in bus.totals.iter_mut().zip(&bus.forms) {
                let share = forms[t.index()].at(v, &evals);
                *total = v.add(*total, share);
            }
            settled.push(Claims {
                chi: bus.point[..self.taus[t]].to_vec(),
                evals,
                slices: Vec::new(),
            });
        }

        // The tie between the batch and the bus, and why the batch's target is never sent.
        //
        // Each side's leaf claim, less its framework blocks, is the tables' and producers' share `R_s`.
        //
        // The verifier just derived those, and the batch must sum to `sum_s xi^s * R_s`.
        //
        // The challenge `xi` comes after the `R_s` are fixed, so hitting that one number forces each side's share.
        //
        // RAM's image is left out of it, and the program claim makes up for it.
        let xi = v.sample();
        let powers = FormPowers::new(v, xi);
        let target = powers.combine(v, bus.totals);
        let batch = VerifierBatch::new(v, self, &bus, powers);
        let table_sumcheck = constraints::verify(v, batch.airs(), &bus.point, target).map_err(CpuError::Constraint)?;
        drop(batch);

        // Each memory log's argument, from its share of the bus.
        let syscall = v.constant(F192::from(F64(Syscall::Exit.number())));
        let outputs = [&[syscall][..], output].concat();
        let mut logs = Vec::with_capacity(Log::ALL.len());
        for ((log, shape), share) in Log::ALL.into_iter().zip(&self.logs).zip(&bus.logs) {
            let share = LinkShare {
                point: share.point.clone(),
                value: share.value,
                weights: bus.weights.clone(),
                beta: bus.beta,
            };
            let statement = Statement {
                live: live[log as usize],
                outputs: if log == Log::Registers { &outputs } else { &[] },
            };
            let opening = v
                .scope("memory", |v| memory::verify(v, shape, statement, &share))
                .map_err(|error| CpuError::Memory { log, error })?;
            logs.push(opening);
        }

        // The program claim: the bytecode producer's, and RAM's image at a fresh weight.
        let lw_img = v.sample();
        let image = logs
            .iter()
            .find_map(|o| o.image.as_ref())
            .expect("the memory log claims RAM's image");
        let program = Claim::from_table_sumcheck(v, &bus, &table_sumcheck, powers, image, lw_img);
        let claims = TableClaims::new(settled, table_sumcheck.claims);
        let slots = self.opening_claims(bus.claims, &claims.columns, &logs);
        Ok(TableReduction {
            slots,
            logs,
            producers: claims.producers,
            tables: claims.summed,
            program,
        })
    }
}
