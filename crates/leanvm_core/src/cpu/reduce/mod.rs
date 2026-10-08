//! The verifier's core from the commitment to the end of the proof, written once over the verifier's arithmetic.

use super::batch::{FormPowers, VerifierBatch};
use super::deferred::{Claim, DeferredClaims, ProgramPoint};
use super::error::CpuError;
use super::layout::{Framework, Layout, Schema};
use crate::class_flock::FlockId;
use crate::constraints::Claims;
use crate::leaf::PublicColumns;
use crate::pcs::{Commitment, Rate, StackClaim};
use crate::tables::{ClassTable, N_TABLES};
use crate::{constraints, leaf};
use fiat_shamir::arith::Verifier;
use flock::reduction;
use pcs::verifier::OpeningVerifier;

/// What the bus and the table sumcheck leave to the rest of the verifier.
pub(crate) struct TableReduction<E> {
    /// The opening's point claims: the bus's framework claims, each table's columns, then the exit's.
    pub(crate) slots: Vec<StackClaim<E>>,
    /// Each producer's multiplicity bits at its point, which the opening ring-switches.
    pub(crate) producers: Vec<Claims<E>>,
    /// Each table's claims in the table sumcheck, whose register numbers' bits the opening ring-switches.
    pub(crate) tables: Vec<Claims<E>>,
    /// The claim on the program's bytecode table and RAM image.
    pub(crate) program: Claim<ProgramPoint<E>, E>,
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
    /// The verifier's core past the announcement, for a run that ends on the given clock and returns the given output.
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
        clock: V::E,
        output: &[V::E; 4],
        rate: Rate,
    ) -> Result<DeferredClaims<V::E>, CpuError> {
        let commitment = Commitment::read(v, self.shape, rate)?;
        let reduced = v.scope("bus and tables", |v| self.reduce_tables(v, clock, output))?;

        // Flock's reductions, batched over every class circuit then every clock circuit, each leaving its matrices' form to its circuit.
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
            let rings = self.rings(slices, &reduced.producers, &reduced.tables, zero);
            commitment.verify(v, &reduced.slots, &rings)
        })
        .map_err(CpuError::Open)?;
        v.finish()?;
        Ok(DeferredClaims {
            program: reduced.program,
            circuits,
        })
    }

    /// Verify the bus and the table sumcheck of a run that ends on the given clock and returns the given output.
    ///
    /// The layout's own final clock is zero: a leaf is affine in each coordinate, so the clock's share joins the pull side's total here.
    ///
    /// A table with a class circuit puts linear forms on the bus, so its columns' values at the bus's point settle its share.
    ///
    /// The table sumcheck then proves what the other tables and the producers owe.
    ///
    /// # Errors
    ///
    /// Returns the bus's or the table sumcheck's refusal.
    pub(crate) fn reduce_tables<V: Verifier + PublicColumns>(
        &self,
        v: &mut V,
        clock: V::E,
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
        let per_tick = v.mul(
            bus.selectors[1][Framework::State as usize],
            bus.weights[Framework::FINAL_CLOCK],
        );
        bus.totals[1] = v.mul_add(per_tick, clock, bus.totals[1]);

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
        let program = Claim::from_table_sumcheck(v, &bus, &table_sumcheck, powers);
        let claims = TableClaims::new(settled, table_sumcheck.claims);
        let slots = self.opening_claims(v, bus.claims, &claims.columns, output);
        Ok(TableReduction {
            slots,
            producers: claims.producers,
            tables: claims.summed,
            program,
        })
    }
}
