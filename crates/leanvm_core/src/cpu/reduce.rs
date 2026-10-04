//! The verifier's core from the bus to the opening's claims, written once over the verifier's arithmetic.

use super::batch::{FormPowers, VerifierBatch};
use super::deferred::{Claim, ProgramPoint};
use super::error::CpuError;
use super::layout::{Framework, Layout, Schema};
use crate::arith::Verifier;
use crate::constraints::{self, Claims};
use crate::{leaf, pcs, tables};

/// What the bus and the table sumcheck leave to the rest of the verifier.
pub(crate) struct TableReduction<E> {
    /// The opening's point claims: the bus's framework claims, each table's columns, then the exit's.
    pub(crate) slots: Vec<pcs::SlotClaim<E>>,
    /// Each producer's multiplicity bits at its point, which the opening ring-switches.
    pub(crate) producers: Vec<Claims<E>>,
    /// The claim on the program's bytecode table and RAM image.
    pub(crate) program: Claim<ProgramPoint<E>, E>,
}

impl Layout {
    /// Verify the bus and the table sumcheck of a run that ends on the given clock and returns the given output.
    ///
    /// The layout's own final clock is zero: a leaf is affine in each coordinate, so the clock's share joins the pull side's total here.
    ///
    /// # Errors
    ///
    /// Returns the bus's or the table sumcheck's refusal.
    pub(crate) fn reduce_tables<V: Verifier>(
        &self,
        v: &mut V,
        clock: V::E,
        output: &[V::E; 4],
    ) -> Result<TableReduction<V::E>, CpuError> {
        let mut bus = leaf::verify_balance(v, &self.push, &self.pull, &self.producers, &Schema::get().spans)
            .map_err(CpuError::Bus)?;
        let [at, again] = Framework::FINAL_CLOCK;
        let weight = v.add(bus.weights[at], bus.weights[again]);
        let per_tick = v.mul(bus.selectors[1][Framework::State as usize], weight);
        bus.totals[1] = v.mul_add(per_tick, clock, bus.totals[1]);

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
        let mut tables = table_sumcheck.claims;
        let producers = tables.split_off(tables::N_TABLES);
        let slots = self.opening_claims(v, bus.claims, &tables, output);
        Ok(TableReduction {
            slots,
            producers,
            program,
        })
    }
}
