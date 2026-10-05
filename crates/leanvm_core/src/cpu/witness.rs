//! The prover's witness: the stacked multilinear holding every committed column, built once from a run.

use super::MAX_LOG_ROWS;
use super::execute::Execution;
use super::layout::{Layout, Lookup, Schema, Shared, q_column};
use super::program::Program;
use crate::class_flock::Prepared;
use crate::tables::{ClassSpec, ClassTable, FillContext};
use crate::{class_flock, tables};
use primitives::field::F64;

/// The prover's witness: the stack `q` with every committed column at its placed offset, and the public layout.
pub(crate) struct Witness {
    /// The stacked multilinear the commitment takes.
    pub(crate) q: Vec<F64>,
    /// The ports' values, by global column index.
    ///
    /// They carry data for the bus but are not committed, so they are not in the stack.
    pub(crate) virt: Vec<(usize, Vec<F64>)>,
    /// The public structure the witness fills.
    pub(crate) layout: Layout,
    /// The clock the run ended on, which the prover announces.
    pub(crate) ts_final: u64,
    /// Each circuit's flock batch, freed right after its reduction.
    pub(crate) reductions: Vec<Prepared>,
}

impl Witness {
    /// The witness of a finished run.
    ///
    /// # Panics
    ///
    /// Panics if a table's rows are not a power of two at flock's floor: the fill blocks failed to fill it.
    pub(crate) fn build(program: &Program, exec: &Execution) -> Self {
        let (p, trace, schema) = (&program.rv, &exec.trace, Schema::get());

        // Every table's rows are real, filled to a power of two at flock's floor, so its height is its row count.
        let row_counts = trace.row_counts();
        assert!(
            row_counts.iter().all(|&r| r <= 1 << MAX_LOG_ROWS),
            "a table exceeds 2^{MAX_LOG_ROWS} rows"
        );
        let taus: [usize; tables::N_TABLES] = std::array::from_fn(|t| {
            let r = row_counts[t];
            assert!(
                r.is_power_of_two(),
                "a table has {r} rows, not a power of two: the fill blocks did not fill it"
            );
            let tau = crate::log2_strict_usize(r);
            let floor = class_flock::n_blocks_log(ClassSpec::ALL[t], r);
            assert_eq!(
                tau,
                floor,
                "the {} table must be filled to flock's instance floor",
                ClassSpec::ALL[t].name
            );
            tau
        });

        // The public layout comes first: it fixes each column's length, so each is allocated once.
        let layout = Layout::new(p, taus, trace.ts_final);

        // The stack is written exactly once: one window per committed column, each filled in place.
        //
        // SAFETY: each table fills its column windows before they are read.
        // The shared columns are filled below.
        // The pad tail is zeroed.
        let mut q = unsafe { primitives::uninit_vec::<F64>(layout.shape.committed_len()) };

        // A port is not in the stack, so its values get a buffer of their own.
        let mut virt: Vec<(usize, Vec<F64>)> = Vec::new();
        for (t, &(base, width)) in schema.spans.iter().enumerate() {
            for i in (base..base + width).filter(|&i| layout.placements[i].window().is_none()) {
                // SAFETY: each table checks that it writes every circuit port column in full.
                virt.push((i, unsafe { primitives::uninit_vec::<F64>(1 << layout.taus[t]) }));
            }
        }
        let mut windows = crate::witness::split_stack(&mut q, &layout.placements);
        for (i, buf) in virt.iter_mut() {
            windows[*i] = buf;
        }

        crate::stage!("Fill columns", || {
            // Each table fills its own columns from the trace, in its global span.
            for (t, table) in ClassTable::all().iter().enumerate() {
                let (base, n) = schema.spans[t];
                let ctx = FillContext::new(trace, p, 1 << layout.taus[t], n);
                table.fill(ctx, &mut windows[base..base + n]);
            }

            // Every shared column is written: the stack is uninitialized, so one left out would read garbage.
            for c in Shared::ALL {
                if let Some(values) = c.values(trace) {
                    windows[c.col()].copy_from_slice(values);
                }
            }

            // What the run did not leave, the multiplicities, is counted from its rows.
            trace.count_reads(windows[Lookup::Bytecode.multiplicity().col()]);
        });

        // The packed witnesses, one instance per row of their table.
        let reductions = crate::stage!("Build flock witnesses", || {
            (0..class_flock::N_FLOCKS)
                .map(|f| {
                    let rows = &trace.rows[class_flock::flock(f).0];
                    Prepared::build(f, rows, p.entries(), windows[q_column(f)])
                })
                .collect()
        });

        // Release the windows' borrow of the stack and of the port buffers.
        drop(windows);
        Self {
            q,
            virt,
            layout,
            ts_final: trace.ts_final,
            reductions,
        }
    }

    /// One read-only view per column, in global column order.
    ///
    /// A committed column's view is its window in the stack; a port's is its own buffer.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let mut cols: Vec<&[F64]> = self
            .layout
            .placements
            .iter()
            .map(|p| {
                p.window()
                    .map_or(&[][..], |w| &self.q[w.offset..w.offset + (1 << w.n_vars)])
            })
            .collect();
        for (i, buf) in &self.virt {
            cols[*i] = buf;
        }
        cols
    }

    /// The committed data before the stack's zero pad: the real witness size.
    pub(crate) fn committed_size(&self) -> usize {
        crate::witness::committed_len(&self.layout.placements)
    }
}
