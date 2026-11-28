//! The public structure of a run, which the verifier rebuilds from the program and the announced sizes: the stack's
//! placements over the verifier's column numbering ([`verifier::layout::stack_blocks`]) and the pointer width, and the
//! prover's witness (`build`).

use super::*;
use crate::link::pointer::Chunks;
use crate::tables::{FillCtx, KeccakOp};
use crate::witness::{Placement, StackShape};
use primitives::field::F64;
use verifier::layout::{
    GLOBAL_COLUMN_BASES, KECCAK_OUT, MEMORY_0, MEMORY_1, OP_KECCAK, SizeSource, TABLE_WIDTHS, spare_local,
};

/// The Keccak reduction's committed states `q_keccak`, `2^(SLOT_LOG + τ)` words for `2^τ` steps: the one copy of the
/// `KECCAK` input lanes, whose columns are virtual ([`keccak_value`]).
pub use verifier::layout::QKECCAK;

/// Every column, the shared ones then each table's, at [`GLOBAL_COLUMN_BASES`].
pub const N_COLUMNS: usize = GLOBAL_COLUMN_BASES[tables::N_TABLES - 1] + TABLE_WIDTHS[tables::N_TABLES - 1];

/// A KECCAK column that `q_keccak` carries. Both kinds are virtual, with no placement of their own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeccakLane {
    /// A column whose words are `q_keccak`'s slot `s`, so a claim on it is a claim on that slot: an input lane
    /// (slot = lane), or one of the columns riding the spare slots ([`verifier::layout::qkeccak_slot`]).
    Slot(usize),
    /// Output lane `l`, whose claim is the Keccak reduction's claim on the permutation's output.
    Output(usize),
}

/// What `q_keccak` holds for the global column `col`, if it holds anything: a value lane of the KECCAK table, or one of
/// its columns riding a spare slot.
pub fn keccak_value(col: usize) -> Option<KeccakLane> {
    if let Some(slot) = verifier::layout::qkeccak_slot(col) {
        return Some(KeccakLane::Slot(slot));
    }
    let lane = col.checked_sub(GLOBAL_COLUMN_BASES[OP_KECCAK] + KECCAK_OUT)?;
    (lane < primitives::hash::STATE_LANES).then_some(KeccakLane::Output(lane))
}
// `q_keccak`'s slots as the verifier counts them: the committed states', then a spare one per riding column.
const _: () = {
    use verifier::layout::{QKECCAK_SLOTS, QKECCAK_SPARE};
    assert!(crate::keccak::SLOTS == QKECCAK_SLOTS && 1 << crate::keccak::SLOT_LOG == QKECCAK_SLOTS + QKECCAK_SPARE);
};

/// The public proof structure: everything the verifier reconstructs from the program and the announced sizes.
pub struct Layout {
    /// Per global column, where the stack holds it; [`Placement::VIRTUAL`] for a column `q_keccak` carries or nothing
    /// commits ([`keccak_value`]).
    pub placements: Vec<Placement>,
    pub shape: StackShape,
    pub taus: [usize; tables::N_TABLES],
    /// Rows per table the program executed, at most `2^taus[t]`: the rest are padding rows (§sec:e2e-pad).
    pub rows: [usize; tables::N_TABLES],
    /// The bits of every Hotwire pointer ([`crate::link`]).
    pub pointer_width: usize,
}

impl Layout {
    /// Words of the committed columns, before the stack's pad.
    pub(crate) fn committed_size(&self) -> usize {
        (self.placements.iter())
            .filter(|p| !p.is_virtual())
            .map(|p| 1usize << p.n_vars)
            .sum()
    }

    /// Where the stack holds the `2^n_vars` rows of the global column `col`: its own placement, or its slot's rows of
    /// `q_keccak` for a column riding there.
    pub fn rows_of(&self, col: usize, n_vars: usize) -> Placement {
        match keccak_value(col) {
            Some(KeccakLane::Slot(slot)) => self.placements[QKECCAK].rows(slot << n_vars, n_vars),
            _ => self.placements[col],
        }
    }
}

/// The public [`Layout`] of a run of a `2^log_bytecode`-instruction program with `2^log_mem` cells of memory and `rows`
/// rows in each table.
pub fn layout_of(log_bytecode: usize, log_mem: usize, rows: [usize; tables::N_TABLES]) -> Layout {
    let taus = table_logs(rows);
    let mut kappas = vec![None; N_COLUMNS];
    for block in verifier::layout::stack_blocks() {
        let source = match block.source {
            SizeSource::Memory => log_mem,
            SizeSource::Table(t) => taus[t],
        };
        kappas[block.column] = Some(source + block.adj);
    }
    let (placements, shape) = crate::witness::placements_of(&kappas);
    Layout {
        placements,
        shape,
        taus,
        rows,
        pointer_width: verifier::pointer_width(log_mem, log_bytecode, rows.iter().sum::<usize>() as u64),
    }
}

/// Every table's log height (`verifier::layout::table_log_heights`).
pub(crate) fn table_logs(rows: [usize; tables::N_TABLES]) -> [usize; tables::N_TABLES] {
    let taus: [usize; tables::N_TABLES] = verifier::layout::table_log_heights(&rows.map(|r| r as u64))
        .try_into()
        .expect("a height per table");
    debug_assert_eq!(
        taus[OP_KECCAK],
        crate::keccak::n_steps_log(rows[OP_KECCAK]),
        "the KECCAK table is the Keccak reduction's batch"
    );
    taus
}

/// The prover's witness: the stack `q`, which holds every committed column at its placement, and the public
/// [`Layout`].
pub(crate) struct Witness {
    pub(crate) q: Vec<F64>,
    /// The KECCAK output lanes' values as `(global column, values)`. The link reads them, but nothing commits them.
    pub(crate) virt: Vec<(usize, Vec<F64>)>,
    pub(crate) layout: Layout,
    /// What the Keccak reduction needs beside `q`, which holds the states it rebuilds its witness from.
    pub(crate) keccak_reduction: crate::keccak::Reduction,
    /// Columns a test changes, written back to the stack at [`Witness::write_edits`].
    #[cfg(test)]
    edits: Vec<(usize, Vec<F64>)>,
}

impl Witness {
    /// One view per column, in global column order: its rows in the stack, its slot of `q_keccak` for a column riding
    /// there, the private buffer for an output lane.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let tau = self.layout.taus[OP_KECCAK];
        let mut cols: Vec<&[F64]> = (self.layout.placements.iter().enumerate())
            .map(|(i, p)| match keccak_value(i) {
                Some(KeccakLane::Slot(_)) => self.layout.rows_of(i, tau).view(&self.q),
                _ if p.is_virtual() => &[],
                _ => p.view(&self.q),
            })
            .collect();
        for (i, buf) in &self.virt {
            cols[*i] = buf;
        }
        cols
    }

    /// A committed column's rows, to change: the change reaches the stack at [`Witness::write_edits`].
    #[cfg(test)]
    pub(crate) fn column_mut(&mut self, i: usize) -> &mut [F64] {
        if !self.edits.iter().any(|(c, _)| *c == i) {
            let rows = self.columns()[i].to_vec();
            self.edits.push((i, rows));
        }
        let (_, rows) = self.edits.iter_mut().find(|(c, _)| *c == i).expect("just added");
        rows
    }

    /// Write every column changed through [`Witness::column_mut`] back to the stack.
    #[cfg(test)]
    pub(crate) fn write_edits(&mut self) {
        for (i, rows) in std::mem::take(&mut self.edits) {
            let p = self.layout.rows_of(i, rows.len().ilog2() as usize);
            self.q[p.offset..][..rows.len()].copy_from_slice(&rows);
        }
    }
}

/// The witness of a run: every committed column written in its place in the stack, at the heights the layout fixes,
/// the `KECCAK` columns riding `q_keccak`'s spare slots in theirs, then `q_keccak`'s committed states.
pub(crate) fn build(program: &Program, exec: &Execution, layout: Layout) -> Witness {
    let tr = &exec.trace;
    let steps = 1 << layout.taus[OP_KECCAK];
    // Every word no column covers stays zero.
    let mut q = parallel::filled(layout.shape.committed_len(), F64::ZERO);
    // The output lanes are committed nowhere, but the link reads them.
    let mut virt: Vec<(usize, Vec<F64>)> = (0..N_COLUMNS)
        .filter(|&i| matches!(keccak_value(i), Some(KeccakLane::Output(_))))
        .map(|i| (i, vec![F64::ZERO; steps]))
        .collect();
    let mut columns = crate::witness::split_stack(&mut q, &layout.placements);
    for (i, buf) in virt.iter_mut() {
        columns[*i] = buf;
    }
    // `q_keccak`'s slots, `steps` words each: the committed states', then one per KECCAK column riding a spare slot,
    // which its fill writes there.
    let (states, spare) = std::mem::take(&mut columns[QKECCAK]).split_at_mut(crate::keccak::SLOTS * steps);
    for (k, slot) in spare.chunks_mut(steps).enumerate() {
        columns[GLOBAL_COLUMN_BASES[OP_KECCAK] + spare_local(k)] = slot;
    }

    // `g^i` for every pc, frame, cell and offset the run used.
    let gpow = primitives::field::g_powers(exec.mem_used.max(program.prog.len()));
    let chunks = Chunks::new(layout.pointer_width);
    crate::stage!("Fill columns", || {
        for (t, table) in tables::tables().into_iter().enumerate() {
            let (base, width) = (GLOBAL_COLUMN_BASES[t], table.n_committed_columns());
            let height = 1 << layout.taus[t];
            let ctx = FillCtx::new(tr, &exec.mem, &gpow, &program.prog, &chunks, height, table.padding());
            table.fill(&ctx, &mut columns[base..base + width]);
        }
        // The memory image, a word's two `K` lanes.
        const _: () = assert!(MEMORY_0 + 1 == MEMORY_1);
        tables::write_rows(&mut columns[MEMORY_0..=MEMORY_1], exec.mem.len(), |i| {
            exec.mem.word(i).to_limbs().map(F64)
        });
    });

    // The committed states of every executed `KECCAK`'s input, row `j` step `j`.
    let keccak_reduction = crate::stage!("Build q_keccak", || {
        let inputs = parallel::map_collect(tr.keccak.len(), |j| {
            let r = &tr.keccak[j];
            let k = KeccakOp::of(&program.prog[r.pc as usize]);
            crate::keccak::state_of_cells(k.in_odd, |c| exec.mem.word(k.cell(r.fp, c) as usize))
        });
        crate::keccak::place(&inputs, states)
    });
    drop(columns);
    Witness {
        q,
        virt,
        layout,
        keccak_reduction,
        #[cfg(test)]
        edits: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::fixture::{assemble, gw, looping_program, set, w};
    use crate::tables::Read;
    use primitives::field::F128;
    use primitives::test_rng::Rng;

    const PI: [F128; 2] = [F128::new(7, 0), F128::new(11, 0)];

    /// Straight-line: `KECCAK`s in both layouts, writing all, one and two output cells; `DEREF` in its three modes; an
    /// untaken `JUMP` and a taken one to the next instruction; a 128-bit `MUL` and `XOR`.
    fn straight_program() -> Program {
        let (a, b) = (
            F128::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
            F128::new(5, 0x0bad_f00d),
        );
        let keccak = |m: [u32; 4], tail, b8, cap, out, in_odd, out_odd, out_cells| Op::Keccak {
            m,
            tail,
            b8,
            cap,
            out,
            in_odd,
            out_odd,
            out_cells,
        };
        let mut prog = vec![set(2, a), set(3, b)];
        prog.extend((4..9).map(|c| set(c, F128::new(c.into(), 0x77))));
        prog.extend((9..13).map(|c| set(c, F128::ZERO)));
        prog.extend([
            keccak([2, 3, 2, 3], 4, 8, 9, 16, false, true, OutCells::All),
            keccak([16, 17, 18, 19], 20, 24, 25, 32, true, false, OutCells::All),
            keccak([3, 2, 33, 2], 4, 8, 9, 60, false, false, OutCells::Two),
            set(46, gw(48)),
            set(47, w(5)),
        ]);
        prog.extend(
            [DerefMode::Pc, DerefMode::Fp, DerefMode::Cell]
                .into_iter()
                .zip([2, 3, 1])
                .map(|(mode, o2)| Op::Deref {
                    o1: 46,
                    o2,
                    o3: 47,
                    mode,
                }),
        );
        prog.extend([
            set(52, F128::ZERO),
            set(53, gw(5)),
            Op::Jump { oc: 52, od: 53, of: 53 },
            set(54, F128::ONE),
            set(55, gw(25)),
        ]);
        prog.push(Op::Jump { oc: 54, od: 55, of: 54 });
        assert_eq!(prog.len(), 25);
        prog.extend([Op::Mul { a: 2, b: 3, c: 57 }, Op::Xor { a: 2, b: 3, c: 58 }]);
        prog.resize(31, Op::Xor { a: 2, b: 3, c: 58 });
        prog.push(Op::Xor { a: 0, b: 0, c: 0 });
        assemble(prog, 64)
    }

    fn witness(program: &Program) -> (Execution, Witness) {
        let exec = execute(program, &[], PI).unwrap();
        assert!(exec.unconstrained_reads.is_empty());
        let layout = layout_of(
            crate::log2_strict_usize(program.prog.len()),
            crate::log2_strict_usize(exec.mem.len()),
            exec.rows(),
        );
        let witness = build(program, &exec, layout);
        (exec, witness)
    }

    /// Every executed row is what its links say, read through its pointers: its cycle pointer names its cycle, and
    /// the states chain from `(1, 1)` to the final state; its bytecode pointer names its `pc` and an instruction of
    /// its opcode whose operands its forms hold; every access's pointer, shifted, names the cell of its address,
    /// which holds its word; `JUMP`'s identities vanish. Every padding row is the table's padding row.
    fn check_rows(program: &Program, exec: &Execution, w: &Witness) {
        let layout = &w.layout;
        let chunks = Chunks::new(layout.pointer_width);
        let columns = w.columns();
        let (stacked, n_bc) = (program.stacked_bytecode(), program.prog.len());
        let slot = |s: usize, i: usize| w_of(stacked[s * n_bc + i]);
        let mut states: Vec<Option<[F128; 4]>> = vec![None; exec.cycles];
        let coefs = Rng::new(3).ext_vec(4);
        for (t, table) in tables::tables().into_iter().enumerate() {
            let links = table.links();
            let (base, width) = (GLOBAL_COLUMN_BASES[t], table.n_committed_columns());
            let padding = table.padding();
            for u in 0..1 << layout.taus[t] {
                let row: Vec<F64> = (0..width).map(|c| columns[base + c][u]).collect();
                if u >= layout.rows[t] {
                    assert_eq!(row, padding, "table {t} row {u} is padding");
                    continue;
                }
                let e: Vec<F128> = row.iter().map(|&v| F128::from(v)).collect();
                let index = |c: usize| chunks.decode(row[c].0).expect("a one-hot word");
                let state = &links.state;
                let next = state.next.each_ref().map(|f| f.evaluate(&e));
                let cycle = index(state.cycle);
                assert!(states[cycle].is_none(), "cycle {cycle} twice");
                states[cycle] = Some([e[state.pc], e[state.fp], next[0], next[1]]);

                let bc = &links.bytecode;
                let i = index(bc.pointer);
                assert_eq!(e[bc.pc], gw(i));
                assert_eq!(slot(3, i), gw(bc.opcode), "the opcode slot");
                for (slots, form) in &bc.operands {
                    assert_eq!(slots.iter().map(|&s| slot(s, i)).sum::<F128>(), form.evaluate(&e));
                }

                for access in &links.memory {
                    if access.gate.is_some_and(|g| row[g] == F64::ZERO) {
                        continue;
                    }
                    let cell = chunks
                        .shifted(index(access.pointer), access.shift)
                        .expect("inside the window");
                    let mut address = access.address.evaluate(&e);
                    if let Some((s, k)) = access.frame {
                        address += gw(k as usize) * e[state.fp] * slot(s, i);
                    }
                    assert_eq!(address, gw(cell), "table {t} row {u}");
                    let reads = access.reads.iter().map(|read| match *read {
                        Read::Word { pointer, ref scale } => scale.evaluate(&e) * exec.mem.word(index(pointer)),
                        Read::Slot { slot: s, scale } => scale * slot(s, i),
                        Read::Frame { slot: s, scale } => scale * e[state.fp] * slot(s, i),
                        Read::Pc { slot: s, scale } => scale * e[state.pc] * slot(s, i),
                    });
                    let word = access.value.evaluate(&e) + reads.sum::<F128>();
                    assert_eq!(word, exec.mem.word(cell), "table {t} row {u} cell {cell}");
                }
                let identities = table.constraint(&coefs[..table.n_constraints()]);
                assert_eq!(identities.evaluate(&e), F128::ZERO);
            }
        }
        let states: Vec<[F128; 4]> = states.into_iter().map(|s| s.expect("every cycle has a row")).collect();
        assert_eq!(states[0][..2], [F128::ONE, F128::ONE]);
        for pair in states.windows(2) {
            assert_eq!(
                pair[0][2..],
                pair[1][..2],
                "a row's successor is the next cycle's state"
            );
        }
        assert_eq!(
            states[exec.cycles - 1][2..],
            [gw(n_bc - 1), F128::ONE],
            "the final state"
        );
    }

    fn w_of(word: u64) -> F128 {
        F128::new(word, 0)
    }

    /// [`check_rows`] on both fixtures; and every column's view is the stack where its placement (or its slot's rows of
    /// `q_keccak`, [`Layout::rows_of`]) says.
    #[test]
    fn witness_rows_follow_the_links() {
        for program in [looping_program(12), straight_program()] {
            let (exec, w) = witness(&program);
            assert!(
                exec.rows().iter().all(|&n| n > 0),
                "a row in every table: {:?}",
                exec.rows()
            );
            check_rows(&program, &exec, &w);
            let layout = &w.layout;
            for (c, column) in w.columns().into_iter().enumerate() {
                let placement = match keccak_value(c) {
                    Some(KeccakLane::Output(_)) => continue,
                    Some(KeccakLane::Slot(_)) => layout.rows_of(c, column.len().ilog2() as usize),
                    None => layout.placements[c],
                };
                assert_eq!(column, &w.q[placement.offset..][..1 << placement.n_vars], "column {c}");
            }
        }
    }

    /// `q_keccak` holds the committed states of every step's input and nothing past the spare slots' columns.
    #[test]
    fn qkeccak_holds_the_committed_states() {
        let program = straight_program();
        let (exec, w) = witness(&program);
        let steps = 1 << w.layout.taus[OP_KECCAK];
        let inputs: Vec<_> = (exec.trace.keccak.iter())
            .map(|r| {
                let k = KeccakOp::of(&program.prog[r.pc as usize]);
                crate::keccak::state_of_cells(k.in_odd, |c| exec.mem.word(k.cell(r.fp, c) as usize))
            })
            .collect();
        let mut states = vec![F64::ZERO; crate::keccak::SLOTS * steps];
        crate::keccak::place(&inputs, &mut states);
        let q_keccak = w.layout.placements[QKECCAK].view(&w.q);
        assert_eq!(q_keccak.len(), steps << crate::keccak::SLOT_LOG);
        assert_eq!(q_keccak[..states.len()], states);
    }

    /// The placements are the verifier's (`verifier::layout::build_layout`) over a sweep of sizes, a column `q_keccak`
    /// carries at its slot's rows and an output lane at none, and so is the stack's size.
    #[test]
    fn placements_match_the_verifier() {
        let mut rng = Rng::new(0x5eed);
        for case in 0..300 {
            let log_bc = case % 7;
            let program = assemble(vec![Op::Xor { a: 0, b: 0, c: 0 }; 1 << log_bc], 4);
            let log_mem = 1 + (rng.next_u64() % 24) as usize;
            let rows: [usize; tables::N_TABLES] = std::array::from_fn(|_| {
                let log = rng.next_u64() % 21;
                (rng.next_u64() % (1 << log)) as usize + (rng.next_u64() % 2) as usize
            });
            let ours = layout_of(log_bc, log_mem, rows);
            let rows_u64: Vec<u64> = rows.iter().map(|&n| n as u64).collect();
            let theirs = verifier::layout::build_layout(program.bytecode(), log_mem as u64, &rows_u64).unwrap();
            assert_eq!(ours.shape.mu, theirs.stack_log, "case {case}");
            assert_eq!(ours.taus.to_vec(), theirs.table_log_heights);
            assert_eq!(theirs.placements.len(), N_COLUMNS);
            for (c, their) in theirs.placements.iter().enumerate() {
                let mine = match keccak_value(c) {
                    Some(KeccakLane::Output(_)) => None,
                    Some(KeccakLane::Slot(_)) => Some(ours.rows_of(c, ours.taus[OP_KECCAK])),
                    None => Some(ours.placements[c]),
                };
                let their = their.map(|p| Placement {
                    n_vars: p.variables,
                    offset: p.index as usize,
                });
                assert_eq!(mine, their, "case {case} column {c}");
            }
        }
    }
}
