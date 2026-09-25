//! Filling every table to a power of two, so that no table has padding rows.
//!
//! A table is proven over a power-of-two number of rows, so a run whose counts are not
//! powers of two has to make up the difference, and it makes it up by executing more
//! instructions. The bytecode carries, per table and per size in [`SIZES`], a *block*:
//! that many dummy instructions of the table's opcode, then a `JUMP` back to the block's
//! own first instruction, in the same frame (`lean_compiler::filler`).
//!
//! So a block is a **cycle**, and no program code jumps into it. That is what makes this
//! work: the state channel's tuples are pushed and pulled around the cycle and cancel
//! among themselves, for any number of traversals, so the fill is a closed loop running
//! beside the program's chain rather than part of it (doc §Filling the tables). The
//! prover picks how many times each block is traversed, and nothing has to be counted,
//! tested, or entered.
//!
//! A traversal of the size-`s` block costs exactly `s + 1` rows: `s` of its own table and
//! one `JUMP`. Nothing else, and nothing on any other table. That is what makes the solve
//! here exact, with no calibrated cost model and no residual to correct, and it is why
//! one interpretation of the program suffices: the interpreter solves once the program
//! has halted, by which point its row counts are final.
//!
//! The sizes are powers of two so any fill is reachable exactly, while the bulk rides the
//! largest block at one `JUMP` per 128 rows. A table already sitting on a power of two is
//! never entered at all.

use crate::tables::N_TABLES;

/// No table asked to grow past its natural power of two.
pub const NO_FLOORS: [usize; N_TABLES] = [0; N_TABLES];

/// The table a committed-size floor grows ([`crate::cpu::Program::min_log_committed`]).
/// `SET` writes one cell from an immediate: no operand reads, no second memory
/// touch, and no precompile behind it, so its rows are the cheapest to prove.
pub const PAD_TABLE: usize = 2;

/// Block sizes, largest first: a fill of `f` rows takes `f / 128` traversals of the
/// largest block and then one per set bit of the remainder.
pub const SIZES: [usize; 8] = [128, 64, 32, 16, 8, 4, 2, 1];

/// Least rows a table can be proven over. Only `BLAKE2s` has one above `1`: flock sizes
/// its argument to at least eight instances, so filling that table below the floor
/// would leave it padded up to it, which is the padding this exists to avoid.
pub const MIN_ROWS: [usize; N_TABLES] = [1, 1, 1, 1, 1, 8];

/// The `JUMP` table's index in [`crate::cpu::Stats::TABLES`]. Every traversal of every
/// block lands its closing jump here, so this table is solved last, absorbing the cost
/// of the whole fill.
pub const JUMP: usize = 4;

/// One block in the bytecode: `size` dummy rows of `table`'s opcode at `pc`, then the
/// jump back to `pc`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub pc: u32,
    pub size: u32,
    pub table: u8,
}

/// A block's frame, as offsets from the frame pointer the interpreter gives it.
///
/// The three the interpreter writes are the closing jump's destination (`g^{pc}` of the
/// block's own first instruction, which is a g-power and so doubles as the jump's nonzero
/// condition), the frame to go there in (this frame), and the pointer the `DEREF` dummy
/// follows. No instruction writes them, which is why a traversal costs its own rows and
/// nothing more.
///
/// The rest is what the dummies use: a cell that is never written, so the `JUMP` table's
/// dummy reads a zero condition and falls through instead of leaving the block; the
/// scratch cell a dummy writes, which doubles as the `BLAKE2s` dummy's chaining value and
/// so spans `SCRATCH..SCRATCH+2`; and the digest, placed clear of it so that a digest
/// never becomes the next traversal's chaining value. `DIGEST+2..DIGEST+6` are the
/// message cells, never written, so every traversal compresses the same input.
pub mod frame {
    /// Where the closing jump goes, and in which frame.
    pub const DEST: u32 = 0;
    pub const NEXT_FP: u32 = 1;
    /// The pointer a `DEREF` dummy follows: `g^0`, memory cell `0`.
    pub const PTR: u32 = 2;
    /// Never written, so it reads as zero.
    pub const ZERO: u32 = 3;
    /// What a dummy writes.
    pub const SCRATCH: u32 = 4;
    /// The `BLAKE2s` dummy's output pair.
    pub const DIGEST: u32 = 6;
    /// Cells a block's frame occupies.
    pub const CELLS: u32 = 12;
}

/// Traversals per block: `plan[t][k]` is how many times the size-`SIZES[k]` block of
/// table `t` is traversed.
pub type Plan = [[usize; SIZES.len()]; N_TABLES];

/// Traversals in total, which is the number of `JUMP` rows the fill costs.
pub fn traversals(plan: &Plan) -> usize {
    plan.iter().flatten().sum()
}

/// Cycles in a plan, one frame each: every block it traverses at all.
pub fn frames(plan: &Plan) -> usize {
    plan.iter().flatten().filter(|&&n| n > 0).count()
}

/// The fill a plan delivers to each table, not counting the closing jumps.
fn delivered(plan: &Plan) -> [usize; N_TABLES] {
    let mut out = [0usize; N_TABLES];
    for (t, row) in plan.iter().enumerate() {
        for (k, &n) in row.iter().enumerate() {
            out[t] += n * SIZES[k];
        }
    }
    out
}

/// Traversals delivering exactly `fill` rows: as many of the largest block as fit, then
/// the binary decomposition of what is left.
fn decompose(fill: usize) -> [usize; SIZES.len()] {
    let mut out = [0usize; SIZES.len()];
    let mut left = fill;
    for (k, &s) in SIZES.iter().enumerate() {
        out[k] = left / s;
        left -= out[k] * s;
    }
    debug_assert_eq!(left, 0, "the sizes end at 1, so nothing can be left over");
    out
}

/// The smallest power of two that is at least `n`, and at least `1`.
fn ceil_pow2(n: usize) -> usize {
    n.max(1).next_power_of_two()
}

/// Traversals whose rows land on `JUMP` itself, delivering exactly `gap` rows. A
/// traversal of the size-`s` block gives that table `s + 1` rows here, its dummies plus
/// its own closing jump, so the sizes to decompose over are `s + 1`, which are not powers
/// of two. `2` and `3` are among them, so every gap but `1` is reachable; a gap of `1`
/// returns `None` and the caller takes a larger target.
fn decompose_jump(gap: usize) -> Option<[usize; SIZES.len()]> {
    if gap == 1 {
        return None;
    }
    let mut out = [0usize; SIZES.len()];
    let mut left = gap;
    for (k, &s) in SIZES.iter().enumerate() {
        // Never leave exactly one row behind, which nothing can deliver.
        while left > s && left - (s + 1) != 1 {
            out[k] += 1;
            left -= s + 1;
        }
    }
    (left == 0).then_some(out)
}

/// A plan taking every table from `base` to an exact power of two, at or above
/// `floors[t]`, or `None` if some table cannot be filled at all.
///
/// Every table but `JUMP` is independent: its fill is the distance to its next power of
/// two, decomposed into traversals. `JUMP` is not, because every traversal of the whole
/// fill lands a row there, its own traversals included. Counting those first makes it a
/// single decomposition rather than a fixpoint.
///
/// A floor above a table's natural target is how a run too small to be provable at the
/// size its consumer needs buys the difference: see [`crate::cpu::Program::min_log_committed`].
pub fn solve(base: [usize; N_TABLES], floors: [usize; N_TABLES]) -> Option<Plan> {
    let mut plan: Plan = [[0; SIZES.len()]; N_TABLES];
    for t in 0..N_TABLES {
        if t != JUMP {
            plan[t] = decompose(ceil_pow2(base[t].max(MIN_ROWS[t]).max(floors[t])) - base[t]);
        }
    }
    // What `JUMP` already owes: its own rows, plus one per traversal so far.
    let owed = base[JUMP] + traversals(&plan);
    let mut target = ceil_pow2(owed.max(MIN_ROWS[JUMP]).max(floors[JUMP]));
    loop {
        if let Some(jump_steps) = decompose_jump(target - owed) {
            plan[JUMP] = jump_steps;
            debug_assert!(is_filled(filled(base, &plan)));
            return Some(plan);
        }
        target = target.checked_mul(2)?;
    }
}

/// The plan filling `base` whose stacked witness, as `committed_log` measures it, is
/// at least `2^min_log`: the natural one if it is, else the one growing [`PAD_TABLE`]
/// the least. The witness never shrinks as a table grows, so the first to reach wins.
pub fn plan(base: [usize; N_TABLES], min_log: usize, committed_log: impl Fn(&Plan) -> usize) -> Plan {
    let mut floors = NO_FLOORS;
    loop {
        let plan = solve(base, floors).unwrap_or_else(|| panic!("no fill plan from {base:?}"));
        if committed_log(&plan) >= min_log {
            return plan;
        }
        floors[PAD_TABLE] = 2 * filled(base, &plan)[PAD_TABLE];
        assert!(
            floors[PAD_TABLE] <= 1 << crate::cpu::MAX_LOG_ROWS,
            "no fill reaches a 2^{min_log} witness"
        );
    }
}

/// The cycles a plan runs, in the order the interpreter should walk them: for each, the
/// block's first pc, its size, and how many times to traverse it. Panics if `blocks` is
/// missing one the plan calls for, which can only mean bytecode the compiler did not emit.
pub fn cycles(blocks: &[Block], plan: &Plan) -> Vec<(u32, u32, usize)> {
    let mut out = Vec::new();
    for (t, row) in plan.iter().enumerate() {
        for (k, &n) in row.iter().enumerate() {
            if n == 0 {
                continue;
            }
            let size = SIZES[k] as u32;
            let block = blocks
                .iter()
                .find(|b| b.table as usize == t && b.size == size)
                .unwrap_or_else(|| panic!("the program has no fill block for table {t}, size {size}"));
            out.push((block.pc, size, n));
        }
    }
    out
}

/// The row counts a plan produces from `base`: its fill, plus one `JUMP` per traversal.
pub fn filled(base: [usize; N_TABLES], plan: &Plan) -> [usize; N_TABLES] {
    let mut out = base;
    for (t, add) in delivered(plan).into_iter().enumerate() {
        out[t] += add;
    }
    out[JUMP] += traversals(plan);
    out
}

/// Every table an exact power of two, at or above its floor: what a run has to look
/// like to be provable at all.
pub fn is_filled(counts: [usize; N_TABLES]) -> bool {
    counts
        .iter()
        .enumerate()
        .all(|(u, &c)| c.is_power_of_two() && c >= MIN_ROWS[u])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Whatever the shape of the run, every table comes out an exact power of two at or
    /// above its floor.
    #[test]
    fn solve_reaches_power_of_two_floors() {
        let cases: [[usize; N_TABLES]; 6] = [
            [0, 0, 0, 0, 0, 0],
            [1, 1, 1, 1, 1, 1],
            // Roughly the XMSS run's mix.
            [125_000, 286_000, 341_000, 508_000, 114_000, 130_000],
            // Tables already exactly on a power of two, the awkward case: the closing
            // jumps of every other table's traversals still have to fit somewhere.
            [1 << 17, 1 << 12, 1000, 1 << 19, 1 << 16, 8],
            [1, 2, 3, 4, 5, 6],
            [0, 0, 0, 0, 1 << 20, 0],
        ];
        for base in cases {
            let plan = solve(base, NO_FLOORS).unwrap_or_else(|| panic!("no plan for {base:?}"));
            let got = filled(base, &plan);
            assert!(is_filled(got), "{base:?} filled to {got:?}");
            for t in 0..N_TABLES {
                assert!(got[t] >= base[t], "rows cannot be removed");
            }
        }
    }

    /// A floor takes a table past its natural power of two, and every other table
    /// still lands on one: what a run too small for its consumer buys with.
    #[test]
    fn floor_grows_target_table() {
        let base = [1_000, 2_000, 3_000, 4_000, 500, 8];
        let mut floors = NO_FLOORS;
        floors[PAD_TABLE] = 1 << 16;
        let plan = solve(base, floors).expect("solvable");
        let got = filled(base, &plan);
        assert!(is_filled(got), "{got:?}");
        assert_eq!(got[PAD_TABLE], 1 << 16);
    }

    /// The bulk of a fill rides the largest block, so the fill stays cheap: one closing
    /// jump per 128 rows, plus at most one traversal per size per table for the
    /// remainders.
    #[test]
    fn fill_uses_bulk_blocks() {
        let base = [125_000, 286_000, 341_000, 508_000, 114_000, 130_000];
        let plan = solve(base, NO_FLOORS).expect("solvable");
        let fill: usize = delivered(&plan).iter().sum();
        assert!(
            traversals(&plan) <= fill / SIZES[0] + SIZES.len() * N_TABLES,
            "{} traversals for {fill} rows",
            traversals(&plan)
        );
    }
}
