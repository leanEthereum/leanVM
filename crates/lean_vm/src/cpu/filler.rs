//! Filling every table to a power of two with padding rows at clock zero.
//!
//! A table is proven over a power-of-two number of rows, so a run whose counts are not
//! powers of two has to make up the difference. The text carries, per table and per
//! size in [`SIZES`], a *block*: that many no-ops of the table's class, then a `JAL`
//! back to the block's own first instruction ([`append_blocks`]).
//!
//! So a block is a **cycle**, and no program code jumps into it. Its rows carry the
//! clock `ts = 0`, which is what makes it balance: `0·g^k = 0`, so the state tuples
//! pushed and pulled around the cycle cancel among themselves for any number of
//! traversals, where a real clock would have moved on. And zero is no power of `g`, so
//! nothing such a row puts on the bus can meet a tuple of the run itself: its register
//! accesses are forced to the previous timestamp `0` as well, and each cancels against
//! itself (doc §Filling the tables). The rows therefore touch nothing, and the prover
//! writes them out rather than executing anything.
//!
//! A traversal of the size-`s` block costs exactly `s + 1` rows: `s` of its own table and
//! one of `ALU`'s, the jump. Nothing else, and nothing on any other table. That is what
//! makes the solve here exact, with no calibrated cost model and no residual to correct.
//!
//! The sizes are powers of two so any fill is reachable exactly, while the bulk rides the
//! largest block at one jump per 128 rows. A table already sitting on a power of two is
//! never entered at all. `ALU`, where the jumps land, also has the block of size zero, a
//! jump to itself: its traversals cost `s + 1` rows each, and that one makes a gap of a
//! single row reachable.

use crate::rv::Class;
use crate::rv::asm;
use crate::tables::{CLASSES, N_TABLES};

/// Block sizes, largest first: a fill of `f` rows takes `f / 128` traversals of the
/// largest block and then one per set bit of the remainder. The last, a lone jump,
/// is `ALU`'s only.
pub const SIZES: [usize; 9] = [128, 64, 32, 16, 8, 4, 2, 1, 0];

/// Least rows a table can be proven over: flock sizes a batch to at least eight
/// instances and its zerocheck to a cube of at least `2^13` bits
/// ([`crate::class_flock::n_blocks_log`]). Filling a table below its floor would leave
/// it padded up to it, which is the padding this exists to avoid.
pub fn min_rows(t: usize) -> usize {
    1 << crate::class_flock::n_blocks_log(CLASSES[t], 1)
}

/// `ALU`'s index in [`CLASSES`]. Every traversal of every block lands its closing jump
/// here, so this table is solved last, absorbing the cost of the whole fill.
pub const JUMP: usize = 0;
const _: () = assert!(matches!(CLASSES[JUMP].class, Class::Alu));

/// One block in the text: `size` no-ops of `table`'s class from entry `index`, then the
/// jump back to `index`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub index: usize,
    pub size: usize,
    pub table: usize,
}

/// A no-op of `class`: every register is `x0`, which a padding row never touches for real.
fn nop(class: Class) -> u32 {
    match class {
        Class::Alu => asm::i_type(0x13, 0, 0, 0, 0),
        // A load and a store of the byte at address zero, which clock zero never checks.
        Class::Load => asm::i_type(0x03, 0, 0, 0, 0),
        Class::Store => asm::s_type(0x23, 0, 0, 0, 0),
        Class::Shift => asm::i_type(0x13, 1, 0, 0, 0),
        Class::Mul => asm::r_type(0x33, 0, 1, 0, 0, 0),
        Class::Mulh => asm::r_type(0x33, 3, 1, 0, 0, 0),
        Class::Div => asm::r_type(0x33, 5, 1, 0, 0, 0),
        // A compression of the block at address zero, which clock zero never checks.
        Class::Hash => asm::r_type(crate::rv::hash::OPCODE, 0, 0, 0, 0, 0),
        Class::Illegal => unreachable!("no fill block of an illegal entry"),
    }
}

/// Whether a text of `words` instructions still leaves room, inside the text region,
/// for the illegal word and the padding blocks [`crate::cpu::Program::new`] appends,
/// and for the pad to a power of two ([`crate::rv::Program::new`]).
pub fn text_fits(words: usize) -> bool {
    let mut blocks = Vec::new();
    append_blocks(&mut blocks);
    words
        .checked_add(blocks.len() + 1 + 2)
        .is_some_and(|total| total.next_power_of_two() <= 1 << crate::rv::MAX_LOG_TEXT)
}

/// Append every table's blocks to `text`, returning where each one landed.
pub fn append_blocks(text: &mut Vec<u32>) -> Vec<Block> {
    let mut blocks = Vec::new();
    for (t, spec) in CLASSES.iter().enumerate() {
        for size in SIZES.into_iter().filter(|&size| size > 0 || t == JUMP) {
            blocks.push(Block {
                index: text.len(),
                size,
                table: t,
            });
            text.extend(std::iter::repeat_n(nop(spec.class), size));
            // The closing jump, which a padding row takes back to the block's top.
            text.push(asm::j_type(0, -4 * size as i32));
        }
    }
    blocks
}

/// Traversals per block: `plan[t][k]` is how many times the size-`SIZES[k]` block of
/// table `t` is traversed.
pub type Plan = [[usize; SIZES.len()]; N_TABLES];

/// Traversals in total, which is the number of jump rows the fill costs.
pub fn traversals(plan: &Plan) -> usize {
    plan.iter().flatten().sum()
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
    for (k, &s) in SIZES.iter().enumerate().filter(|&(_, &s)| s > 0) {
        out[k] = left / s;
        left -= out[k] * s;
    }
    debug_assert_eq!(left, 0, "the positive sizes end at 1, so nothing can be left over");
    out
}

/// The smallest power of two that is at least `n`, and at least `1`.
fn ceil_pow2(n: usize) -> usize {
    n.max(1).next_power_of_two()
}

/// Traversals whose rows land on `JUMP` itself, delivering exactly `gap` rows. A
/// traversal of the size-`s` block gives that table `s + 1` rows here, its no-ops plus
/// its own closing jump, so the sizes to decompose over are `s + 1`, down to the lone
/// jump's `1`.
fn decompose_jump(gap: usize) -> [usize; SIZES.len()] {
    let mut out = [0usize; SIZES.len()];
    let mut left = gap;
    for (k, &s) in SIZES.iter().enumerate() {
        out[k] = left / (s + 1);
        left -= out[k] * (s + 1);
    }
    out
}

/// A plan taking every table from `base` to an exact power of two.
///
/// Every table but `JUMP` is independent: its fill is the distance to its next power of
/// two, decomposed into traversals. `JUMP` is not, because every traversal of the whole
/// fill lands a row there, its own traversals included. Counting those first makes it a
/// single decomposition rather than a fixpoint.
pub fn solve(base: [usize; N_TABLES]) -> Plan {
    let mut plan: Plan = [[0; SIZES.len()]; N_TABLES];
    for t in 0..N_TABLES {
        if t != JUMP {
            plan[t] = decompose(ceil_pow2(base[t].max(min_rows(t))) - base[t]);
        }
    }
    // What `JUMP` already owes: its own rows, plus one per traversal so far.
    let owed = base[JUMP] + traversals(&plan);
    plan[JUMP] = decompose_jump(ceil_pow2(owed.max(min_rows(JUMP))) - owed);
    debug_assert!(is_filled(filled(base, &plan)));
    plan
}

/// The cycles a run needs, in the order to walk them: for each, the block's first
/// entry, its size, and how many times to traverse it.
pub fn cycles(blocks: &[Block], base: [usize; N_TABLES]) -> Vec<(usize, usize, usize)> {
    let plan = solve(base);
    let mut out = Vec::new();
    for (t, row) in plan.iter().enumerate() {
        for (k, &n) in row.iter().enumerate() {
            if n == 0 {
                continue;
            }
            let size = SIZES[k];
            let block = blocks
                .iter()
                .find(|b| b.table == t && b.size == size)
                .unwrap_or_else(|| panic!("the program has no fill block for table {t}, size {size}"));
            out.push((block.index, size, n));
        }
    }
    out
}

/// The row counts a plan produces from `base`: its fill, plus one jump per traversal.
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
        .all(|(u, &c)| c.is_power_of_two() && c >= min_rows(u))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Whatever the shape of the run, every table comes out an exact power of two at or
    /// above its floor, and no further than the next one: a gap of a single row included,
    /// which the closing jumps of the other tables' fills can leave `ALU` with.
    #[test]
    fn solve_reaches_power_of_two_floors() {
        let mut cases = vec![[0; N_TABLES], [1; N_TABLES], [125_000; N_TABLES], [1 << 17; N_TABLES]];
        for alu in [(1 << 17) - 3, (1 << 17) - 2, (1 << 17) - 1] {
            let mut base = [1 << 10; N_TABLES];
            base[JUMP] = alu;
            cases.push(base);
        }
        for base in cases {
            let plan = solve(base);
            let got = filled(base, &plan);
            assert!(is_filled(got), "{base:?} filled to {got:?}");
            for t in 0..N_TABLES {
                let owed = base[t]
                    + if t == JUMP {
                        traversals(&plan) - plan[JUMP].iter().sum::<usize>()
                    } else {
                        0
                    };
                assert_eq!(got[t], ceil_pow2(owed.max(min_rows(t))), "{base:?} filled to {got:?}");
            }
        }
    }

    /// The bulk of a fill rides the largest block, so the fill stays cheap: one closing
    /// jump per 128 rows, plus at most one traversal per size per table for the
    /// remainders.
    #[test]
    fn fill_uses_bulk_blocks() {
        let base = [125_000; N_TABLES];
        let plan = solve(base);
        let fill: usize = delivered(&plan).iter().sum();
        assert!(
            traversals(&plan) <= fill / SIZES[0] + SIZES.len() * N_TABLES,
            "{} traversals for {fill} rows",
            traversals(&plan)
        );
    }
}
