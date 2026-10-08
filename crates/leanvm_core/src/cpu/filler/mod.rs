//! Filling every table to a power of two with padding rows at clock zero.
//!
//! A table is proven over a power of two of rows, so a run has to make up the difference.
//!
//! The text carries a block per table and per size.
//!
//! A block is that many no-ops of the table's class, then a `JAL` back to its first instruction.
//!
//! So a block is a cycle, and no program code jumps into it.
//!
//! Its rows carry the clock zero, which lacks the live bit, so it does not advance.
//!
//! - The state tuples pushed and pulled around the cycle cancel, for any number of traversals.
//! - Each access pulls the very tuple it pushes, which cancels too (doc §Filling the tables).
//! - Nothing such a row puts on the bus can meet a tuple of the run, which all have the live bit.
//!
//! The rows therefore touch nothing, and the prover writes them out rather than executing them.
//!
//! A traversal of the size-`s` block costs exactly `s + 1` rows: `s` of its table, and the jump, on the ALU.
//!
//! That is what makes the solve exact, with no cost model and no residual to correct.

use crate::rv::asm::{Op, Reg};
use crate::tables::{N_TABLES, PerTable, TableId};

/// Block sizes, largest first.
///
/// A fill of `f` rows takes `f / 128` traversals of the largest block, then one per set bit of the remainder.
///
/// The last, a lone jump, is the ALU's only: it makes a gap of a single row reachable.
pub const SIZES: [usize; 9] = [128, 64, 32, 16, 8, 4, 2, 1, 0];

/// The table of the closing jumps, the ALU.
///
/// Every traversal of every block lands its closing jump there.
///
/// So that table is solved last, absorbing the cost of the whole fill.
pub const JUMP: TableId = TableId::ALU;

/// One block in the text: `size` no-ops of `table`'s class from entry `index`, then the jump back to `index`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    /// The block's first entry.
    pub index: usize,
    /// The no-ops before the closing jump.
    pub size: usize,
    /// The table whose class the no-ops are.
    pub table: TableId,
}

/// Every table's fill blocks, as they sit in a program's text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FillBlocks(Vec<Block>);

impl FillBlocks {
    /// The words the blocks take in the text: each block's no-ops, then its closing jump.
    pub const WORDS: usize = {
        let mut words = 0;
        let mut t = 0;
        while t < N_TABLES {
            let mut k = 0;
            while k < SIZES.len() {
                if SIZES[k] > 0 || t == JUMP.index() {
                    words += SIZES[k] + 1;
                }
                k += 1;
            }
            t += 1;
        }
        words
    };

    /// Append every table's blocks to `text`.
    ///
    /// Each table gets a block per positive size, and the ALU the lone jump too.
    pub fn append(text: &mut Vec<u32>) -> Self {
        let mut blocks = Vec::new();
        for t in TableId::ALL {
            for size in SIZES.into_iter().filter(|&size| size > 0 || t == JUMP) {
                blocks.push(Block {
                    index: text.len(),
                    size,
                    table: t,
                });
                // A no-op touches only `x0` and address zero, which a padding row at clock zero never touches for real.
                let nop = t
                    .class()
                    .nop()
                    .expect("every table's class has an instruction")
                    .encode()
                    .bits();
                text.extend(std::iter::repeat_n(nop, size));

                // The closing jump, which a padding row takes back to the block's top.
                text.push(
                    Op::Jal {
                        rd: Reg::ZERO,
                        offset: -4 * size as i32,
                    }
                    .encode()
                    .bits(),
                );
            }
        }
        Self(blocks)
    }

    /// The block of `table` with `size` no-ops, if it has one.
    pub fn get(&self, table: TableId, size: usize) -> Option<&Block> {
        self.0.iter().find(|b| b.table == table && b.size == size)
    }

    /// The cycles `plan` walks, in order: each block's first entry, its size, and how many traversals.
    ///
    /// # Panics
    ///
    /// Panics if a block the plan traverses is missing.
    pub fn cycles(&self, plan: &Plan) -> Vec<(usize, usize, usize)> {
        let mut out = Vec::new();
        for (t, traversals) in plan.0.iter() {
            for (k, &n) in traversals.0.iter().enumerate().filter(|&(_, &n)| n > 0) {
                let size = SIZES[k];
                let block = self
                    .get(t, size)
                    .unwrap_or_else(|| panic!("the program has no fill block for {}, size {size}", t.name()));
                out.push((block.index, size, n));
            }
        }
        out
    }
}

/// How often each of one table's blocks is traversed: entry `k` counts its size-`SIZES[k]` block.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Traversals([usize; SIZES.len()]);

impl Traversals {
    /// The traversals delivering exactly `fill` rows to their own table.
    ///
    /// As many of the largest block as fit, then the binary decomposition of the rest.
    fn delivering(fill: usize) -> Self {
        let mut left = fill;
        let out = SIZES.map(|size| {
            // The lone jump supplies no rows to a non-ALU table.
            if size == 0 {
                return 0;
            }
            let count = left / size;
            left -= count * size;
            count
        });
        debug_assert_eq!(left, 0, "the positive sizes end at 1, so nothing can be left over");
        Self(out)
    }

    /// The ALU's own traversals, landing exactly `gap` rows on it.
    ///
    /// A traversal of the size-`s` block gives the ALU `s + 1` rows: its no-ops and its own closing jump.
    ///
    /// So the sizes to decompose over are `s + 1`, down to the lone jump's 1.
    fn landing_on_jump(gap: usize) -> Self {
        let mut left = gap;
        let out = SIZES.map(|size| {
            // Each traversal contributes its closing jump to the ALU too.
            let count = left / (size + 1);
            left -= count * (size + 1);
            count
        });
        Self(out)
    }

    /// The traversals in total: one closing jump each.
    pub fn count(&self) -> usize {
        self.0.iter().sum()
    }

    /// The rows the traversals deliver to their own table, not counting the closing jumps.
    pub fn delivered(&self) -> usize {
        self.0.iter().zip(SIZES).map(|(&n, size)| n * size).sum()
    }
}

/// How the fill traverses every table's blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan(PerTable<Traversals>);

impl Plan {
    /// The plan taking every table from `base` rows to its provable height: the next power of two at or above its floor.
    ///
    /// Every table but the ALU is independent: its fill is the distance to that height.
    ///
    /// The ALU is not, since every traversal lands a row there, its own included.
    ///
    /// Counting those first makes it one decomposition rather than a fixpoint.
    pub fn solve(base: PerTable<usize>) -> Self {
        let height = |t: TableId, rows: usize| t.spec().provable_height(rows);
        let mut plan = Self(PerTable::default());
        for t in TableId::ALL.into_iter().filter(|&t| t != JUMP) {
            plan.0[t] = Traversals::delivering(height(t, base[t]) - base[t]);
        }

        // What the ALU already owes: its own rows, plus one per traversal so far.
        let owed = base[JUMP] + plan.traversals();
        plan.0[JUMP] = Traversals::landing_on_jump(height(JUMP, owed) - owed);
        debug_assert!(
            plan.filled(base)
                .iter()
                .all(|(t, &rows)| t.spec().is_provable_height(rows))
        );
        plan
    }

    /// The traversals in total: the number of jump rows the fill costs.
    pub fn traversals(&self) -> usize {
        self.0.values().map(Traversals::count).sum()
    }

    /// The row counts the plan produces from `base`: its fill, plus one jump per traversal.
    pub fn filled(&self, base: PerTable<usize>) -> PerTable<usize> {
        let mut out = PerTable::from_fn(|t| base[t] + self.0[t].delivered());
        out[JUMP] += self.traversals();
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_word_count_is_what_append_writes() {
        let mut text = Vec::new();
        FillBlocks::append(&mut text);
        assert_eq!(text.len(), FillBlocks::WORDS);
    }

    #[test]
    fn solve_reaches_each_tables_provable_height() {
        // Fixture: empty, tiny, large and power-of-two runs, then ALU gaps of 3, 2 and 1 rows.
        //
        // A gap of one row is what the other tables' closing jumps can leave the ALU with.
        let mut cases: Vec<_> = [0, 1, 125_000, 1 << 17].map(|n| PerTable::new([n; N_TABLES])).into();
        for alu in [(1 << 17) - 3, (1 << 17) - 2, (1 << 17) - 1] {
            let mut base = PerTable::new([1 << 10; N_TABLES]);
            base[JUMP] = alu;
            cases.push(base);
        }

        for base in cases {
            let plan = Plan::solve(base);
            let got = plan.filled(base);

            // Every table lands on the nearest provable height: what it owed, rounded up, the ALU owing the others' jumps too.
            for t in TableId::ALL {
                let spec = t.spec();
                let jumps = if t == JUMP {
                    plan.traversals() - plan.0[JUMP].count()
                } else {
                    0
                };
                let owed = base[t] + jumps;
                assert!(spec.is_provable_height(got[t]), "{base:?} filled to {got:?}");
                assert_eq!(
                    got[t],
                    owed.max(spec.min_rows()).next_power_of_two(),
                    "{base:?} filled to {got:?}"
                );
            }
        }
    }

    #[test]
    fn the_bulk_of_a_fill_rides_the_largest_block() {
        // Fixture: 125 000 rows short of a power of two on every table.
        let base = PerTable::new([125_000; N_TABLES]);
        let plan = Plan::solve(base);
        let fill: usize = plan.0.values().map(Traversals::delivered).sum();

        // One closing jump per 128 rows, plus at most one traversal per size per table for the remainders.
        assert!(
            plan.traversals() <= fill / SIZES[0] + SIZES.len() * N_TABLES,
            "{} traversals for {fill} rows",
            plan.traversals()
        );
    }
}
