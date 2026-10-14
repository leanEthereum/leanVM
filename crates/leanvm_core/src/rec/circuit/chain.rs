//! Hash chains on the dynamic bus: one `STEP` row per step, tied to its `HASH` row, and one `LINK` row per chain.
//!
//! A step pulls its input at its position's key and pushes its output at the next position's; a link pushes the
//! chain's tip at the position its digit names and pulls its end at position 7. The rows of a circuit balance only
//! if every key is pushed and pulled as often, with the same words.

use super::Builder;
use crate::rec::circuit::{Kw, Limbs, PARAM_IV, TableSlots};
use crate::rec::clean::{LINK_A, LINK_D, LINK_E, LINK_T, LINK_W, STEP_A, STEP_BASE, STEP_J, STEP_O, STEP_T, STEP_V};
use crate::rec::table::Table;

/// The bits of a tweak word a step's columns hold past its base: the position and chain at bits 32 to 40.
const POSITION_BITS: u64 = 0x1ff << 32;

impl Builder {
    /// One chain step: `T`, `v0`, `v1` as fresh `K` wires holding `tweak` and `v`, the hash row of the 6-word message
    /// `T, idx, p0, p1, v0, v1` from the parameter IV, and the step row reading `T`, `v`, the output's first three
    /// words, `tag`, `one` and `base`.
    ///
    /// Callers hold `one` to the constant one, so the step moves its position by one, `tag` to a constant, and `base`
    /// to the constant below `2^32` that `tweak` adds its position at bits 32 and up to.
    #[expect(
        clippy::too_many_arguments,
        reason = "the wires and values of `Model.chainStep`'s call"
    )]
    pub fn chain_step(&mut self, idx: Kw, pp: [Kw; 2], base: Kw, tag: Kw, one: Kw, tweak: u64, v: [u64; 2]) {
        traced!(
            self,
            format!(
                "chain_step {} {} {} {} {} {}",
                idx.0, pp[0].0, pp[1].0, base.0, tag.0, one.0
            ),
            self.chain_step_rows(idx, pp, base, tag, one, tweak, v)
        );
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the wires and values of `Model.chainStep`'s call"
    )]
    fn chain_step_rows(&mut self, idx: Kw, pp: [Kw; 2], base: Kw, tag: Kw, one: Kw, tweak: u64, v: [u64; 2]) {
        let t = self.free_k(tweak);
        let v = v.map(|x| self.free_k(x));
        let z = self.k_zero();
        let h = self.d_const(PARAM_IV);
        let (_, ch) = self.leaf_block_rows(h, [t, idx, pp[0], pp[1], v[0], v[1], z, z], 48, true);
        let mut slots = [0u32; Table::Step.n_slots()];
        for (slot, w) in [
            (STEP_T, t.0),
            (STEP_V, v[0].0),
            (STEP_V + 1, v[1].0),
            (STEP_O, ch.0),
            (STEP_J, tag.0),
            (STEP_A, one.0),
            (STEP_BASE, base.0),
        ] {
            slots[slot] = w;
        }
        self.row(Table::Step, &slots);
    }

    /// One chain: `t0`, `t1` and `e0`, `e1` as fresh `K` wires holding `tip` and `end`, and the link row reading
    /// `w`, the digit's bits `d`, the tip, the end and `one`. Returns the end's wires.
    ///
    /// Callers hold `one` to the constant one, so the link pulls the end at position 7.
    pub fn link(&mut self, w: Kw, d: [Kw; 3], one: Kw, tip: [u64; 2], end: [u64; 2]) -> [Kw; 2] {
        traced!(
            self,
            format!("link {} {} {} {} {}", w.0, d[0].0, d[1].0, d[2].0, one.0),
            self.link_rows(w, d, one, tip, end)
        )
    }

    fn link_rows(&mut self, w: Kw, d: [Kw; 3], one: Kw, tip: [u64; 2], end: [u64; 2]) -> [Kw; 2] {
        let t = tip.map(|x| self.free_k(x));
        let e = end.map(|x| self.free_k(x));
        let mut slots = [0u32; Table::Link.n_slots()];
        for (slot, w) in [
            (LINK_W, w.0),
            (LINK_D, d[0].0),
            (LINK_D + 1, d[1].0),
            (LINK_D + 2, d[2].0),
            (LINK_T, t[0].0),
            (LINK_T + 1, t[1].0),
            (LINK_E, e[0].0),
            (LINK_E + 1, e[1].0),
            (LINK_A, one.0),
        ] {
            slots[slot] = w;
        }
        self.row(Table::Link, &slots);
        e
    }
}

/// The check that the dynamic tuples balance, every `(key, x0, x1)` pushed as often as pulled.
pub(super) const BALANCE: &str = "the dynamic tuples balance";

/// Step and link rows on the values: their tuples, and the checks they fail.
pub(super) struct Dynamic {
    /// Each row's pushed tuple, `(key, x0, x1)`.
    pushed: Vec<[u64; 3]>,
    /// Each row's pulled tuple.
    pulled: Vec<[u64; 3]>,
    /// Per dynamic table, the checks its rows fail, in row order: each step's tweak word is its base, below `2^32`,
    /// plus a position at bits 32 to 40, and each `a` is Boolean.
    pub(super) failures: [Vec<&'static str>; 2],
}

impl Dynamic {
    /// The rows `rows` of each dynamic table, row-major, their wires' values by `value`.
    pub(super) fn of(rows: [&[u32]; 2], value: impl Fn(u32) -> Limbs) -> Self {
        let n_rows: usize = (Table::DYNAMIC.iter().zip(rows))
            .map(|(t, r)| r.len() / t.n_slots())
            .sum();
        let mut pushed = Vec::with_capacity(n_rows);
        let mut pulled = Vec::with_capacity(n_rows);
        let mut cols = Vec::new();
        let failures = std::array::from_fn(|k| {
            let (table, mut failures) = (Table::DYNAMIC[k], Vec::new());
            let tuples = table.dynamic_tuples().expect("a dynamic table");
            let a = if table == Table::Step { STEP_A } else { LINK_A };
            for row in rows[k].chunks_exact(table.n_slots()) {
                let slot = |s: usize| value(row[s]);
                if table == Table::Step {
                    let (t, base) = (slot(STEP_T)[0], slot(STEP_BASE)[0]);
                    if base >> 32 != 0 || (t ^ base) & !POSITION_BITS != 0 {
                        failures.push("a step's tweak word is its base plus a position");
                    }
                }
                if slot(a)[0] > 1 {
                    failures.push("a step's or link's a is Boolean");
                }
                let [push, pull] = tuples.at(slot, &mut cols);
                pushed.push(push.map(|x| x.0));
                pulled.push(pull.map(|x| x.0));
            }
            failures
        });
        Self {
            pushed,
            pulled,
            failures,
        }
    }

    /// Whether the tuples balance, every one pushed as often as pulled.
    pub(super) fn balance(&mut self) -> bool {
        self.pushed.sort_unstable();
        self.pulled.sort_unstable();
        self.pushed == self.pulled
    }
}

/// The checks a circuit's step and link rows fail on the values, each wire's at its number, the balance last.
pub(super) fn dynamic_failures(rows: &TableSlots, values: &[Limbs]) -> Vec<&'static str> {
    let mut dynamic = Dynamic::of(Table::DYNAMIC.map(|t| rows.of(t)), |w| values[w as usize]);
    let mut failures = dynamic.failures.concat();
    if !dynamic.balance() {
        failures.push(BALANCE);
    }
    failures
}

/// Honest chains for tests, as planned rows a test may tamper with before they become rows.
#[cfg(test)]
pub(crate) mod testing {
    use super::Builder;
    use crate::rec::circuit::{Kw, chain};

    /// The hash message's index word and parameter words.
    const IDX: u64 = 0x1d;
    const PP: [u64; 2] = [0x77, 0x99];
    /// The tag every key carries, at bits 41 and up.
    const TAG: u64 = 3 << 41;

    /// A row of a test's chains.
    #[derive(Clone, Copy, Debug)]
    pub(crate) enum Planned {
        /// A step hashing `v` under the tweak word `tweak`.
        Step { tweak: u64, v: [u64; 2] },
        /// Chain `c`'s link: its digit, tip and end.
        Link {
            c: u64,
            d: u64,
            tip: [u64; 2],
            end: [u64; 2],
        },
    }

    /// The tweak words' base: leanXMSS's, `tweak0(1, 0)`.
    const BASE: u64 = 0x100;

    /// The tweak word of position `s` of chain `c`: `tweak0(1, 8c + s)`.
    pub(crate) const fn tweak(c: u64, s: u64) -> u64 {
        BASE | (8 * c + s) << 32
    }

    /// A step's output words, natively.
    pub(crate) fn step(tweak: u64, v: [u64; 2]) -> [u64; 2] {
        let o = chain(&[tweak, IDX, PP[0], PP[1], v[0], v[1]]);
        [o[0], o[1]]
    }

    /// The honest rows of chains with the given digits: chain `i` from its tip, a step per position from its digit to
    /// 6, then its link.
    pub(crate) fn plan(digits: &[u64]) -> Vec<Planned> {
        let mut rows = Vec::new();
        for (c, &d) in (0..).zip(digits) {
            let tip = [0x1000 + c, 0x2000 + c];
            let mut v = tip;
            for s in d..7 {
                rows.push(Planned::Step { tweak: tweak(c, s), v });
                v = step(tweak(c, s), v);
            }
            rows.push(Planned::Link { c, d, tip, end: v });
        }
        rows
    }

    impl Builder {
        /// The planned rows, each link's end a statement word.
        pub(crate) fn emit_chains(&mut self, plan: &[Planned]) {
            let idx = self.k_const(IDX);
            let pp = PP.map(|p| self.k_const(p));
            let base = self.k_const(BASE);
            let tag = self.k_const(TAG);
            let one = self.k_const(1);
            for &row in plan {
                match row {
                    Planned::Step { tweak, v } => self.chain_step(idx, pp, base, tag, one, tweak, v),
                    Planned::Link { c, d, tip, end } => {
                        let w = self.k_const(tweak(c, 0) | TAG);
                        let d: [Kw; 3] = std::array::from_fn(|k| self.k_const(d >> k & 1));
                        for e in self.link(w, d, one, tip, end) {
                            self.expose(e);
                        }
                    }
                }
            }
        }
    }
}
