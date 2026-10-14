//! The recursion machine's tables: their slots, the columns each slot's limbs are made of, and their identities.
//!
//! The hash table's first columns are ports of its rows' packed BLAKE2s witnesses, which flock proves.
//! The step and link tables also push and pull dynamic tuples, keyed by their data.
//! The public table commits nothing: its blocks are the framework's.

use super::circuit::{Assignment, Limbs, WireKind};
use super::{clean, hash};
use crate::bus::{BusForm, Coord};
use crate::tables::{self, PerTable, TableKey};
use WireKind::{D, E, K};
use primitives::field::{F64, F192};

/// The recursion machine's tables, in protocol order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Table {
    /// `c = a·b + d` over `E`, slots `a`, `b`, `d`, `c`.
    Emul,
    /// `c = a·k + d` with `k` in `K`, slots `a`, `k`, `d`, `c`.
    Exk,
    /// One BLAKE2s compression per row: a transcript step, a Merkle node or a block of a leaf.
    Hash,
    /// A word and its 64 bits.
    Split,
    /// Four words seen as a digest, an `E` element, two 128-bit halves and four `K` words.
    Cast,
    /// One step of a hash chain: pulls its input at its position's key and pushes its output at the next position's.
    Step,
    /// One hash chain: pushes its start at the position its digit names and pulls its end at position 7.
    Link,
    /// A value the verifier knows: a constant of the circuit or a word of the statement.
    Pub,
}

/// One value per table of the recursion machine.
pub type PerRecTable<T> = PerTable<T, Table, { Table::COUNT }>;

/// Each table's base-two logarithm of rows, none for a table the proof leaves out.
pub type Heights = PerRecTable<Option<usize>>;

/// The four limbs a slot carries, each a degree-two form over its table's local columns.
#[derive(Clone, Debug)]
pub(crate) struct SlotForm(pub(crate) [Coord; 4]);

/// Where a committed column's value is found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ColumnSource {
    /// Limb `limb` of slot `slot`.
    Limb { slot: usize, limb: usize },
    /// Bit `k` of a step row's position and chain, bit `32 + k` of its tweak word.
    TweakBit(usize),
    /// A step row's carry `s0·s1`.
    Carry,
}

/// A hash row's slots, in order:
///
/// - the chaining value `h`, the counter and final flag `(t, f)`;
/// - the message's first half through the Merkle mux, the mux's bit `b`;
/// - the message's words 4 to 6 as `x` and its word 7 as `ds`;
/// - the output, the output's first three words as a challenge;
/// - the eight message words.
const HASH_KINDS: [WireKind; 16] = [D, D, D, K, E, K, D, E, K, K, K, K, K, K, K, K];

/// A cast row's slots: the digest, the element of its first three words, its two halves, its four words.
const CAST_KINDS: [WireKind; 8] = [D, E, E, E, K, K, K, K];

/// A step row's slots: its tweak word, its two input words, its output's first three words, its tag, its bit `a`, its
/// tweak word's base.
const STEP_KINDS: [WireKind; 7] = [K, K, K, E, K, K, K];

impl Table {
    /// How many tables there are.
    pub const COUNT: usize = 8;

    /// Every table, in protocol order.
    pub const ALL: [Self; Self::COUNT] = [
        Self::Emul,
        Self::Exk,
        Self::Hash,
        Self::Split,
        Self::Cast,
        Self::Step,
        Self::Link,
        Self::Pub,
    ];

    /// The tables owning columns: every table but the public one, which comes last.
    pub(crate) const OWNED: [Self; Self::COUNT - 1] = [
        Self::Emul,
        Self::Exk,
        Self::Hash,
        Self::Split,
        Self::Cast,
        Self::Step,
        Self::Link,
    ];

    /// The tables with dynamic tuples, each with an activity column: one on the circuit's rows, zero on padding.
    pub(crate) const DYNAMIC: [Self; 2] = [Self::Step, Self::Link];

    /// Its name, as the documentation writes it.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Emul => "EMUL",
            Self::Exk => "EXK",
            Self::Hash => "HASH",
            Self::Split => "SPLIT",
            Self::Cast => "CAST",
            Self::Step => "STEP",
            Self::Link => "LINK",
            Self::Pub => "PUB",
        }
    }

    /// Its slots' kinds.
    ///
    /// A public slot carries a wire of any kind; its one entry is the widest.
    pub const fn slot_kinds(self) -> &'static [WireKind] {
        match self {
            Self::Emul => &[E, E, E, E],
            Self::Exk => &[E, K, E, E],
            Self::Hash => &HASH_KINDS,
            Self::Split => &[K; 65],
            Self::Cast => &CAST_KINDS,
            Self::Step => &STEP_KINDS,
            Self::Link => &[K; 9],
            Self::Pub => &[D],
        }
    }

    /// Its number of slots.
    pub const fn n_slots(self) -> usize {
        self.slot_kinds().len()
    }

    /// The index of its first slot among all tables' slots.
    pub const fn first_slot(self) -> usize {
        let mut total = 0;
        let mut i = 0;
        while i < self as usize {
            total += Self::ALL[i].n_slots();
            i += 1;
        }
        total
    }

    /// How many columns it has, its ports first.
    pub(crate) const fn n_cols(self) -> usize {
        match self {
            Self::Emul => 9,
            Self::Exk => 7,
            Self::Hash => hash::N_PORTS + 1,
            Self::Split => 65,
            Self::Cast => 4,
            Self::Step => 18,
            Self::Link => 9,
            Self::Pub => 0,
        }
    }

    /// How many of its columns are ports of its packed witness: its first.
    pub(crate) const fn n_ports(self) -> usize {
        if matches!(self, Self::Hash) { hash::N_PORTS } else { 0 }
    }

    /// `log2` of its height for `rows` rows: a power of two, at flock's floor for the hash table.
    ///
    /// A table with no rows has none, and the proof leaves it out, other than the hash table, whose packed witness flock
    /// proves at its floor, and the public table, whose blocks are the framework's.
    pub(crate) fn height_log(self, rows: usize) -> Option<usize> {
        match self {
            Self::Hash => Some(tables::batch_log(hash::CIRCUIT.k_log(), rows)),
            Self::Pub => Some(crate::log2_ceil_usize(rows.max(1))),
            _ => (rows > 0).then(|| crate::log2_ceil_usize(rows)),
        }
    }

    /// The limbs slot `s` carries, over its local columns: the forms `LeanVMCircuits.Rec.Tables` proves.
    pub(crate) fn slot(self, s: usize) -> SlotForm {
        let limbs = match self {
            Self::Emul => clean::emul(s),
            Self::Exk => clean::exk(s),
            Self::Hash => clean::hash(s),
            Self::Split => clean::split(s),
            Self::Cast => clean::cast(s),
            Self::Step => clean::step(s),
            Self::Link => clean::link(s),
            Self::Pub => None,
        };
        SlotForm(limbs.unwrap_or_else(|| unreachable!("{self:?} has no slot {s}")))
    }

    /// Its dynamic tuples, push then pull, each a key and two words over its local columns, if it has any.
    pub(crate) fn dynamic(self) -> Option<[[Coord; 3]; 2]> {
        match self {
            Self::Step => Some([clean::step_push(), clean::step_pull()]),
            Self::Link => Some([clean::link_push(), clean::link_pull()]),
            _ => None,
        }
    }

    /// The identities its rows satisfy, each a degree-two form over its local columns that vanishes.
    pub(crate) fn identities(self) -> Vec<BusForm> {
        let n = self.n_cols();
        let form = |&(linear, prods): &clean::Identity| {
            let mut coeffs = vec![F192::ZERO; n];
            for &(c, w) in linear {
                coeffs[c] += F192::from(F64(w));
            }
            BusForm {
                coeffs,
                prods: prods.iter().map(|&(a, b, w)| (a, b, F192::from(F64(w)))).collect(),
                constant: F192::ZERO,
            }
        };
        match self {
            // A Boolean mux bit; what a hash row hashes is its wiring's.
            Self::Hash => clean::HASH_IDENTITIES.iter().map(form).collect(),
            // A word is its bits, each Boolean.
            Self::Split => clean::SPLIT_IDENTITIES.iter().map(form).collect(),
            // A step's bits are Boolean and its carry their product; a step's and a link's `a` is Boolean.
            Self::Step => clean::STEP_IDENTITIES.iter().map(form).collect(),
            Self::Link => clean::LINK_IDENTITIES.iter().map(form).collect(),
            _ => Vec::new(),
        }
    }

    /// Each committed column, those past its ports: the first slot limb that is that column alone, else a step row's
    /// bits and carry, which its tweak word's slot gives.
    fn committed_sources(self) -> Vec<ColumnSource> {
        let forms: Vec<SlotForm> = (0..self.n_slots()).map(|s| self.slot(s)).collect();
        (self.n_ports()..self.n_cols())
            .map(|c| match (self, c) {
                (Self::Step, c) if (clean::STEP_BITS..clean::STEP_CARRY).contains(&c) => {
                    ColumnSource::TweakBit(c - clean::STEP_BITS)
                }
                (Self::Step, clean::STEP_CARRY) => ColumnSource::Carry,
                _ => (forms.iter().enumerate())
                    .find_map(|(slot, form)| form.limb_of(c).map(|limb| ColumnSource::Limb { slot, limb }))
                    .expect("every committed column is a slot's limb"),
            })
            .collect()
    }

    /// Write its committed columns, those past its ports, from the assignment.
    ///
    /// The windows are its local columns, each its height long; padding rows are zero.
    pub(crate) fn fill(self, a: &Assignment, windows: &mut [&mut [F64]]) {
        let height = a.wires.len(self);
        for (c, source) in self.committed_sources().into_iter().enumerate() {
            let column = &mut windows[self.n_ports() + c];
            for (z, cell) in column[..height].iter_mut().enumerate() {
                *cell = F64(source.value(|s| a.value(self, z, s)));
            }
            column[height..].fill(F64::ZERO);
        }
    }

    /// Its dynamic tuples as functions of a row's slot values, if it has any.
    pub(crate) fn dynamic_tuples(self) -> Option<DynamicTuples> {
        debug_assert_eq!(self.n_ports(), 0, "a dynamic tuple reads committed columns only");
        Some(DynamicTuples {
            tuples: self.dynamic()?,
            sources: self.committed_sources(),
        })
    }
}

/// A dynamic table's tuples as functions of a row's slot values: its committed columns' sources and its tuples' forms,
/// made once for all its rows.
pub(crate) struct DynamicTuples {
    /// Push then pull, each a key and two words over the table's local columns.
    tuples: [[Coord; 3]; 2],
    /// Each committed column's source.
    sources: Vec<ColumnSource>,
}

impl DynamicTuples {
    /// The tuples, push then pull, each `(key, x0, x1)`, of a row whose slots carry the given values; `cols` holds the
    /// row's columns, filled from those values as the prover's are.
    pub(crate) fn at(&self, slot: impl Fn(usize) -> Limbs, cols: &mut Vec<F64>) -> [[F64; 3]; 2] {
        cols.clear();
        cols.extend(self.sources.iter().map(|source| F64(source.value(&slot))));
        self.tuples
            .each_ref()
            .map(|tuple| tuple.each_ref().map(|c| eval_local(c, cols)))
    }
}

impl ColumnSource {
    /// The column's value on a row whose slots carry the given values.
    fn value(self, slot: impl Fn(usize) -> Limbs) -> u64 {
        let tweak_bit = |k: usize| (slot(clean::STEP_T)[0] >> (32 + k)) & 1;
        match self {
            Self::Limb { slot: s, limb } => slot(s)[limb],
            Self::TweakBit(k) => tweak_bit(k),
            Self::Carry => tweak_bit(0) & tweak_bit(1),
        }
    }
}

/// A degree-two form over a row's local columns, at the row's values.
pub(crate) fn eval_local(c: &Coord, cols: &[F64]) -> F64 {
    match c {
        Coord::Const(v) => *v,
        Coord::Col(i) => cols[*i],
        Coord::Prod(i, j) => cols[*i] * cols[*j],
        Coord::Scaled(v, i) => *v * cols[*i],
        Coord::ScaledProd(v, i, j) => *v * cols[*i] * cols[*j],
        Coord::Sum(cs) => cs.iter().fold(F64::ZERO, |acc, c| acc + eval_local(c, cols)),
        _ => unreachable!("a local form reads no public column"),
    }
}

impl SlotForm {
    /// Its limbs over the global columns, its table's first at `base`.
    pub(crate) fn offset(self, base: usize) -> [Coord; 4] {
        self.0.map(|c| c.offset(base))
    }

    /// The first limb that is column `c` alone.
    fn limb_of(&self, c: usize) -> Option<usize> {
        self.0.iter().position(|l| matches!(l, Coord::Col(x) if *x == c))
    }
}

impl TableKey<{ Self::COUNT }> for Table {
    const ALL: [Self; Self::COUNT] = Self::ALL;

    fn index(self) -> usize {
        self as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn out(t: Table, cols: &[F64]) -> [u64; 4] {
        t.slot(3).0.map(|c| eval_local(&c, cols).0)
    }

    // A step row at position `s` of chain `c` over a base `B` pulls at `X^63 + T + j` and, with `a = 1`, pushes at
    // position `s + 1` of the same chain (`s = 7` wraps to 0); its tweak slot is `T`. A link row pushes its tip at
    // position `d` and pulls its end at position 7.
    #[test]
    fn step_and_link_keys_are_chain_positions() {
        let j = 0x5a5 << 41;
        let (step, link) = (
            Table::Step.dynamic_tuples().unwrap(),
            Table::Link.dynamic_tuples().unwrap(),
        );
        let mut cols = Vec::new();
        // leanXMSS's base and leanSPHINCS's at layer 2.
        for base in [0x100, 0x2_0101] {
            let tweak = |c: u64, s: u64| base | (8 * c + s) << 32;
            for c in 0..64 {
                for s in 0..8 {
                    for a in 0..2 {
                        let t = tweak(c, s);
                        let values = [
                            [t, 0, 0, 0],
                            [11, 0, 0, 0],
                            [12, 0, 0, 0],
                            [13, 14, 15, 0],
                            [j, 0, 0, 0],
                            [a, 0, 0, 0],
                            [base, 0, 0, 0],
                        ];
                        let [push, pull] = step.at(|slot| values[slot], &mut cols);
                        let next = if a == 1 { tweak(c, (s + 1) % 8) } else { t };
                        assert_eq!(pull.map(|x| x.0), [1 << 63 | t | j, 11, 12], "c {c} s {s} a {a}");
                        assert_eq!(push.map(|x| x.0), [1 << 63 | next | j, 13, 14], "c {c} s {s} a {a}");
                        let cols: Vec<F64> = (Table::Step.committed_sources().into_iter())
                            .map(|source| F64(source.value(|slot| values[slot])))
                            .collect();
                        assert_eq!(eval_local(&Table::Step.slot(clean::STEP_T).0[0], &cols).0, t);
                    }
                }
            }
            let w = tweak(5, 0) | j;
            for d in 0..8 {
                let mut values = [[0; 4]; 9];
                values[clean::LINK_W][0] = w;
                for k in 0..3 {
                    values[clean::LINK_D + k][0] = d >> k & 1;
                }
                values[clean::LINK_T] = [21, 0, 0, 0];
                values[clean::LINK_T + 1] = [22, 0, 0, 0];
                values[clean::LINK_E] = [23, 0, 0, 0];
                values[clean::LINK_E + 1] = [24, 0, 0, 0];
                values[clean::LINK_A][0] = 1;
                let [push, pull] = link.at(|slot| values[slot], &mut cols);
                assert_eq!(push.map(|x| x.0), [1 << 63 | w | d << 32, 21, 22]);
                assert_eq!(pull.map(|x| x.0), [1 << 63 | w | 7 << 32, 23, 24]);
            }
        }
    }

    proptest! {
        #[test]
        fn emul_and_exk_outputs_are_e_arithmetic(w in proptest::array::uniform9(any::<u64>())) {
            let cols = w.map(F64);
            let e = |c: usize| F192::new(w[c], w[c + 1], w[c + 2]);
            let limbs = |x: F192| [x.c0, x.c1, x.c2, 0];
            prop_assert_eq!(out(Table::Emul, &cols), limbs(e(0) * e(3) + e(6)));
            prop_assert_eq!(out(Table::Exk, &cols[..7]), limbs(e(0).mul_base(F64(w[3])) + e(4)));
        }
    }

    #[test]
    fn every_slot_form_fits_its_kind() {
        let zero = |c: &Coord| matches!(c, Coord::Const(v) if v.0 == 0);
        for t in Table::OWNED {
            for (s, &kind) in t.slot_kinds().iter().enumerate() {
                let used = match kind {
                    WireKind::K => 1,
                    WireKind::E => 3,
                    WireKind::D => 4,
                };
                assert!(t.slot(s).0[used..].iter().all(zero), "{t:?} slot {s}");
            }
            assert_eq!(t.committed_sources().len(), t.n_cols() - t.n_ports());
        }
    }

    #[test]
    fn f64_products_are_the_proven_field() {
        // Invariant: the prover's `K` multiplies as `LeanVMCircuits.Rec.mul`, proven to be the field's product.
        for &(a, b, c) in clean::K_PRODUCTS {
            assert_eq!(F64(a) * F64(b), F64(c), "{a:#x} * {b:#x}");
        }
    }
}
