//! The recursion machine's tables: their slots, the columns each slot's limbs are made of, and their identities.
//!
//! The hash table's first columns are ports of its rows' packed BLAKE2s witnesses, which flock proves.
//! The public table commits nothing: its blocks are the framework's.

use super::circuit::{Assignment, WireKind};
use super::clean;
use crate::class_flock::{self, FlockId};
use crate::leaf::{BusForm, Coord};
use crate::tables::{PerTable, TableId, TableKey};
use WireKind::{D, E, K};
use flock::circuit::Circuit;
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
    /// A value the verifier knows: a constant of the circuit or a word of the statement.
    Pub,
}

/// One value per table of the recursion machine.
pub type PerRecTable<T> = PerTable<T, Table, { Table::COUNT }>;

/// The four limbs a slot carries, each a degree-two form over its table's local columns.
#[derive(Clone, Debug)]
pub(crate) struct SlotForm(pub(crate) [Coord; 4]);

/// Where a committed column's value is found: limb `limb` of slot `slot`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LimbOf {
    slot: usize,
    limb: usize,
}

/// The packed BLAKE2s witness behind the hash table, which flock proves.
///
/// The table's first columns are ports of it: the inputs `t`, `f`, `h0..h3`, `m0..m7`, then the outputs `o0..o3`.
pub(crate) struct HashFlock;

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

impl Table {
    /// How many tables there are.
    pub const COUNT: usize = 6;

    /// Every table, in protocol order.
    pub const ALL: [Self; Self::COUNT] = [Self::Emul, Self::Exk, Self::Hash, Self::Split, Self::Cast, Self::Pub];

    /// The tables owning columns: every table but the public one, which comes last.
    pub(crate) const OWNED: [Self; Self::COUNT - 1] = [Self::Emul, Self::Exk, Self::Hash, Self::Split, Self::Cast];

    /// Its name, as the documentation writes it.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Emul => "EMUL",
            Self::Exk => "EXK",
            Self::Hash => "HASH",
            Self::Split => "SPLIT",
            Self::Cast => "CAST",
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
            Self::Hash => HashFlock::N_PORTS + 1,
            Self::Split => 65,
            Self::Cast => 4,
            Self::Pub => 0,
        }
    }

    /// How many of its columns are ports of its packed witness: its first.
    pub(crate) const fn n_ports(self) -> usize {
        if matches!(self, Self::Hash) {
            HashFlock::N_PORTS
        } else {
            0
        }
    }

    /// `log2` of its height for `rows` rows: a power of two, at flock's floor for the hash table.
    pub(crate) fn height_log(self, rows: usize) -> usize {
        match self {
            Self::Hash => HashFlock::height_log(rows),
            _ => crate::log2_ceil_usize(rows.max(1)),
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
            Self::Pub => None,
        };
        SlotForm(limbs.unwrap_or_else(|| unreachable!("{self:?} has no slot {s}")))
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
            _ => Vec::new(),
        }
    }

    /// Each committed column, those past its ports, as the first slot limb that is that column alone.
    fn committed_sources(self) -> Vec<LimbOf> {
        let forms: Vec<SlotForm> = (0..self.n_slots()).map(|s| self.slot(s)).collect();
        (self.n_ports()..self.n_cols())
            .map(|c| {
                (forms.iter().enumerate())
                    .find_map(|(slot, form)| form.limb_of(c).map(|limb| LimbOf { slot, limb }))
                    .expect("every committed column is a slot's limb")
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
                *cell = F64(a.value(self, z, source.slot)[source.limb]);
            }
            column[height..].fill(F64::ZERO);
        }
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

impl HashFlock {
    /// How many ports the hash table reads, at the witness's words `0..18`.
    pub(crate) const N_PORTS: usize = 18;

    /// The packed witness of the BLAKE2s class circuit, which proves every hash row.
    pub(crate) const FLOCK: FlockId = FlockId::class(TableId::HASH).expect("the HASH class has a circuit");

    /// The BLAKE2s compression circuit.
    pub(crate) fn circuit() -> &'static Circuit {
        Self::FLOCK.circuit()
    }

    /// `log2` of a hash row's packed words: the stride between consecutive rows' same-port words.
    pub(crate) const fn stride_log() -> usize {
        Self::FLOCK.stride_log()
    }

    /// `log2` of the hash table's height for `rows` rows, at least flock's floor.
    const fn height_log(rows: usize) -> usize {
        class_flock::batch_log(Self::FLOCK.k_log(), rows)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tables::{ClassSpec, Word};
    use proptest::prelude::*;

    fn eval(c: &Coord, cols: &[F64]) -> F64 {
        match c {
            Coord::Const(v) => *v,
            Coord::Col(i) => cols[*i],
            Coord::Prod(i, j) => cols[*i] * cols[*j],
            Coord::Sum(cs) => cs.iter().fold(F64::ZERO, |acc, c| acc + eval(c, cols)),
            _ => unreachable!("a slot's limbs are formable"),
        }
    }

    fn out(t: Table, cols: &[F64]) -> [u64; 4] {
        t.slot(3).0.map(|c| eval(&c, cols).0)
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
    fn the_hash_ports_are_the_precompile_ports() {
        // The generated slot forms name the ports by column: `h` is slot 0, `(t, f)` slot 1, the message words slots
        // 8 to 15, the output slot 6, and the mux bit slot 3, the one committed column after the ports.
        let ports: Vec<Word> = ClassSpec::HASH.ports().collect();
        assert_eq!(ports.len(), HashFlock::N_PORTS);
        let col = |s: usize, limb: usize| match Table::Hash.slot(s).0[limb] {
            Coord::Col(c) => c,
            ref other => panic!("slot {s} limb {limb} is {other:?}"),
        };
        assert_eq!((ports[col(1, 0)], ports[col(1, 1)]), (Word::V2, Word::Flags));
        assert!((0..4).all(|i| ports[col(0, i)] == Word::Cell(i as u8)));
        assert!((0..8).all(|i| ports[col(8 + i, 0)] == Word::Cell(8 + i as u8)));
        assert!((0..4).all(|i| ports[col(6, i)] == Word::CellNew(4 + i as u8)));
        assert_eq!(col(3, 0), HashFlock::N_PORTS);
    }

    #[test]
    fn f64_products_are_the_proven_field() {
        // Invariant: the prover's `K` multiplies as `LeanVMCircuits.Rec.mul`, proven to be the field's product.
        for &(a, b, c) in clean::K_PRODUCTS {
            assert_eq!(F64(a) * F64(b), F64(c), "{a:#x} * {b:#x}");
        }
    }
}
