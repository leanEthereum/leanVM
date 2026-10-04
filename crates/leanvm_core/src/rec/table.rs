//! The recursion machine's tables: their slots, the columns each slot's limbs are made of, and their identities.
//!
//! The hash table's first columns are ports of its rows' packed BLAKE2s witnesses, which flock proves.
//! The public table commits nothing: its blocks are the framework's.

use super::circuit::{Assignment, Kind};
use crate::class_flock;
use crate::leaf::{BusForm, Coord};
use crate::tables::{self, Part};
use flock::circuit::Circuit as FlockCircuit;
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
const HASH_KINDS: [Kind; 16] = {
    use Kind::{D, E, K};
    [D, D, D, K, E, K, D, E, K, K, K, K, K, K, K, K]
};

/// A cast row's slots: the digest, the element of its first three words, its two halves, its four words.
const CAST_KINDS: [Kind; 8] = {
    use Kind::{D, E, K};
    [D, E, E, E, K, K, K, K]
};

impl Table {
    /// How many tables there are.
    pub const COUNT: usize = 6;

    /// Every table, in protocol order.
    pub const ALL: [Self; Self::COUNT] = [Self::Emul, Self::Exk, Self::Hash, Self::Split, Self::Cast, Self::Pub];

    /// The tables owning columns: every table but the public one, which comes last.
    pub(crate) const OWNED: [Self; Self::COUNT - 1] = [Self::Emul, Self::Exk, Self::Hash, Self::Split, Self::Cast];

    /// Its slots' kinds.
    ///
    /// A public slot carries a wire of any kind; its one entry is the widest.
    pub const fn slot_kinds(self) -> &'static [Kind] {
        use Kind::{D, E, K};
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

    /// The limbs slot `s` carries, over its local columns.
    pub(crate) fn slot(self, s: usize) -> SlotForm {
        let limbs = match self {
            Self::Emul => SlotForm::emul(s),
            Self::Exk => SlotForm::exk(s),
            Self::Hash => SlotForm::hash(s),
            Self::Split if s < 65 => SlotForm::k(s),
            Self::Cast => SlotForm::cast(s),
            _ => None,
        };
        limbs.unwrap_or_else(|| unreachable!("{self:?} has no slot {s}"))
    }

    /// The identities its rows satisfy, each a degree-two form over its local columns that vanishes.
    pub(crate) fn identities(self) -> Vec<BusForm> {
        let n = self.n_cols();
        let form = |linear: &[(usize, F192)], prods: Vec<(usize, usize, F192)>| {
            let mut coeffs = vec![F192::ZERO; n];
            for &(c, w) in linear {
                coeffs[c] += w;
            }
            BusForm {
                coeffs,
                prods,
                constant: F192::ZERO,
            }
        };
        // `c^2 + c`, which vanishes exactly when column `c` is Boolean.
        let boolean = |c: usize| form(&[(c, F192::ONE)], vec![(c, c, F192::ONE)]);
        match self {
            // A Boolean mux bit; what a hash row hashes is its wiring's.
            Self::Hash => vec![boolean(HashFlock::SEL)],
            // A word is its bits, each Boolean.
            Self::Split => {
                let word: Vec<(usize, F192)> = std::iter::once((0, F192::ONE))
                    .chain((0..64).map(|i| (1 + i, F192::from(F64(1 << i)))))
                    .collect();
                std::iter::once(form(&word, Vec::new()))
                    .chain((1..65).map(boolean))
                    .collect()
            }
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
    /// The limb every slot narrower than four words pads with.
    const ZERO: Coord = Coord::Const(F64::ZERO);

    /// A `K` slot: column `c`.
    const fn k(c: usize) -> Option<Self> {
        Some(Self([Coord::Col(c), Self::ZERO, Self::ZERO, Self::ZERO]))
    }

    /// An `E` slot: columns `c..c + 3`.
    const fn e(c: usize) -> Option<Self> {
        Some(Self([Coord::Col(c), Coord::Col(c + 1), Coord::Col(c + 2), Self::ZERO]))
    }

    /// A digest slot: columns `c..c + 4`.
    const fn d(c: usize) -> Option<Self> {
        Some(Self([
            Coord::Col(c),
            Coord::Col(c + 1),
            Coord::Col(c + 2),
            Coord::Col(c + 3),
        ]))
    }

    /// `EMUL`'s slots `a`, `b`, `d` and `c = a·b + d` modulo `y^3 + y + 1`.
    ///
    /// `p_i = sum_{j+l=i} a_j·b_l`, then `y^3 = y + 1` and `y^4 = y^2 + y` fold `p_3` and `p_4` down.
    fn emul(s: usize) -> Option<Self> {
        use Coord::{Col, Prod, Sum};
        let p = |i: usize| {
            (0..3)
                .filter(move |&j| i >= j && i - j < 3)
                .map(move |j| Prod(j, 3 + i - j))
        };
        let limb = |parts: &[usize], d: usize| Sum(parts.iter().flat_map(|&i| p(i)).chain([Col(d)]).collect());
        match s {
            0..3 => Self::e(3 * s),
            3 => Some(Self([
                limb(&[0, 3], 6),
                limb(&[1, 3, 4], 7),
                limb(&[2, 4], 8),
                Self::ZERO,
            ])),
            _ => None,
        }
    }

    /// `EXK`'s slots `a`, `k`, `d` and `c = a·k + d`, limb by limb.
    fn exk(s: usize) -> Option<Self> {
        use Coord::{Col, Prod, Sum};
        match s {
            0 => Self::e(0),
            1 => Self::k(3),
            2 => Self::e(4),
            3 => Some(Self(std::array::from_fn(|i| {
                if i < 3 {
                    Sum(vec![Prod(i, 3), Col(4 + i)])
                } else {
                    Self::ZERO
                }
            }))),
            _ => None,
        }
    }

    /// `HASH`'s slots, over its ports and its mux bit.
    fn hash(s: usize) -> Option<Self> {
        use Coord::{Col, Prod, Sum};
        let (t, f, h, m, o, sel) = (
            HashFlock::T,
            HashFlock::F,
            HashFlock::H,
            HashFlock::M,
            HashFlock::O,
            HashFlock::SEL,
        );
        match s {
            0 => Self::d(h),
            1 => Some(Self([Col(t), Col(f), Self::ZERO, Self::ZERO])),
            // The Merkle mux: the message's left half at `b = 0`, its right half at `b = 1`.
            2 => Some(Self(std::array::from_fn(|i| {
                Sum(vec![Col(m + i), Prod(sel, m + i), Prod(sel, m + 4 + i)])
            }))),
            3 => Self::k(sel),
            4 => Self::e(m + 4),
            5 => Self::k(m + 7),
            6 => Self::d(o),
            7 => Self::e(o),
            8..16 => Self::k(m + s - 8),
            _ => None,
        }
    }

    /// `CAST`'s slots over its four words.
    const fn cast(s: usize) -> Option<Self> {
        use Coord::Col;
        match s {
            0 => Self::d(0),
            1 => Self::e(0),
            2 => Some(Self([Col(0), Col(1), Self::ZERO, Self::ZERO])),
            3 => Some(Self([Col(2), Col(3), Self::ZERO, Self::ZERO])),
            4..8 => Self::k(s - 4),
            _ => None,
        }
    }

    /// Its limbs over the global columns, its table's first at `base`.
    pub(crate) fn offset(self, base: usize) -> [Coord; 4] {
        self.0.map(|c| c.offset(base))
    }

    /// The first limb that is column `c` alone.
    fn limb_of(&self, c: usize) -> Option<usize> {
        self.0.iter().position(|l| matches!(l, Coord::Col(x) if *x == c))
    }
}

impl HashFlock {
    /// How many ports the hash table reads, at the witness's words `0..18`.
    pub(crate) const N_PORTS: usize = 18;
    const T: usize = 0;
    const F: usize = 1;
    const H: usize = 2;
    const M: usize = 6;
    const O: usize = 14;
    /// The hash table's mux bit, its one committed column, after its ports.
    const SEL: usize = Self::N_PORTS;

    /// The packed witness index of the BLAKE2s class circuit, which proves every hash row.
    fn index() -> usize {
        let t = tables::table_of(crate::rv::Class::Hash).expect("the HASH class has a table");
        class_flock::flock_index(t, Part::Class)
    }

    /// The BLAKE2s compression circuit.
    pub(crate) fn circuit() -> &'static FlockCircuit {
        class_flock::circuit(Self::index())
    }

    /// `log2` of a hash row's packed words: the stride between consecutive rows' same-port words.
    pub(crate) fn stride_log() -> usize {
        class_flock::stride_log(&tables::HASH, Part::Class)
    }

    /// `log2` of the hash table's height for `rows` rows, at least flock's floor.
    fn height_log(rows: usize) -> usize {
        flock::reduction::min_n_blocks_log(rows.max(1))
            .max(class_flock::MIN_CUBE_LOG.saturating_sub(tables::HASH.k_log))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tables::Word;
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
                    Kind::K => 1,
                    Kind::E => 3,
                    Kind::D => 4,
                };
                assert!(t.slot(s).0[used..].iter().all(zero), "{t:?} slot {s}");
            }
            assert_eq!(t.committed_sources().len(), t.n_cols() - t.n_ports());
        }
    }

    #[test]
    fn the_hash_ports_are_the_precompile_ports() {
        let ports = tables::HASH.ports;
        assert_eq!(ports.len(), HashFlock::N_PORTS);
        assert_eq!((ports[HashFlock::T], ports[HashFlock::F]), (Word::V2, Word::Flags));
        assert!((0..4).all(|i| ports[HashFlock::H + i] == Word::Cell(i as u8)));
        assert!((0..8).all(|i| ports[HashFlock::M + i] == Word::Cell(8 + i as u8)));
        assert!((0..4).all(|i| ports[HashFlock::O + i] == Word::CellNew(4 + i as u8)));
    }
}
