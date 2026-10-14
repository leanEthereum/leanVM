//! The recursion machine's circuit: a fixed list of rows, one table per operation, wired by copy cycles.
//!
//! A wire holds a `K` word, an `E` element (three limbs) or a digest (four words).
//! Every row names one wire per slot, and every slot carries its wire on the bus.
//! The slots naming one wire form a cycle on the bus, which balances only if they all carry one value.
//! A wire in one slot is a cycle of one: it constrains nothing, which is what a value the prover sends is.
//!
//! The rows depend on the shapes of what is verified, never on values.
//! So the verifier rebuilds the same circuit with no proof, its values computed from zeros.
//!
//! The builder records the rows and an honest assignment to their wires:
//!
//! - arithmetic over `E` is the `EMUL` and `EXK` rows, with the units and repeated rows folded away;
//! - a word and its bits are a `SPLIT` row, and the views of four words a `CAST` row;
//! - one BLAKE2s compression is a `HASH` row: a transcript step, a Merkle node or a block of a long message.

use super::table::{PerRecTable, Table};
use crate::cpu::Assumption;
use crate::rv::{Hash, InstructionClass};
use fiat_shamir::arith::Arith;
use primitives::field::{F64, F192};
use primitives::hash::ChainingValue;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use thiserror::Error;

/// A wire's value as four `K` words: a `K` wire uses the first, an `E` wire the first three.
pub type Limbs = [u64; 4];

/// The parameter IV as four words.
pub const PARAM_IV: Limbs = words(primitives::hash::PARAM_IV);

/// The IV of the hash that folds a run's assumptions into its output, as four words.
pub(crate) const ASSUMING_IV: Limbs = words(primitives::hash::personal_iv(&Assumption::PERSONALIZATION));

/// What a wire holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WireKind {
    /// One `K` word.
    K,
    /// One `E` element, three `K` limbs.
    E,
    /// A digest, four `K` words.
    D,
}

/// A `K` wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Kw(pub(crate) u32);

/// An `E` wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ew(pub(crate) u32);

/// A digest wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Dw(pub(crate) u32);

/// A wire of any kind, known by the number the builder gave it.
pub trait AnyWire: Copy {
    /// The wire's number.
    fn id(self) -> u32;
}

/// Where a public row's value comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PubSource {
    /// A constant of the circuit.
    Const(Limbs),
    /// Word `i` of the statement.
    Statement(usize),
}

/// Every table's rows, row-major, one number per slot: a wire, or the class of wires it is held equal to.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TableSlots(PerRecTable<Vec<u32>>);

/// The fixed part of a circuit: its rows, and the wire class each slot names.
///
/// The statement's public rows come first, in statement order, then the constants'.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Circuit {
    /// Each slot's wire class.
    pub(crate) classes: TableSlots,
    /// Per public row, where its value comes from.
    pub(crate) pubs: Vec<PubSource>,
    /// How many words the statement has.
    pub(crate) statement_len: usize,
    /// Each table's least height, as a base-two logarithm.
    pub(crate) floor: PerRecTable<usize>,
}

/// What the prover adds to a circuit: every wire's value and every hash row's inputs.
#[derive(Clone, Debug)]
pub struct Assignment {
    /// Each slot's own wire, whose value the slot carries.
    pub(crate) wires: TableSlots,
    /// Each wire's value.
    pub(crate) values: Vec<Limbs>,
    /// Each hash row's compression.
    pub(crate) hash: Vec<Compression>,
    /// The statement's words.
    pub(crate) statement: Vec<Limbs>,
}

/// A finished circuit, the values of the run that built it, and the checks that failed on them.
#[derive(Clone, Debug)]
pub struct Finished {
    /// The circuit.
    pub circuit: Circuit,
    /// The run's values.
    pub assignment: Assignment,
    /// The first few checks that failed, each under its scope's names.
    pub failures: Vec<Unsatisfied>,
}

/// A check of a circuit's rows that fails on the prover's values.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[error("{}: {check}", scope.join(" / "))]
pub struct Unsatisfied {
    /// The names the check ran under, outermost first.
    scope: Vec<String>,
    /// What the check asserts.
    check: &'static str,
}

/// One BLAKE2s compression, its inputs in the compression circuit's port order: `t`, `f`, `h0..h3`, `m0..m7`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Compression([u64; 14]);

/// Builds circuit rows and records an honest assignment to their wires.
///
/// Arithmetic identities involving constant zero or one can avoid emitting rows.
/// An arithmetic row with the input wires of an earlier one emits no row either: its output is the earlier row's.
/// Folding depends on circuit constants and wire numbers, never on the values of unconstrained wires.
#[derive(Debug, Default)]
pub struct Builder {
    /// Each wire's value.
    values: Vec<Limbs>,
    /// Each wire's kind.
    kinds: Vec<WireKind>,
    /// Parent wire in each equality class, with roots pointing to themselves.
    parent: Vec<u32>,
    /// Wire numbers for every table row and slot.
    rows: TableSlots,
    /// Sources of public row values, in insertion order.
    pubs: Vec<PubSource>,
    /// Deduplicated constant wires, keyed by kind and padded value.
    consts: HashMap<(WireKind, Limbs), u32>,
    /// Cached arithmetic identities used to fold operations.
    units: Units,
    /// Each `EMUL` and `EXK` row's output by its key, `EMUL`'s two factors in order.
    arith: HashMap<RowKey, u32, BuildHasherDefault<RowHasher>>,
    /// Each hash row's compression.
    hash: Vec<Compression>,
    /// The statement's words.
    statement: Vec<Limbs>,
    /// The names the checks run under, outermost first.
    scope: Vec<String>,
    /// Failed checks collected with their enclosing scope names, the first few only.
    failures: Vec<Unsatisfied>,
}

/// The constants arithmetic folds away, once created.
#[derive(Clone, Copy, Debug, Default)]
struct Units {
    /// Cached wire for the extension-field constant zero.
    e_zero: Option<u32>,
    /// Cached wire for the extension-field constant one.
    e_one: Option<u32>,
    /// Cached wire for the base-field constant zero.
    k_zero: Option<u32>,
    /// Cached wire for the base-field constant one.
    k_one: Option<u32>,
}

/// An arithmetic row's table and input wires, as one key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct RowKey(u128);

/// Hashes a row key: wire numbers the builder made, never adversarial, so two rounds of a 64-bit finalizer suffice.
#[derive(Default)]
struct RowHasher(u64);

/// Input wires of one hash row, before its output and individual message-word slots.
#[derive(Clone, Copy)]
struct HashHead {
    /// Input chaining value.
    h: Dw,
    /// Byte counter and finalization flag, followed by two zero words.
    tf: Dw,
    /// Four-word message half selected by the Merkle path bit.
    mux: Dw,
    /// Selects the left message half when zero and the right half when one.
    bit: Kw,
    /// Message words four through six, packed as an extension-field element.
    x: Ew,
    /// Final message word.
    ds: Kw,
}

/// The slot of a cast row's digest.
const DIGEST: usize = 0;

/// The slot of a cast row's element of its first three words.
const ELEMENT: usize = 1;

/// The first slot of a cast row's two halves.
const HALVES: usize = 2;

/// The first slot of a cast row's four words.
const WORDS: usize = 4;

impl AnyWire for Kw {
    fn id(self) -> u32 {
        self.0
    }
}

impl AnyWire for Ew {
    fn id(self) -> u32 {
        self.0
    }
}

impl AnyWire for Dw {
    fn id(self) -> u32 {
        self.0
    }
}

impl TableSlots {
    /// Append a row to a table.
    fn push(&mut self, table: Table, slots: &[u32]) {
        debug_assert_eq!(slots.len(), table.n_slots());
        self.0[table].extend_from_slice(slots);
    }

    /// Put a one-slot table's rows in the given order of their old indices.
    fn reorder(&mut self, table: Table, order: &[usize]) {
        debug_assert_eq!(table.n_slots(), 1);
        let rows = &self.0[table];
        self.0[table] = order.iter().map(|&i| rows[i]).collect();
    }

    /// A table's slots, row-major.
    pub(crate) fn of(&self, table: Table) -> &[u32] {
        &self.0[table]
    }

    /// How many rows a table has.
    pub(crate) fn len(&self, table: Table) -> usize {
        self.of(table).len() / table.n_slots()
    }

    /// Every table's slots, each number replaced through `f`.
    pub(crate) fn map(&self, mut f: impl FnMut(u32) -> u32) -> Self {
        Self(PerRecTable::from_fn(|t| self.0[t].iter().map(|&w| f(w)).collect()))
    }
}

impl Circuit {
    /// Each table's number of rows.
    pub fn row_counts(&self) -> PerRecTable<usize> {
        PerRecTable::from_fn(|t| self.classes.len(t))
    }

    /// Each table's base-two logarithm of rows: the least power of two holding its rows, and at least its floor.
    pub fn heights(&self) -> PerRecTable<usize> {
        let counts = self.row_counts();
        PerRecTable::from_fn(|t: Table| t.height_log(counts[t]).max(self.floor[t]))
    }

    /// The same circuit with each table at least the given height.
    #[must_use]
    pub(crate) fn with_floor(self, floor: PerRecTable<usize>) -> Self {
        Self { floor, ..self }
    }

    /// How many wire classes the slots name.
    pub(crate) fn n_classes(&self) -> usize {
        (Table::ALL.iter())
            .flat_map(|&t| self.classes.of(t))
            .max()
            .map_or(0, |&c| c as usize + 1)
    }
}

impl Assignment {
    /// The statement's words.
    pub fn statement(&self) -> &[Limbs] {
        &self.statement
    }

    /// The value slot `s` of a table's row `z` carries.
    pub(crate) fn value(&self, table: Table, z: usize, s: usize) -> Limbs {
        self.values[self.wires.of(table)[z * table.n_slots() + s] as usize]
    }
}

impl Unsatisfied {
    /// The names the check ran under, outermost first.
    #[must_use]
    pub fn scope(&self) -> &[String] {
        &self.scope
    }

    /// What the check asserts.
    #[must_use]
    pub const fn check(&self) -> &'static str {
        self.check
    }
}

impl Compression {
    /// The inputs of a padding row: all zero.
    pub(crate) const PADDING: Self = Self([0; 14]);

    /// The compression of the message `m` into `h` at byte counter `t`, final if `last`.
    pub const fn new(h: Limbs, m: [u64; 8], t: u64, last: bool) -> Self {
        Self::with_flags(h, m, t, if last { Hash::FINAL } else { 0 })
    }

    /// The compression of the message `m` into `h` at byte counter `t`, with finalization word `f`.
    pub const fn with_flags(h: Limbs, m: [u64; 8], t: u64, f: u64) -> Self {
        Self([
            t, f, h[0], h[1], h[2], h[3], m[0], m[1], m[2], m[3], m[4], m[5], m[6], m[7],
        ])
    }

    /// A one-block message from the parameter IV: its only block, so final.
    pub const fn single(m: [u64; 8]) -> Self {
        Self::new(PARAM_IV, m, 64, true)
    }

    /// The inputs, in the compression circuit's port order.
    pub const fn inputs(&self) -> &[u64; 14] {
        &self.0
    }

    /// The output chaining value, as the precompile computes it.
    pub fn output(&self) -> Limbs {
        let i = &self.0;
        let block: [u64; 16] = std::array::from_fn(|w| match w {
            0..4 => i[2 + w],
            4..8 => 0,
            _ => i[6 + w - 8],
        });
        Hash {
            flags: i[1],
            t: i[0],
            block,
        }
        .eval()
    }
}

/// The chaining value after `n` zero blocks from the parameter IV, as four words.
pub fn zero_prefix(n: usize) -> Limbs {
    words(ChainingValue::zero_prefix(n).state())
}

/// The BLAKE2s hash of the little-endian bytes of `words`, eight words a block.
///
/// The last block is zero padded and its counter is the message's length in bytes.
/// So the length is hashed: appending zero words changes the digest.
pub fn chain(words: &[u64]) -> Limbs {
    let n_blocks = words.len().div_ceil(8).max(1);
    let bytes = 8 * words.len() as u64;
    (0..n_blocks).fold(PARAM_IV, |h, j| {
        // The final block retains the message's words and zero-pads its unused slots.
        let m = std::array::from_fn(|k| words.get(8 * j + k).copied().unwrap_or(0));
        Compression::new(h, m, (64 * (j as u64 + 1)).min(bytes), j + 1 == n_blocks).output()
    })
}

/// Four words from eight little-endian 32-bit halves.
const fn words(h: [u32; 8]) -> Limbs {
    let mut out = [0; 4];
    let mut i = 0;
    while i < 4 {
        out[i] = h[2 * i] as u64 | (h[2 * i + 1] as u64) << 32;
        i += 1;
    }
    out
}

impl RowKey {
    /// The key of a row of `table` over the input wires `inputs`.
    fn new(table: Table, inputs: [u32; 3]) -> Self {
        Self((table as u128) << 96 | u128::from(inputs[0]) << 64 | u128::from(inputs[1]) << 32 | u128::from(inputs[2]))
    }
}

impl Hasher for RowHasher {
    fn write(&mut self, _: &[u8]) {
        unreachable!("a row key is one u128");
    }

    fn write_u128(&mut self, key: u128) {
        const fn mix(mut x: u64) -> u64 {
            x ^= x >> 33;
            x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
            x ^= x >> 33;
            x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
            x ^ (x >> 33)
        }
        self.0 = mix(mix(key as u64) ^ (key >> 64) as u64);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

impl Builder {
    /// How many failed checks are recorded by name: a forged proof can fail one per row.
    const RECORDED_FAILURES: usize = 64;

    /// An empty circuit.
    pub fn new() -> Self {
        Self::default()
    }

    /// Run `f` under a name, which an equality that fails reports.
    pub fn scope<T>(&mut self, name: impl Into<String>, f: impl FnOnce(&mut Self) -> T) -> T {
        self.enter(name);
        let out = f(self);
        self.leave();
        out
    }

    /// Enter a named scope, which the next leave closes.
    pub(crate) fn enter(&mut self, name: impl Into<String>) {
        self.scope.push(name.into());
    }

    /// Close the innermost scope.
    pub(crate) fn leave(&mut self) {
        self.scope.pop();
    }

    /// Record a check that failed on the values and that no equality expresses.
    pub fn fail(&mut self, check: &'static str) {
        if self.failures.len() < Self::RECORDED_FAILURES {
            self.failures.push(Unsatisfied {
                scope: self.scope.clone(),
                check,
            });
        }
    }

    /// The circuit, its values, and the checks that failed on them.
    ///
    /// A wire class is numbered by its first slot, so a circuit is the same however it was built.
    pub fn finish(mut self) -> Finished {
        let (wires, pubs) = self.statement_first();
        let mut number: Vec<Option<u32>> = vec![None; self.values.len()];
        let mut n_classes = 0;
        let classes = wires.map(|w| {
            let root = self.find(w) as usize;
            *number[root].get_or_insert_with(|| {
                n_classes += 1;
                n_classes - 1
            })
        });
        let circuit = Circuit {
            classes,
            pubs,
            statement_len: self.statement.len(),
            floor: PerRecTable::default(),
        };
        let assignment = Assignment {
            wires,
            values: self.values,
            hash: self.hash,
            statement: self.statement,
        };
        Finished {
            circuit,
            assignment,
            failures: self.failures,
        }
    }

    /// The rows and the public sources with the statement's public rows first, in statement order.
    ///
    /// They are then one aligned stretch of the public table.
    fn statement_first(&mut self) -> (TableSlots, Vec<PubSource>) {
        let mut order: Vec<usize> = (0..self.pubs.len()).collect();
        order.sort_by_key(|&i| match self.pubs[i] {
            PubSource::Statement(j) => (0, j),
            PubSource::Const(_) => (1, i),
        });
        let mut rows = std::mem::take(&mut self.rows);
        rows.reorder(Table::Pub, &order);
        let pubs = order.iter().map(|&i| self.pubs[i]).collect();
        (rows, pubs)
    }

    /// A new wire of a kind, holding a value.
    fn wire(&mut self, kind: WireKind, value: Limbs) -> u32 {
        let id = u32::try_from(self.values.len()).expect("fewer than 2^32 wires");
        self.values.push(value);
        self.kinds.push(kind);
        self.parent.push(id);
        id
    }

    /// The root of `x`'s class, halving the path on the way.
    fn find(&mut self, mut x: u32) -> u32 {
        while self.parent[x as usize] != x {
            let p = self.parent[x as usize];
            self.parent[x as usize] = self.parent[p as usize];
            x = p;
        }
        x
    }

    /// Merge the classes of two wires, recording a failure if their values differ.
    fn union(&mut self, a: u32, b: u32) {
        if self.values[a as usize] != self.values[b as usize] {
            self.fail("unequal wires");
        }
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[rb as usize] = ra;
        }
    }

    /// Append a row to a table, its slots the given wires.
    fn row(&mut self, table: Table, slots: &[u32]) {
        debug_assert!(
            table == Table::Pub
                || (slots.iter().zip(table.slot_kinds())).all(|(&w, &kind)| self.kinds[w as usize] == kind),
            "{table:?} slot kind"
        );
        self.rows.push(table, slots);
    }

    /// The value of an `E` wire.
    pub fn e(&self, w: Ew) -> F192 {
        let [c0, c1, c2, _] = self.values[w.0 as usize];
        F192::new(c0, c1, c2)
    }

    /// The value of a `K` wire.
    pub fn k(&self, w: Kw) -> u64 {
        self.values[w.0 as usize][0]
    }

    /// The value of a digest wire.
    pub fn d(&self, w: Dw) -> Limbs {
        self.values[w.0 as usize]
    }

    /// An extension-field wire constrained only by the slots that use it.
    ///
    /// Its three coefficients occupy the first three words, with the fourth word zero.
    pub fn free_e(&mut self, value: F192) -> Ew {
        Ew(self.wire(WireKind::E, [value.c0, value.c1, value.c2, 0]))
    }

    /// A free `K` value.
    pub fn free_k(&mut self, value: u64) -> Kw {
        Kw(self.wire(WireKind::K, [value, 0, 0, 0]))
    }

    /// A free digest.
    pub fn free_d(&mut self, value: Limbs) -> Dw {
        Dw(self.wire(WireKind::D, value))
    }

    /// Hold `a` and `b` equal.
    pub fn eq<W: AnyWire>(&mut self, a: W, b: W) {
        self.union(a.id(), b.id());
    }

    /// Hold `a` to a constant.
    pub fn eq_e_const(&mut self, a: Ew, value: F192) {
        let c = self.e_const(value);
        self.eq(a, c);
    }

    /// Hold `a` to a constant.
    pub fn eq_k_const(&mut self, a: Kw, value: u64) {
        let c = self.k_const(value);
        self.eq(a, c);
    }

    /// The constant wire of a kind and value, a public row the first time it is asked for.
    fn constant(&mut self, kind: WireKind, value: Limbs) -> u32 {
        if let Some(&w) = self.consts.get(&(kind, value)) {
            return w;
        }
        let w = self.wire(kind, value);
        self.pubs.push(PubSource::Const(value));
        self.row(Table::Pub, &[w]);
        self.consts.insert((kind, value), w);
        let unit = match (kind, value) {
            (WireKind::E, [0, 0, 0, 0]) => &mut self.units.e_zero,
            (WireKind::E, [1, 0, 0, 0]) => &mut self.units.e_one,
            (WireKind::K, [0, 0, 0, 0]) => &mut self.units.k_zero,
            (WireKind::K, [1, 0, 0, 0]) => &mut self.units.k_one,
            _ => return w,
        };
        *unit = Some(w);
        w
    }

    /// An extension-field wire bound to a public constant.
    ///
    /// Its three coefficients occupy the first three words, with the fourth word zero.
    pub fn e_const(&mut self, value: F192) -> Ew {
        Ew(self.constant(WireKind::E, [value.c0, value.c1, value.c2, 0]))
    }

    /// The constant `K` word `value`.
    pub fn k_const(&mut self, value: u64) -> Kw {
        Kw(self.constant(WireKind::K, [value, 0, 0, 0]))
    }

    /// The constant digest `value`.
    pub fn d_const(&mut self, value: Limbs) -> Dw {
        Dw(self.constant(WireKind::D, value))
    }

    /// The constant zero of `K`.
    fn k_zero(&mut self) -> Kw {
        self.units.k_zero.map_or_else(|| self.k_const(0), Kw)
    }

    /// Make `w` a word of the statement, which the verifier is handed and the bus holds `w` to.
    ///
    /// Returns the word's index in the statement.
    pub fn expose<W: AnyWire>(&mut self, w: W) -> usize {
        let i = self.statement.len();
        self.statement.push(self.values[w.id() as usize]);
        self.pubs.push(PubSource::Statement(i));
        self.row(Table::Pub, &[w.id()]);
        i
    }

    /// The `EMUL` row `c = a·b + d`, or the earlier row with the same inputs.
    fn emul(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        let key = RowKey::new(Table::Emul, self.emul_key(a, b, d));
        if let Some(&c) = self.arith.get(&key) {
            return Ew(c);
        }
        let c = self.free_e(self.e(a) * self.e(b) + self.e(d));
        self.row(Table::Emul, &[a.0, b.0, d.0, c.0]);
        self.arith.insert(key, c.0);
        c
    }

    /// The inputs of `a·b + d` in one order for every order giving the same row: the factors in order, and for `1·x + d` the terms.
    fn emul_key(&self, a: Ew, b: Ew, d: Ew) -> [u32; 3] {
        let one = self.units.e_one;
        if one == Some(a.0) || one == Some(b.0) {
            let x = if one == Some(a.0) { b.0 } else { a.0 };
            [one.expect("the unit"), x.min(d.0), x.max(d.0)]
        } else {
            [a.0.min(b.0), a.0.max(b.0), d.0]
        }
    }

    /// `a·k + d`, `k` in `K`.
    pub fn mul_k_add(&mut self, a: Ew, k: Kw, d: Ew) -> Ew {
        let u = self.units;
        if u.e_zero == Some(a.0) || u.k_zero == Some(k.0) {
            return d;
        }
        if u.k_one == Some(k.0) {
            return self.add(a, d);
        }
        let key = RowKey::new(Table::Exk, [a.0, k.0, d.0]);
        if let Some(&c) = self.arith.get(&key) {
            return Ew(c);
        }
        let c = self.free_e(self.e(a).mul_base(F64(self.k(k))) + self.e(d));
        self.row(Table::Exk, &[a.0, k.0, d.0, c.0]);
        self.arith.insert(key, c.0);
        c
    }

    /// The `SPLIT` row of a word and its bits.
    fn split_row(&mut self, word: Kw, bits: &[Kw; 64]) {
        let slots: [u32; 65] = std::array::from_fn(|i| if i == 0 { word.0 } else { bits[i - 1].0 });
        self.row(Table::Split, &slots);
    }

    /// The 64 bits of `w`, lowest first, each a `K` wire holding 0 or 1.
    pub fn split(&mut self, w: Kw) -> [Kw; 64] {
        let v = self.k(w);
        let bits: [Kw; 64] = std::array::from_fn(|i| self.free_k((v >> i) & 1));
        self.split_row(w, &bits);
        bits
    }

    /// The word whose bits are `bits`, lowest first, the rest zero.
    ///
    /// # Panics
    ///
    /// Panics if there are more than 64 bits.
    pub fn pack(&mut self, bits: &[Kw]) -> Kw {
        assert!(bits.len() <= 64, "a word has 64 bits");
        let zero = self.k_zero();
        let all: [Kw; 64] = std::array::from_fn(|i| bits.get(i).copied().unwrap_or(zero));
        let v = (all.iter().enumerate()).fold(0u64, |acc, (i, &b)| acc | (self.k(b) & 1) << i);
        let w = self.free_k(v);
        self.split_row(w, &all);
        w
    }

    /// A cast row over the words `v`: the given `(slot, wire)` pairs, fresh wires in the other slots.
    fn cast_row(&mut self, given: &[(usize, u32)], v: Limbs) -> [u32; 8] {
        let values: [Limbs; 8] = [
            v,
            [v[0], v[1], v[2], 0],
            [v[0], v[1], 0, 0],
            [v[2], v[3], 0, 0],
            [v[0], 0, 0, 0],
            [v[1], 0, 0, 0],
            [v[2], 0, 0, 0],
            [v[3], 0, 0, 0],
        ];
        let kinds = Table::Cast.slot_kinds();
        let wires: [u32; 8] = std::array::from_fn(|s| {
            (given.iter().find(|&&(at, _)| at == s)).map_or_else(|| self.wire(kinds[s], values[s]), |&(_, w)| w)
        });
        if given.iter().any(|&(s, w)| self.values[w as usize] != values[s]) {
            self.fail("cast");
        }
        self.row(Table::Cast, &wires);
        wires
    }

    /// The limbs of `e`.
    pub fn e_to_k(&mut self, e: Ew) -> [Kw; 3] {
        let v = self.e(e);
        let w = self.cast_row(&[(ELEMENT, e.0)], [v.c0, v.c1, v.c2, 0]);
        std::array::from_fn(|i| Kw(w[WORDS + i]))
    }

    /// The element with limbs `k`.
    pub fn k_to_e(&mut self, k: [Kw; 3]) -> Ew {
        let v = [self.k(k[0]), self.k(k[1]), self.k(k[2]), 0];
        let given: [(usize, u32); 3] = std::array::from_fn(|i| (WORDS + i, k[i].0));
        Ew(self.cast_row(&given, v)[ELEMENT])
    }

    /// `k` in `E`.
    pub fn k_to_e1(&mut self, k: Kw) -> Ew {
        let zero = self.k_zero();
        self.k_to_e([k, zero, zero])
    }

    /// A digest's words.
    pub fn d_to_k(&mut self, d: Dw) -> [Kw; 4] {
        let v = self.d(d);
        let w = self.cast_row(&[(DIGEST, d.0)], v);
        std::array::from_fn(|i| Kw(w[WORDS + i]))
    }

    /// A digest's first three words as an element, and its last word.
    pub fn d_to_e_and_k(&mut self, d: Dw) -> (Ew, Kw) {
        let v = self.d(d);
        let w = self.cast_row(&[(DIGEST, d.0)], v);
        (Ew(w[ELEMENT]), Kw(w[WORDS + 3]))
    }

    /// A digest's two 128-bit halves, each with a zero top limb.
    pub fn d_to_halves(&mut self, d: Dw) -> [Ew; 2] {
        let v = self.d(d);
        let w = self.cast_row(&[(DIGEST, d.0)], v);
        [Ew(w[HALVES]), Ew(w[HALVES + 1])]
    }

    /// The digest whose two 128-bit halves are `lo` and `hi`, each with a zero top limb.
    pub fn halves_to_d(&mut self, lo: Ew, hi: Ew) -> Dw {
        let (l, h) = (self.e(lo), self.e(hi));
        if l.c2 != 0 || h.c2 != 0 {
            self.fail("a digest half has a top limb");
        }
        let w = self.cast_row(&[(HALVES, lo.0), (HALVES + 1, hi.0)], [l.c0, l.c1, h.c0, h.c1]);
        Dw(w[DIGEST])
    }

    /// The digest with words `k`.
    pub fn k_to_d(&mut self, k: [Kw; 4]) -> Dw {
        let v = k.map(|w| self.k(w));
        let given: [(usize, u32); 4] = std::array::from_fn(|i| (WORDS + i, k[i].0));
        Dw(self.cast_row(&given, v)[DIGEST])
    }

    /// Ordinary one-block BLAKE2s on `acc || x || ds`, from the parameter IV.
    ///
    /// Returns the digest and its first three words.
    pub fn compress(&mut self, acc: Dw, x: Ew, ds: Kw) -> (Dw, Ew) {
        let bit = self.k_zero();
        let (a, xv, dv) = (self.d(acc), self.e(x), self.k(ds));
        let m = [a[0], a[1], a[2], a[3], xv.c0, xv.c1, xv.c2, dv];
        self.single_block(acc, bit, x, ds, m)
    }

    /// One Merkle node: the parent of `acc` and `sibling`, `acc` on the right if `bit` is set.
    pub fn node(&mut self, acc: Dw, bit: Kw, sibling: Limbs) -> Dw {
        let a = self.d(acc);
        let (left, right) = if self.k(bit) == 1 { (sibling, a) } else { (a, sibling) };
        let m = [
            left[0], left[1], left[2], left[3], right[0], right[1], right[2], right[3],
        ];
        let x = self.free_e(F192::new(m[4], m[5], m[6]));
        let ds = self.free_k(m[7]);
        self.single_block(acc, bit, x, ds, m).0
    }

    /// One Merkle node over two wired children: the parent of `left` and `right`.
    pub fn parent(&mut self, left: Dw, right: Dw) -> Dw {
        let (l, rv) = (self.d(left), self.d(right));
        let m = [l[0], l[1], l[2], l[3], rv[0], rv[1], rv[2], rv[3]];
        let (x, ds) = self.d_to_e_and_k(right);
        let bit = self.k_zero();
        self.single_block(left, bit, x, ds, m).0
    }

    /// One block of a long message: `m` absorbed into `h` at byte counter `t`, final if `last`.
    pub fn leaf_block(&mut self, h: Dw, m: [Kw; 8], t: u64, last: bool) -> Dw {
        let tf = self.d_const([t, if last { Hash::FINAL } else { 0 }, 0, 0]);
        self.block(h, m, tf)
    }

    /// One block of a long message whose byte counter and finalization word are wires: `tf` is `[t, f, 0, 0]`.
    pub fn block(&mut self, h: Dw, m: [Kw; 8], tf: Dw) -> Dw {
        let [t, f, ..] = self.d(tf);
        let compression = Compression::with_flags(self.d(h), m.map(|w| self.k(w)), t, f);
        let v = &compression.inputs()[6..];
        let head = HashHead {
            h,
            tf,
            mux: self.free_d([v[0], v[1], v[2], v[3]]),
            bit: self.free_k(0),
            x: self.free_e(F192::new(v[4], v[5], v[6])),
            ds: self.free_k(v[7]),
        };
        self.hash_row(head, m.map(|w| w.0), compression).0
    }

    /// The hash of `words` in rows, as the native chain computes it.
    pub fn chain(&mut self, words: &[Kw]) -> Dw {
        self.chain_from(PARAM_IV, words)
    }

    /// The hash of `words` from the initial chaining value `iv`: BLAKE2s-256 of their bytes under the parameter block
    /// `iv` folds in.
    pub fn chain_from(&mut self, iv: Limbs, words: &[Kw]) -> Dw {
        let n_blocks = words.len().div_ceil(8).max(1);
        let zero = self.k_zero();
        let bytes = 8 * words.len() as u64;
        let mut h = self.d_const(iv);
        for j in 0..n_blocks {
            let m: [Kw; 8] = std::array::from_fn(|i| words.get(8 * j + i).copied().unwrap_or(zero));
            h = self.leaf_block(h, m, (64 * (j as u64 + 1)).min(bytes), j + 1 == n_blocks);
        }
        h
    }

    /// A one-block compression from the parameter IV, its message words free but for the mux, `x` and `ds`.
    fn single_block(&mut self, mux: Dw, bit: Kw, x: Ew, ds: Kw, m: [u64; 8]) -> (Dw, Ew) {
        let head = HashHead {
            h: self.d_const(PARAM_IV),
            tf: self.d_const([64, Hash::FINAL, 0, 0]),
            mux,
            bit,
            x,
            ds,
        };
        let words = m.map(|v| self.free_k(v).0);
        self.hash_row(head, words, Compression::single(m))
    }

    /// A hash row: its head's slots, then its output and challenge, then its message's words.
    fn hash_row(&mut self, head: HashHead, words: [u32; 8], compression: Compression) -> (Dw, Ew) {
        let out = compression.output();
        let o = self.free_d(out);
        let ch = self.free_e(F192::new(out[0], out[1], out[2]));
        let HashHead { h, tf, mux, bit, x, ds } = head;
        let mut slots = [0u32; Table::Hash.n_slots()];
        slots[..8].copy_from_slice(&[h.0, tf.0, mux.0, bit.0, x.0, ds.0, o.0, ch.0]);
        slots[8..].copy_from_slice(&words);
        self.row(Table::Hash, &slots);
        self.hash.push(compression);
        (o, ch)
    }
}

impl Arith for Builder {
    type E = Ew;

    fn constant(&mut self, c: F192) -> Ew {
        self.e_const(c)
    }

    fn mul_add(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        let u = self.units;
        if u.e_zero.is_some_and(|z| z == a.0 || z == b.0) {
            d
        } else if u.e_one == Some(b.0) {
            self.add(a, d)
        } else if u.e_one == Some(a.0) {
            self.add(b, d)
        } else {
            self.emul(a, b, d)
        }
    }

    fn add(&mut self, a: Ew, d: Ew) -> Ew {
        let zero = self.units.e_zero;
        if zero == Some(d.0) {
            a
        } else if zero == Some(a.0) {
            d
        } else {
            let one = self.one();
            self.emul(a, one, d)
        }
    }

    /// Through the cheaper table when `c` is in `K`.
    fn mul_const_add(&mut self, a: Ew, c: F192, d: Ew) -> Ew {
        if c.c1 == 0 && c.c2 == 0 {
            let k = self.k_const(c.c0);
            return self.mul_k_add(a, k, d);
        }
        let c = self.e_const(c);
        self.mul_add(a, c, d)
    }

    /// A hint the prover supplies, held to `a·(1/a) = 1`.
    fn inv(&mut self, a: Ew) -> Ew {
        let v = self.e(a);
        let i = self.free_e(v.inv());
        let p = self.mul(a, i);
        self.eq_e_const(p, F192::ONE);
        i
    }

    /// `v + c2 (Y + Y^2) + c1 Y^2` for `v = c0 + c1 Y + c2 Y^2`.
    fn frobenius2(&mut self, a: Ew) -> Ew {
        let [_, c1, c2] = self.e_to_k(a);
        let y_y2 = self.e_const(F192::new(0, 1, 1));
        let y2 = self.e_const(F192::new(0, 0, 1));
        let u = self.mul_k_add(y_y2, c2, a);
        self.mul_k_add(y2, c1, u)
    }

    fn zero(&mut self) -> Ew {
        self.units.e_zero.map_or_else(|| self.e_const(F192::ZERO), Ew)
    }

    fn one(&mut self) -> Ew {
        self.units.e_one.map_or_else(|| self.e_const(F192::ONE), Ew)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn units_emit_no_row() {
        let mut b = Builder::new();
        let x = b.free_e(F192::new(3, 5, 7));
        let k = b.free_k(9);
        let (zero, one) = (b.zero(), b.one());
        let (k0, k1) = (b.k_const(0), b.k_const(1));
        assert_eq!(b.mul(x, one), x);
        assert_eq!(b.mul(one, x), x);
        assert_eq!(b.add(x, zero), x);
        assert_eq!(b.add(zero, x), x);
        assert_eq!(b.mul_add(x, zero, one), one);
        assert_eq!(b.mul_k_add(x, k1, zero), x);
        assert_eq!(b.mul_k_add(x, k0, one), one);
        assert_eq!(b.mul_k_add(zero, k, zero), zero);
        let finished = b.finish();
        assert!(finished.failures.is_empty(), "{:?}", finished.failures);
        assert_eq!(finished.circuit.row_counts().into_values(), [0, 0, 0, 0, 0, 4]);
    }

    #[test]
    fn a_repeated_row_is_the_earlier_one() {
        let mut b = Builder::new();
        let (x, y, z) = (
            b.free_e(F192::new(3, 5, 7)),
            b.free_e(F192::new(2, 0, 9)),
            b.free_e(F192::new(4, 1, 0)),
        );
        let k = b.free_k(9);
        let xy = b.mul_add(x, y, z);
        assert_eq!(b.mul_add(y, x, z), xy, "the factors commute");
        let xz = b.mul_add(x, z, y);
        assert_ne!(xz, xy, "a term is not a factor");
        assert_eq!(b.e(xz), b.e(x) * b.e(z) + b.e(y));
        let sum = b.add(x, y);
        assert_eq!(b.add(y, x), sum, "the terms of a sum commute");
        let one = b.one();
        assert_eq!(b.mul_add(one, y, x), sum, "a sum is a product by one");
        assert_ne!(b.mul_add(x, y, one), sum);
        let xk = b.mul_k_add(x, k, z);
        assert_eq!(b.mul_k_add(x, k, z), xk);
        assert_ne!(b.mul_k_add(z, k, x), xk, "a K row is not symmetric");
        assert_ne!(b.mul_add(x, y, y), xy, "another addend is another row");
        let (x_again, k_again) = (b.free_e(b.e(x)), b.free_k(b.k(k)));
        assert_ne!(
            b.mul_add(x_again, y, z),
            xy,
            "a row folds by its wires, never by their values"
        );
        assert_ne!(
            b.mul_k_add(x, k_again, z),
            xk,
            "a row folds by its wires, never by their values"
        );
        let finished = b.finish();
        assert!(finished.failures.is_empty(), "{:?}", finished.failures);
        let [emul, exk, ..] = finished.circuit.row_counts().into_values();
        assert_eq!(
            (emul, exk),
            (6, 3),
            "x·y + z, x·z + y, x + y, x·y + 1, x·y + y, x'·y + z; then x·k + z, z·k + x, x·k' + z"
        );
    }

    #[test]
    fn the_chain_in_rows_is_the_native_chain() {
        for n in [0, 3, 8, 13, 16] {
            let words: Vec<u64> = (0..n).map(|i| 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i + 1)).collect();
            let mut b = Builder::new();
            let wires: Vec<Kw> = words.iter().map(|&w| b.free_k(w)).collect();
            let h = b.chain(&wires);
            assert_eq!(b.d(h), chain(&words), "{n} words");
            // The native chain is BLAKE2s of the words' bytes, so its length is hashed.
            let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
            assert_eq!(
                chain(&words),
                primitives::hash::digest_words(&primitives::hash::hash(&bytes)),
                "{n} words"
            );
        }
    }
}
