//! The recursion machine's circuit: a fixed list of rows, one table per operation, wired by copy cycles.
//!
//! A wire is a value of one of three kinds: a `K` word, an `E` element (three limbs) or a digest `D` (four
//! words). Every row of every table names one wire per slot, and every slot carries its wire on the bus as
//! the tuple `(key, v0, v1, v2, v3)`, unused limbs zero. A slot pulls the tuple at its own key and pushes it
//! at the key of the next slot of the same wire, so the slots of a wire form one cycle and the bus balances
//! only if they all hold the same value. A wire touched once is a cycle of one, which constrains nothing:
//! that is a free value, such as a scalar the prover sends.
//!
//! The rows depend on the inner proofs' shapes and never on their values, so the verifier rebuilds the same
//! circuit with no proof. Values are computed alongside, from the proof when there is one and from zeros
//! when there is not.

use primitives::field::{F64, F192};
use std::collections::HashMap;

/// A wire's value as four `K` words; a `K` wire uses the first, an `E` wire the first three.
pub type Limbs = [u64; 4];

/// What a wire holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    K,
    E,
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

/// The recursion machine's tables, in protocol order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Table {
    /// `c = a·b + d` over `E`. Slots `a`, `b`, `d`, `c`.
    Emul,
    /// `c = a·k + d`, `k` in `K`. Slots `a`, `k`, `d`, `c`.
    Exk,
    /// One BLAKE2s compression each: a transcript step or a Merkle node from the parameter IV, or a block of a
    /// Merkle leaf's hash. Slots: the chaining value, the counter and final flag, the message's first half
    /// through the Merkle selector, the selector bit, the message's words 4 to 6 as an `E` element, its word
    /// 7, the output, the output's first three words as a challenge, the eight message words.
    Hash,
    /// A word and its 64 bits.
    Split,
    /// Four words seen as a digest, an `E` element, two 128-bit `E` halves, and four `K` words.
    Cast,
    /// A value the verifier knows: a constant of the circuit or a word of the statement.
    Pub,
}

/// How many tables there are.
pub const N_TABLES: usize = 6;

impl Table {
    /// Every table, in protocol order.
    pub const ALL: [Self; N_TABLES] = [Self::Emul, Self::Exk, Self::Hash, Self::Split, Self::Cast, Self::Pub];

    /// Its slots' kinds; a `Pub` slot takes any kind.
    pub const fn slot_kinds(self) -> &'static [Kind] {
        use Kind::{D, E, K};
        match self {
            Self::Emul => &[E, E, E, E],
            Self::Exk => &[E, K, E, E],
            Self::Hash => &HASH_KINDS,
            Self::Split => &SPLIT_KINDS,
            Self::Cast => &[D, E, E, E, K, K, K, K],
            Self::Pub => &[K],
        }
    }

    /// Its number of slots.
    pub const fn n_slots(self) -> usize {
        self.slot_kinds().len()
    }

    /// The index of the first slot of this table among all tables' slots.
    pub const fn first_slot(self) -> usize {
        let mut total = 0;
        let mut i = 0;
        while i < self as usize {
            total += Self::ALL[i].n_slots();
            i += 1;
        }
        total
    }
}

const SPLIT_KINDS: [Kind; 65] = [Kind::K; 65];

/// The slots of a hash row: `h`, `(t, f)`, the muxed half, `b`, `x`, `ds`, the output, the challenge, `m0..m7`.
const HASH_KINDS: [Kind; 16] = {
    use Kind::{D, E, K};
    [D, D, D, K, E, K, D, E, K, K, K, K, K, K, K, K]
};

/// The number of slots of a hash row.
const HASH_SLOTS: usize = HASH_KINDS.len();

/// The domain tags of the transcript's compressions (`fiat_shamir`).
pub mod tag {
    pub const OBSERVE: u64 = 1;
    pub const SQUEEZE: u64 = 2;
    pub const POW_BASE: u64 = 3;
    pub const POW_NONCE: u64 = 4;
}

/// The finalization word of a last block.
pub const FINAL: u64 = u32::MAX as u64;

/// Where a `Pub` row's value comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PubSource {
    Const(Limbs),
    /// Word `i` of the statement.
    Statement(usize),
}

/// The inputs of one hash row, in the circuit's port order: `t`, `f`, `h`, `m`.
pub type HashInputs = [u64; 14];

/// The fixed part of a circuit: its rows, and for each slot the wire it names.
///
/// The statement's `Pub` rows come first, in statement order, then the constants'.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Circuit {
    /// Per table, row-major, each row's slots' wire classes.
    pub rows: [Vec<u32>; N_TABLES],
    /// Per `Pub` row, its value's source.
    pub pubs: Vec<PubSource>,
    /// How many words the statement has.
    pub statement_len: usize,
    /// Each table's least height, as a base-two logarithm: a circuit that must share its heights with others
    /// is padded to theirs.
    pub floor: [usize; N_TABLES],
}

/// What the prover adds to a circuit: every wire's value, and every hash row's inputs.
pub struct Assignment {
    /// Per table, row-major, each row's slots' own wires, whose values the slots carry.
    pub rows: [Vec<u32>; N_TABLES],
    pub values: Vec<Limbs>,
    /// Per hash row, its inputs and its selector bit.
    pub hash: Vec<HashInputs>,
    pub selector: Vec<u64>,
    /// The statement's words.
    pub statement: Vec<Limbs>,
}

/// Builds a circuit and, alongside, the values of an honest run of it.
pub struct Builder {
    values: Vec<Limbs>,
    kinds: Vec<Kind>,
    parent: Vec<u32>,
    rows: [Vec<u32>; N_TABLES],
    pubs: Vec<PubSource>,
    consts: HashMap<(Kind, Limbs), u32>,
    hash: Vec<HashInputs>,
    selector: Vec<u64>,
    statement: Vec<Limbs>,
    scope: Vec<String>,
    failures: Vec<String>,
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

const fn e_limbs(x: F192) -> Limbs {
    [x.c0, x.c1, x.c2, 0]
}

const fn limbs_e(l: Limbs) -> F192 {
    F192::new(l[0], l[1], l[2])
}

/// BLAKE2s compression on the circuit's port words, as the HASH class computes it.
pub fn compress_words(inputs: &HashInputs) -> Limbs {
    let block: [u64; 16] = std::array::from_fn(|i| match i {
        0..4 => inputs[2 + i],
        4..8 => 0,
        _ => inputs[6 + i - 8],
    });
    let out = crate::rv::Hash {
        flags: inputs[1],
        t: inputs[0],
        block,
    };
    use crate::rv::InstructionClass;
    out.eval()
}

/// The parameter IV as four words.
pub fn param_iv() -> Limbs {
    let h = primitives::hash::PARAM_IV;
    std::array::from_fn(|i| u64::from(h[2 * i]) | (u64::from(h[2 * i + 1]) << 32))
}

impl Builder {
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
            kinds: Vec::new(),
            parent: Vec::new(),
            rows: Default::default(),
            pubs: Vec::new(),
            consts: HashMap::new(),
            hash: Vec::new(),
            selector: Vec::new(),
            statement: Vec::new(),
            scope: Vec::new(),
            failures: Vec::new(),
        }
    }

    fn wire(&mut self, kind: Kind, value: Limbs) -> u32 {
        let id = u32::try_from(self.values.len()).expect("fewer than 2^32 wires");
        self.values.push(value);
        self.kinds.push(kind);
        self.parent.push(id);
        id
    }

    fn find(&mut self, mut x: u32) -> u32 {
        while self.parent[x as usize] != x {
            let p = self.parent[x as usize];
            self.parent[x as usize] = self.parent[p as usize];
            x = p;
        }
        x
    }

    fn row(&mut self, table: Table, slots: &[u32]) {
        debug_assert_eq!(slots.len(), table.n_slots());
        for (&w, &kind) in slots.iter().zip(table.slot_kinds()) {
            debug_assert!(
                table == Table::Pub || self.kinds[w as usize] == kind,
                "{table:?} slot kind"
            );
        }
        self.rows[table as usize].extend_from_slice(slots);
    }

    /// Run `f` under a name, which an equality that fails reports.
    pub fn scope<T>(&mut self, name: impl Into<String>, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scope.push(name.into());
        let out = f(self);
        self.scope.pop();
        out
    }

    /// The equalities that did not hold on the values, each with its scope.
    pub fn failures(&self) -> &[String] {
        &self.failures
    }

    /// Record a check that failed on the values, which the circuit cannot express as an equality.
    pub fn fail(&mut self, what: &str) {
        if self.failures.len() < 64 {
            self.failures.push(format!("{}: {what}", self.scope.join(" / ")));
        }
    }

    // Values.

    pub fn e(&self, w: Ew) -> F192 {
        limbs_e(self.values[w.0 as usize])
    }

    pub fn k(&self, w: Kw) -> u64 {
        self.values[w.0 as usize][0]
    }

    pub fn d(&self, w: Dw) -> Limbs {
        self.values[w.0 as usize]
    }

    // Wires the prover chooses.

    /// A free `E` value, which only the slots it is used in constrain.
    pub fn free_e(&mut self, value: F192) -> Ew {
        Ew(self.wire(Kind::E, e_limbs(value)))
    }

    pub fn free_k(&mut self, value: u64) -> Kw {
        Kw(self.wire(Kind::K, [value, 0, 0, 0]))
    }

    pub fn free_d(&mut self, value: Limbs) -> Dw {
        Dw(self.wire(Kind::D, value))
    }

    // Constants and the statement.

    fn constant(&mut self, kind: Kind, value: Limbs) -> u32 {
        if let Some(&w) = self.consts.get(&(kind, value)) {
            return w;
        }
        let w = self.wire(kind, value);
        self.pubs.push(PubSource::Const(value));
        self.row(Table::Pub, &[w]);
        self.consts.insert((kind, value), w);
        w
    }

    pub fn e_const(&mut self, value: F192) -> Ew {
        Ew(self.constant(Kind::E, e_limbs(value)))
    }

    pub fn k_const(&mut self, value: u64) -> Kw {
        Kw(self.constant(Kind::K, [value, 0, 0, 0]))
    }

    pub fn d_const(&mut self, value: Limbs) -> Dw {
        Dw(self.constant(Kind::D, value))
    }

    pub fn zero(&mut self) -> Ew {
        self.e_const(F192::ZERO)
    }

    pub fn one(&mut self) -> Ew {
        self.e_const(F192::ONE)
    }

    fn expose(&mut self, w: u32) -> usize {
        let i = self.statement.len();
        self.statement.push(self.values[w as usize]);
        self.pubs.push(PubSource::Statement(i));
        self.row(Table::Pub, &[w]);
        i
    }

    /// Make `w` a word of the statement, which the verifier is handed and the bus holds `w` to.
    pub fn expose_e(&mut self, w: Ew) -> usize {
        self.expose(w.0)
    }

    pub fn expose_k(&mut self, w: Kw) -> usize {
        self.expose(w.0)
    }

    pub fn expose_d(&mut self, w: Dw) -> usize {
        self.expose(w.0)
    }

    // Equalities.

    fn union(&mut self, a: u32, b: u32) {
        if self.values[a as usize] != self.values[b as usize] {
            self.fail("unequal wires");
        }
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[rb as usize] = ra;
        }
    }

    pub fn eq_e(&mut self, a: Ew, b: Ew) {
        self.union(a.0, b.0);
    }

    pub fn eq_k(&mut self, a: Kw, b: Kw) {
        self.union(a.0, b.0);
    }

    pub fn eq_d(&mut self, a: Dw, b: Dw) {
        self.union(a.0, b.0);
    }

    /// Hold `a` to a constant.
    pub fn eq_e_const(&mut self, a: Ew, value: F192) {
        let c = self.e_const(value);
        self.eq_e(a, c);
    }

    pub fn eq_k_const(&mut self, a: Kw, value: u64) {
        let c = self.k_const(value);
        self.eq_k(a, c);
    }

    // Arithmetic.

    /// `a·b + d`.
    pub fn mul_add(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        let c = Ew(self.wire(Kind::E, e_limbs(self.e(a) * self.e(b) + self.e(d))));
        self.row(Table::Emul, &[a.0, b.0, d.0, c.0]);
        c
    }

    pub fn mul(&mut self, a: Ew, b: Ew) -> Ew {
        let zero = self.zero();
        self.mul_add(a, b, zero)
    }

    pub fn add(&mut self, a: Ew, d: Ew) -> Ew {
        let one = self.one();
        self.mul_add(a, one, d)
    }

    pub fn square(&mut self, a: Ew) -> Ew {
        self.mul(a, a)
    }

    /// `a·k + d`, `k` in `K`.
    pub fn mul_k_add(&mut self, a: Ew, k: Kw, d: Ew) -> Ew {
        let c = Ew(self.wire(Kind::E, e_limbs(self.e(a).mul_base(F64(self.k(k))) + self.e(d))));
        self.row(Table::Exk, &[a.0, k.0, d.0, c.0]);
        c
    }

    pub fn mul_k(&mut self, a: Ew, k: Kw) -> Ew {
        let zero = self.zero();
        self.mul_k_add(a, k, zero)
    }

    /// `a·c + d` for a constant `c`.
    pub fn mul_const_add(&mut self, a: Ew, c: F192, d: Ew) -> Ew {
        if c.c1 == 0 && c.c2 == 0 {
            let k = self.k_const(c.c0);
            return self.mul_k_add(a, k, d);
        }
        let c = self.e_const(c);
        self.mul_add(a, c, d)
    }

    pub fn mul_const(&mut self, a: Ew, c: F192) -> Ew {
        let zero = self.zero();
        self.mul_const_add(a, c, zero)
    }

    /// `a + c` for a constant `c`.
    pub fn add_const(&mut self, a: Ew, c: F192) -> Ew {
        let c = self.e_const(c);
        self.add(a, c)
    }

    /// `1 / a`, zero for zero: a hint the prover supplies, held to `a·(1/a) = 1`.
    pub fn inv(&mut self, a: Ew) -> Ew {
        let v = self.e(a);
        let i = self.free_e(if v.is_zero() { F192::ZERO } else { v.inv() });
        let p = self.mul(a, i);
        self.eq_e_const(p, F192::ONE);
        i
    }

    /// `Σ a_i·b_i + init`, one row per term.
    pub fn dot(&mut self, a: &[Ew], b: &[Ew], init: Ew) -> Ew {
        assert_eq!(a.len(), b.len());
        a.iter().zip(b).fold(init, |acc, (&x, &y)| self.mul_add(x, y, acc))
    }

    pub fn sum(&mut self, terms: &[Ew]) -> Ew {
        let mut acc = match terms.first() {
            Some(&t) => t,
            None => return self.zero(),
        };
        for &t in &terms[1..] {
            acc = self.add(acc, t);
        }
        acc
    }

    // Hashing.

    /// One hash row: `compress(acc, (x, ds))` for a transcript step, the selector at zero.
    ///
    /// Returns the output and its first three words as a challenge.
    pub fn compress(&mut self, acc: Dw, x: Ew, ds: Kw) -> (Dw, Ew) {
        let zero = self.k_const(0);
        let (a, xv, dv) = (self.d(acc), self.e(x), self.k(ds));
        let m = [a[0], a[1], a[2], a[3], xv.c0, xv.c1, xv.c2, dv];
        self.compress_row(acc, zero, x, ds, m, 0)
    }

    /// One hash row as a Merkle node: the parent of `acc` and `sibling`, `acc` on the right if `bit`.
    pub fn node(&mut self, acc: Dw, bit: Kw, sibling: Limbs) -> Dw {
        let (a, b) = (self.d(acc), self.k(bit));
        let (left, right) = if b == 1 { (sibling, a) } else { (a, sibling) };
        let m = [
            left[0], left[1], left[2], left[3], right[0], right[1], right[2], right[3],
        ];
        let x = self.free_e(F192::new(m[4], m[5], m[6]));
        let ds = self.free_k(m[7]);
        self.compress_row(acc, bit, x, ds, m, b).0
    }

    /// A compression from the parameter IV: its chaining value and its counter and flag are constants, its
    /// message words free but for what the muxed half, `x` and `ds` hold them to.
    fn compress_row(&mut self, acc: Dw, bit: Kw, x: Ew, ds: Kw, m: [u64; 8], b: u64) -> (Dw, Ew) {
        let iv = param_iv();
        let h = self.d_const(iv);
        let tf = self.d_const([64, FINAL, 0, 0]);
        let words = m.map(|v| self.free_k(v).0);
        let inputs: HashInputs = [
            64, FINAL, iv[0], iv[1], iv[2], iv[3], m[0], m[1], m[2], m[3], m[4], m[5], m[6], m[7],
        ];
        self.hash_row([h.0, tf.0, acc.0, bit.0, x.0, ds.0], words, inputs, b)
    }

    /// One hash row: block `m` absorbed into `h` at byte counter `t`, final if `last`.
    pub fn leaf_block(&mut self, h: Dw, m: [Kw; 8], t: u64, last: bool) -> Dw {
        let f = if last { FINAL } else { 0 };
        let tf = self.d_const([t, f, 0, 0]);
        let hv = self.d(h);
        let mut inputs: HashInputs = [t, f, hv[0], hv[1], hv[2], hv[3], 0, 0, 0, 0, 0, 0, 0, 0];
        for (slot, w) in inputs[6..].iter_mut().zip(m) {
            *slot = self.k(w);
        }
        let v = &inputs[6..];
        let acc = self.free_d([v[0], v[1], v[2], v[3]]);
        let bit = self.free_k(0);
        let x = self.free_e(F192::new(v[4], v[5], v[6]));
        let ds = self.free_k(v[7]);
        self.hash_row([h.0, tf.0, acc.0, bit.0, x.0, ds.0], m.map(|w| w.0), inputs, 0)
            .0
    }

    /// A hash row's slots: `head` its first six, its output and challenge, then `words` its message's.
    fn hash_row(&mut self, head: [u32; 6], words: [u32; 8], inputs: HashInputs, b: u64) -> (Dw, Ew) {
        let out = compress_words(&inputs);
        let o = Dw(self.wire(Kind::D, out));
        let ch = Ew(self.wire(Kind::E, [out[0], out[1], out[2], 0]));
        let mut slots = [0u32; HASH_SLOTS];
        slots[..6].copy_from_slice(&head);
        slots[6..8].copy_from_slice(&[o.0, ch.0]);
        slots[8..].copy_from_slice(&words);
        self.row(Table::Hash, &slots);
        self.hash.push(inputs);
        self.selector.push(b);
        (o, ch)
    }

    // Words and bits.

    fn split_row(&mut self, word: u32, bits: &[u32; 64]) {
        let mut slots = Vec::with_capacity(65);
        slots.push(word);
        slots.extend_from_slice(bits);
        self.row(Table::Split, &slots);
    }

    /// The 64 bits of `w`, lowest first, each a `K` wire holding 0 or 1.
    pub fn split(&mut self, w: Kw) -> [Kw; 64] {
        let v = self.k(w);
        let bits: [Kw; 64] = std::array::from_fn(|i| self.free_k((v >> i) & 1));
        self.split_row(w.0, &bits.map(|b| b.0));
        bits
    }

    /// The word whose bits are `bits`, lowest first, the rest zero.
    pub fn pack(&mut self, bits: &[Kw]) -> Kw {
        assert!(bits.len() <= 64);
        let zero = self.k_const(0);
        let all: [Kw; 64] = std::array::from_fn(|i| bits.get(i).copied().unwrap_or(zero));
        let v = all
            .iter()
            .enumerate()
            .fold(0u64, |acc, (i, &b)| acc | (self.k(b) & 1) << i);
        let w = self.free_k(v);
        self.split_row(w.0, &all.map(|b| b.0));
        w
    }

    // Casts.

    fn cast_row(&mut self, slots: [Option<u32>; 8], v: Limbs) -> [u32; 8] {
        use Kind::{D, E, K};
        let kinds = [D, E, E, E, K, K, K, K];
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
        let wires: [u32; 8] = std::array::from_fn(|i| slots[i].unwrap_or_else(|| self.wire(kinds[i], values[i])));
        for i in 0..8 {
            if slots[i].is_some() && self.values[wires[i] as usize] != values[i] {
                self.fail("cast");
            }
        }
        self.row(Table::Cast, &wires);
        wires
    }

    /// The limbs of `e`.
    pub fn e_to_k(&mut self, e: Ew) -> [Kw; 3] {
        let v = self.e(e);
        let w = self.cast_row(
            [None, Some(e.0), None, None, None, None, None, None],
            [v.c0, v.c1, v.c2, 0],
        );
        [Kw(w[4]), Kw(w[5]), Kw(w[6])]
    }

    /// The element with limbs `k`.
    pub fn k_to_e(&mut self, k: [Kw; 3]) -> Ew {
        let v = [self.k(k[0]), self.k(k[1]), self.k(k[2]), 0];
        let w = self.cast_row(
            [None, None, None, None, Some(k[0].0), Some(k[1].0), Some(k[2].0), None],
            v,
        );
        Ew(w[1])
    }

    /// `k` in `E`.
    pub fn k_to_e1(&mut self, k: Kw) -> Ew {
        let zero = self.k_const(0);
        self.k_to_e([k, zero, zero])
    }

    /// A digest's words.
    pub fn d_to_k(&mut self, d: Dw) -> [Kw; 4] {
        let v = self.d(d);
        let w = self.cast_row([Some(d.0), None, None, None, None, None, None, None], v);
        [Kw(w[4]), Kw(w[5]), Kw(w[6]), Kw(w[7])]
    }

    /// A digest from its words.
    pub fn k_to_d(&mut self, k: [Kw; 4]) -> Dw {
        let v = k.map(|w| self.k(w));
        let w = self.cast_row(
            [
                None,
                None,
                None,
                None,
                Some(k[0].0),
                Some(k[1].0),
                Some(k[2].0),
                Some(k[3].0),
            ],
            v,
        );
        Dw(w[0])
    }

    /// The digest whose two 128-bit halves are `lo` and `hi`, which must have a zero top limb.
    pub fn halves_to_d(&mut self, lo: Ew, hi: Ew) -> Dw {
        let (l, h) = (self.e(lo), self.e(hi));
        if l.c2 != 0 || h.c2 != 0 {
            self.fail("a digest half has a top limb");
        }
        let w = self.cast_row(
            [None, None, Some(lo.0), Some(hi.0), None, None, None, None],
            [l.c0, l.c1, h.c0, h.c1],
        );
        Dw(w[0])
    }

    /// The circuit, its values, and the equalities that did not hold on them.
    ///
    /// A wire's class is numbered by its first slot, so a circuit is the same however it was built.
    pub fn finish(mut self) -> (Circuit, Assignment, Vec<String>) {
        let mut own = std::mem::take(&mut self.rows);
        // The statement's rows first, in statement order: what a recursive verifier evaluates of the `Pub`
        // table is then one aligned stretch.
        let mut order: Vec<usize> = (0..self.pubs.len()).collect();
        order.sort_by_key(|&i| match self.pubs[i] {
            PubSource::Statement(j) => (0, j),
            PubSource::Const(_) => (1, i),
        });
        let pub_rows = &own[Table::Pub as usize];
        own[Table::Pub as usize] = order.iter().map(|&i| pub_rows[i]).collect();
        let pubs: Vec<PubSource> = order.iter().map(|&i| self.pubs[i]).collect();
        let mut number: HashMap<u32, u32> = HashMap::new();
        let rows: [Vec<u32>; N_TABLES] = std::array::from_fn(|t| {
            own[t]
                .iter()
                .map(|&w| {
                    let root = self.find(w);
                    let next = number.len() as u32;
                    *number.entry(root).or_insert(next)
                })
                .collect()
        });
        let statement_len = self.statement.len();
        (
            Circuit {
                rows,
                pubs,
                statement_len,
                floor: [0; N_TABLES],
            },
            Assignment {
                rows: own,
                values: self.values,
                hash: self.hash,
                selector: self.selector,
                statement: self.statement,
            },
            self.failures,
        )
    }

    /// How many rows each table has so far.
    pub fn row_counts(&self) -> [usize; N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len() / Table::ALL[t].n_slots())
    }
}

impl Circuit {
    /// Each table's rows.
    pub fn row_counts(&self) -> [usize; N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len() / Table::ALL[t].n_slots())
    }
}
