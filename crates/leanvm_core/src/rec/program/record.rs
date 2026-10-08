//! The verifier's steps recorded as a straight-line program: the third arithmetic the verifier is run over.
//!
//! Each call of the verifier's arithmetic or transcript appends one operation, and computes its value on the side.
//!
//! The operations depend on the shape alone, the values on the proof: a program built from a shape is the one built from a proof.

use crate::leaf::PublicColumns;
use crate::rec::circuit::{Compression, PARAM_IV, chain, digest_limbs, zero_prefix};
use crate::rec::transcript::ProofSource;
use ::pcs::verifier::OpeningVerifier;
use ::pcs::whir::{Stratum, strata};
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::TranscriptError;
use fiat_shamir::{DS_OBSERVE, DS_POW_BASE, DS_POW_NONCE, DS_SQUEEZE, MAX_GRINDING_BITS, MAX_PENDING};
use primitives::field::{F64, F192};
use std::collections::HashMap;

/// An element of `E`, by number.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct E(pub(super) u32);

/// A word of `K`, by number.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct K(pub(super) u32);

/// A digest, by number.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct D(pub(super) u32);

/// A query: its position, a word the program computes.
#[derive(Clone, Copy, Debug)]
pub struct Query {
    /// The position.
    pos: K,
    /// How many bits the position has.
    depth: usize,
}

/// Where words sit in the program's memory, as a word index of a region.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Loc {
    /// The constants, in the image.
    Const(usize),
    /// The advice: the proof and the hints.
    Advice(usize),
    /// The program's scratch words, in RAM.
    Scratch(usize),
}

impl Loc {
    /// The location `k` words on.
    pub(super) const fn add(self, k: usize) -> Self {
        match self {
            Self::Const(i) => Self::Const(i + k),
            Self::Advice(i) => Self::Advice(i + k),
            Self::Scratch(i) => Self::Scratch(i + k),
        }
    }
}

/// Where an element is when no extension register holds it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Home {
    /// One of the constant registers: `1`, `y`, `y^2`.
    Pinned(u8),
    /// Three words of memory.
    Mem(Loc),
    /// Nowhere: an instruction computed it.
    Computed,
}

/// One step of the verifier.
#[derive(Clone, Debug)]
pub(super) enum Op {
    /// `out = a * b + d`.
    MulAdd { out: u32, a: u32, b: u32, d: Option<u32> },
    /// `out = a * k + d`, `k` a word.
    MulKAdd { out: u32, a: u32, k: u32, d: Option<u32> },
    /// `a = b`.
    AssertEq { a: u32, b: u32 },
    /// `e` stored at `at`, which gives its limbs as words.
    Limbs { e: u32, at: Loc },
    /// The transcript's first state: the compression of the seed and the output's four words.
    Init { iv: Loc, output: Loc },
    /// A transcript step absorbing up to two scalars, its challenge copied to `challenge`.
    Step {
        first: Option<Loc>,
        last: Option<Loc>,
        tag: u64,
        challenge: Option<Loc>,
    },
    /// A proof of work on the nonce at `nonce`, then the step that binds it.
    Grind { nonce: Loc, bits: u32 },
    /// The announced clock at `at` is live, at slot zero, with nothing above its live bit.
    Clock { at: Loc },
    /// Query positions cut from the challenge at `challenge`, `depth` bits each, each moved into its stratum.
    Queries {
        challenge: Loc,
        depth: usize,
        strata: Vec<Stratum>,
        out: Loc,
    },
    /// A leaf hashed from its words, then `levels` nodes up its path, into the digest at `out`.
    OpenRow {
        pos: Loc,
        levels: usize,
        row_words: usize,
        leaf_words: usize,
        seed: Loc,
        leaf: Loc,
        path: Loc,
        out: Loc,
    },
    /// The parent of two nodes.
    Parent { left: Loc, right: Loc, out: Loc },
    /// Two digests are one.
    EqD { a: Loc, b: Loc },
    /// A root read as two scalars, their top limbs zero.
    Root { lo: Loc, hi: Loc, out: Loc },
    /// The transcript's state set to a constant: the start of a transcript with no statement of its own.
    InitState { state: Loc },
    /// The transcript's state, copied out as two elements: three words, then the fourth.
    State { out: [Loc; 2] },
    /// The hash of these words, into the digest at `out`.
    Chain { words: Vec<Loc>, out: Loc },
    /// The program's output, the digest at `digest`, and its exit.
    Exit { digest: Loc },
}

/// The recorder: the verifier's operations, and every value they compute on this proof.
pub struct Gen<'a> {
    /// The operations, in order.
    pub(super) ops: Vec<Op>,
    /// Each element's home and value.
    pub(super) es: Vec<(Home, F192)>,
    /// Each word's place and value.
    ks: Vec<(Loc, u64)>,
    /// Each digest's place and value.
    ds: Vec<(Loc, [u64; 4])>,
    /// The constants' words.
    pub(super) consts: Vec<u64>,
    /// The advice's words: the proof as it is read, and the hints.
    pub(super) advice: Vec<u64>,
    /// How many scratch words the program uses.
    pub(super) n_scratch: usize,
    e_consts: HashMap<[u64; 3], u32>,
    k_consts: HashMap<u64, u32>,
    memo: HashMap<(u8, u32, u32, u32), u32>,
    /// The chaining value after each number of zero blocks, among the constants.
    seeds: HashMap<usize, Loc>,
    zero: E,
    one: E,
    source: ProofSource<'a>,
    offset: usize,
    opening: usize,
    pending: Vec<E>,
    cv: [F64; 4],
}

impl<'a> Gen<'a> {
    /// The register of the constant one, then `y`, then `y^2`.
    const PINNED: [F192; 3] = [F192::ONE, F192::new(0, 1, 0), F192::new(0, 0, 1)];

    /// An empty recorder.
    pub(super) fn new() -> Self {
        let mut g = Self {
            ops: Vec::new(),
            es: (0..3).map(|i| (Home::Pinned(i as u8), Self::PINNED[i])).collect(),
            ks: Vec::new(),
            ds: Vec::new(),
            consts: Vec::new(),
            advice: Vec::new(),
            n_scratch: 0,
            e_consts: HashMap::new(),
            k_consts: HashMap::new(),
            memo: HashMap::new(),
            seeds: HashMap::new(),
            zero: E(0),
            one: E(0),
            source: ProofSource::Shape,
            offset: 0,
            opening: 0,
            pending: Vec::new(),
            cv: [F64::ZERO; 4],
        };
        g.zero = g.e_const(F192::ZERO);
        g
    }

    /// The value of an element.
    pub(super) fn e(&self, x: E) -> F192 {
        self.es[x.0 as usize].1
    }

    fn k(&self, x: K) -> u64 {
        self.ks[x.0 as usize].1
    }

    fn new_e(&mut self, home: Home, value: F192) -> E {
        self.es.push((home, value));
        E(self.es.len() as u32 - 1)
    }

    fn new_k(&mut self, loc: Loc, value: u64) -> K {
        self.ks.push((loc, value));
        K(self.ks.len() as u32 - 1)
    }

    fn new_d(&mut self, value: [u64; 4]) -> D {
        let loc = self.scratch(4);
        self.ds.push((loc, value));
        D(self.ds.len() as u32 - 1)
    }

    fn d_loc(&self, d: D) -> Loc {
        self.ds[d.0 as usize].0
    }

    fn d(&self, d: D) -> [u64; 4] {
        self.ds[d.0 as usize].1
    }

    /// Where a word is.
    pub(super) fn k_loc(&self, k: u32) -> Loc {
        self.ks[k as usize].0
    }

    const fn scratch(&mut self, words: usize) -> Loc {
        self.n_scratch += words;
        Loc::Scratch(self.n_scratch - words)
    }

    /// Scratch words for one element, on a 32-byte boundary: where the element instructions find its limbs.
    const fn scratch_element(&mut self) -> Loc {
        self.n_scratch = self.n_scratch.next_multiple_of(ELEMENT);
        self.scratch(ELEMENT)
    }

    /// An element among the hints, on a 32-byte boundary.
    fn hint_element(&mut self, v: F192) -> Loc {
        self.advice.resize(self.advice.len().next_multiple_of(ELEMENT), 0);
        self.hint(&[v.c0, v.c1, v.c2, 0])
    }

    fn pool(&mut self, words: &[u64]) -> Loc {
        self.consts.extend_from_slice(words);
        Loc::Const(self.consts.len() - words.len())
    }

    fn hint(&mut self, words: &[u64]) -> Loc {
        self.advice.extend_from_slice(words);
        Loc::Advice(self.advice.len() - words.len())
    }

    fn e_const(&mut self, c: F192) -> E {
        if let Some(i) = Self::PINNED.iter().position(|&p| p == c) {
            return E(i as u32);
        }
        let limbs = [c.c0, c.c1, c.c2];
        if let Some(&id) = self.e_consts.get(&limbs) {
            return E(id);
        }
        self.consts.resize(self.consts.len().next_multiple_of(ELEMENT), 0);
        let loc = self.pool(&[c.c0, c.c1, c.c2, 0]);
        let e = self.new_e(Home::Mem(loc), c);
        self.e_consts.insert(limbs, e.0);
        e
    }

    fn k_const(&mut self, c: u64) -> K {
        if let Some(&id) = self.k_consts.get(&c) {
            return K(id);
        }
        let loc = self.pool(&[c]);
        let k = self.new_k(loc, c);
        self.k_consts.insert(c, k.0);
        k
    }

    /// The memory home of a scalar read off the proof.
    fn advice_of(&self, x: E) -> Loc {
        match self.es[x.0 as usize].0 {
            Home::Mem(loc @ Loc::Advice(_)) => loc,
            home => unreachable!("only a scalar of the proof is absorbed, not {home:?}"),
        }
    }

    fn emit_mul_add(&mut self, a: E, b: E, d: Option<E>) -> E {
        // The factors of a product commute.
        let (a, b) = (E(a.0.min(b.0)), E(a.0.max(b.0)));
        let key = (0, a.0, b.0, d.map_or(u32::MAX, |d| d.0));
        if let Some(&out) = self.memo.get(&key) {
            return E(out);
        }
        let value = self.e(a) * self.e(b) + d.map_or(F192::ZERO, |d| self.e(d));
        let out = self.new_e(Home::Computed, value);
        self.ops.push(Op::MulAdd {
            out: out.0,
            a: a.0,
            b: b.0,
            d: d.map(|d| d.0),
        });
        self.memo.insert(key, out.0);
        out
    }

    fn emit_mul_k_add(&mut self, a: E, k: K, d: Option<E>) -> E {
        let key = (1, a.0, k.0, d.map_or(u32::MAX, |d| d.0));
        if let Some(&out) = self.memo.get(&key) {
            return E(out);
        }
        let value = self.e(a).mul_base(F64(self.k(k))) + d.map_or(F192::ZERO, |d| self.e(d));
        let out = self.new_e(Home::Computed, value);
        self.ops.push(Op::MulKAdd {
            out: out.0,
            a: a.0,
            k: k.0,
            d: d.map(|d| d.0),
        });
        self.memo.insert(key, out.0);
        out
    }

    /// `e`'s limbs as words: the words it sits in, or scratch words it is stored to.
    pub(super) fn limbs(&mut self, e: E) -> [K; 3] {
        let v = self.e(e);
        if let Home::Mem(at) = self.es[e.0 as usize].0 {
            return std::array::from_fn(|i| self.new_k(at.add(i), [v.c0, v.c1, v.c2][i]));
        }
        let at = self.scratch_element();
        self.ops.push(Op::Limbs { e: e.0, at });
        std::array::from_fn(|i| self.new_k(at.add(i), [v.c0, v.c1, v.c2][i]))
    }

    fn take(&mut self) -> E {
        let v = match self.source {
            ProofSource::Proof(p) => p.stream.get(self.offset).copied().unwrap_or(F192::ZERO),
            ProofSource::Shape => F192::ZERO,
        };
        self.offset += 1;
        let at = self.hint_element(v);
        self.new_e(Home::Mem(at), v)
    }

    fn step(&mut self, scalars: &[E], tag: F64, squeeze: bool) -> Option<E> {
        let values: Vec<F192> = scalars.iter().map(|&s| self.e(s)).collect();
        let (first, last) = match *scalars {
            [a, b] => (Some(self.advice_of(a)), Some(self.advice_of(b))),
            [b] => (None, Some(self.advice_of(b))),
            _ => (None, None),
        };
        self.cv = fiat_shamir::step(self.cv, &values, tag);
        let challenge = squeeze.then(|| {
            let loc = self.scratch_element();
            let [c0, c1, c2, _] = self.cv.map(|w| w.0);
            (loc, self.new_e(Home::Mem(loc), F192::new(c0, c1, c2)))
        });
        self.ops.push(Op::Step {
            first,
            last,
            tag: tag.0,
            challenge: challenge.map(|c| c.0),
        });
        challenge.map(|c| c.1)
    }

    fn flush(&mut self) {
        if !self.pending.is_empty() {
            let pending = std::mem::take(&mut self.pending);
            self.step(&pending, DS_OBSERVE, false);
        }
    }

    fn observe(&mut self, x: E) {
        if self.pending.len() == MAX_PENDING {
            self.flush();
        }
        self.pending.push(x);
    }

    /// Start on the next proof: its run's four output words, read off the advice, and its transcript seeded with them after `iv`.
    pub(super) fn start(&mut self, source: ProofSource<'a>, iv: [u64; 4], output: [u64; 4]) -> [K; 4] {
        debug_assert!(self.pending.is_empty(), "the previous proof's transcript is flushed");
        (self.source, self.offset, self.opening) = (source, 0, 0);
        let at = self.hint(&output);
        let seed = self.pool(&iv);
        self.cv = fiat_shamir::compress(iv.map(F64), output.map(F64));
        self.ops.push(Op::Init { iv: seed, output: at });
        std::array::from_fn(|i| self.new_k(at.add(i), output[i]))
    }

    /// Hold the next scalar of the proof to a constant of the shape.
    pub(super) fn expect_scalar(&mut self, c: F192) {
        let x = self.take();
        self.observe(x);
        let c = self.e_const(c);
        self.ops.push(Op::AssertEq { a: x.0, b: c.0 });
    }

    /// The announced final clock: a scalar whose word is a live clock at slot zero.
    pub(super) fn clock(&mut self) -> E {
        let x = self.take();
        self.observe(x);
        self.ops.push(Op::Clock { at: self.advice_of(x) });
        x
    }

    /// The word `k` as an element.
    pub(super) fn k_to_e(&mut self, k: K) -> E {
        let one = self.one();
        self.emit_mul_k_add(one, k, None)
    }

    /// Hash these words and the limbs of these elements into the program's output, and return it.
    pub(super) fn commit(&mut self, words: &[K], elements: &[E]) -> [u64; 4] {
        self.flush();
        let mut all = words.to_vec();
        for &e in elements {
            all.extend(self.limbs(e));
        }
        let digest = self.chain(&all);
        self.ops.push(Op::Exit {
            digest: self.d_loc(digest),
        });
        self.d(digest)
    }

    /// The hash of these words.
    pub(super) fn chain(&mut self, words: &[K]) -> D {
        let values: Vec<u64> = words.iter().map(|&k| self.k(k)).collect();
        let out = self.new_d(chain(&values));
        self.ops.push(Op::Chain {
            words: words.iter().map(|&k| self.ks[k.0 as usize].0).collect(),
            out: self.d_loc(out),
        });
        out
    }

    /// A digest's four words.
    pub(super) fn d_words(&mut self, d: D) -> [K; 4] {
        let (loc, value) = self.ds[d.0 as usize];
        std::array::from_fn(|i| self.new_k(loc.add(i), value[i]))
    }

    /// A digest as two elements, two words each with a zero top limb.
    pub(super) fn d_halves(&mut self, d: D) -> [E; 2] {
        let w = self.d_words(d);
        let (one, y) = (E(0), E(1));
        [0, 2].map(|i| {
            let low = self.emit_mul_k_add(one, w[i], None);
            self.emit_mul_k_add(y, w[i + 1], Some(low))
        })
    }

    /// The digest two elements of the advice are the halves of: their top limbs are zero.
    pub(super) fn halves_to_d(&mut self, lo: E, hi: E) -> D {
        let (l, h) = (self.e(lo), self.e(hi));
        let out = self.new_d([l.c0, l.c1, h.c0, h.c1]);
        self.ops.push(Op::Root {
            lo: self.advice_of(lo),
            hi: self.advice_of(hi),
            out: self.d_loc(out),
        });
        out
    }

    /// A free element: the prover's, among the hints.
    pub(super) fn free_e(&mut self, v: F192) -> E {
        let at = self.hint_element(v);
        self.new_e(Home::Mem(at), v)
    }

    /// A word that is a constant.
    pub(super) fn word(&mut self, c: u64) -> K {
        self.k_const(c)
    }

    /// The transcript's state as two elements: its first three words, then its fourth.
    pub(super) fn state(&mut self) -> [E; 2] {
        self.flush();
        let out = [self.scratch_element(), self.scratch_element()];
        self.ops.push(Op::State { out });
        let [w0, w1, w2, w3] = self.cv.map(|w| w.0);
        [
            self.new_e(Home::Mem(out[0]), F192::new(w0, w1, w2)),
            self.new_e(Home::Mem(out[1]), F192::new(w3, 0, 0)),
        ]
    }

    /// Start on a transcript whose state is the constant `state`, reading `source`: a proof with no statement of its own.
    pub(super) fn start_from(&mut self, source: ProofSource<'a>, state: [u64; 4]) {
        debug_assert!(self.pending.is_empty(), "the previous transcript is flushed");
        (self.source, self.offset, self.opening) = (source, 0, 0);
        let at = self.pool(&state);
        self.cv = state.map(F64);
        self.ops.push(Op::InitState { state: at });
    }

    /// Start on the next proof, whose run's output is the digest `output`, its transcript seeded with it after `iv`.
    pub(super) fn start_on(&mut self, source: ProofSource<'a>, iv: [u64; 4], output: D) -> [K; 4] {
        debug_assert!(self.pending.is_empty(), "the previous proof's transcript is flushed");
        (self.source, self.offset, self.opening) = (source, 0, 0);
        let seed = self.pool(&iv);
        self.cv = fiat_shamir::compress(iv.map(F64), self.d(output).map(F64));
        self.ops.push(Op::Init {
            iv: seed,
            output: self.d_loc(output),
        });
        self.d_words(output)
    }

    /// Whether the whole proof was read.
    pub(super) const fn finished(&self) -> bool {
        match self.source {
            ProofSource::Proof(p) => self.offset == p.stream.len() && self.opening == p.merkle.len(),
            ProofSource::Shape => true,
        }
    }
}

impl Arith for Gen<'_> {
    type E = E;

    fn constant(&mut self, c: F192) -> E {
        self.e_const(c)
    }

    fn mul_add(&mut self, a: E, b: E, d: E) -> E {
        if a == self.zero || b == self.zero {
            d
        } else if d == self.zero {
            if b == self.one {
                a
            } else if a == self.one {
                b
            } else {
                self.emit_mul_add(a, b, None)
            }
        } else {
            self.emit_mul_add(a, b, Some(d))
        }
    }

    fn add(&mut self, a: E, d: E) -> E {
        let one = self.one;
        self.mul_add(a, one, d)
    }

    fn mul_const_add(&mut self, a: E, c: F192, d: E) -> E {
        if c.c1 == 0 && c.c2 == 0 {
            if c.c0 <= 1 {
                let c = self.e_const(c);
                return self.mul_add(a, c, d);
            }
            if a == self.zero {
                return d;
            }
            let k = self.k_const(c.c0);
            return self.emit_mul_k_add(a, k, (d != self.zero).then_some(d));
        }
        let c = self.e_const(c);
        self.mul_add(a, c, d)
    }

    fn inv(&mut self, a: E) -> E {
        let v = self.e(a);
        let v = if v.is_zero() { F192::ZERO } else { v.inv() };
        let at = self.hint_element(v);
        let i = self.new_e(Home::Mem(at), v);
        let p = self.mul(a, i);
        let one = self.one;
        self.ops.push(Op::AssertEq { a: p.0, b: one.0 });
        i
    }

    fn frobenius2(&mut self, a: E) -> E {
        let [_, c1, c2] = self.limbs(a);
        let y_y2 = self.e_const(F192::new(0, 1, 1));
        let y2 = self.e_const(F192::new(0, 0, 1));
        let u = self.emit_mul_k_add(y_y2, c2, Some(a));
        self.emit_mul_k_add(y2, c1, Some(u))
    }

    fn zero(&mut self) -> E {
        self.zero
    }

    fn one(&mut self) -> E {
        self.one
    }
}

impl PublicColumns for Gen<'_> {}

impl Verifier for Gen<'_> {
    fn next_scalar(&mut self) -> Result<E, TranscriptError> {
        let x = self.take();
        self.observe(x);
        Ok(x)
    }

    fn next_round_poly(&mut self, n_coeffs: usize, claim: E, eq: Option<E>) -> Result<Vec<E>, TranscriptError> {
        let fixed = usize::from(eq.is_none());
        let mut coeffs: Vec<E> = (0..n_coeffs)
            .map(|i| if i == fixed { claim } else { self.take() })
            .collect();
        let tail = self.sum(&coeffs[fixed + 1..]);
        coeffs[fixed] = match eq {
            None => self.add(claim, tail),
            Some(r) => self.mul_add(r, tail, claim),
        };
        for (i, &c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.observe(c);
            }
        }
        Ok(coeffs)
    }

    fn sample(&mut self) -> E {
        let pending = std::mem::take(&mut self.pending);
        self.step(&pending, DS_SQUEEZE, true)
            .expect("a squeeze gives a challenge")
    }

    fn grind_check(&mut self, bits: u32) -> Result<(), TranscriptError> {
        assert!(bits <= MAX_GRINDING_BITS, "grinding past the digest's low word");
        self.flush();
        let nonce = self.take();
        self.ops.push(Op::Grind {
            nonce: self.advice_of(nonce),
            bits,
        });
        self.cv = fiat_shamir::step(self.cv, &[self.e(nonce)], DS_POW_NONCE);
        Ok(())
    }

    fn ensure_eq<Er>(&mut self, a: E, b: E, _: impl FnOnce() -> Er) -> Result<(), Er> {
        if a != b {
            self.ops.push(Op::AssertEq { a: a.0, b: b.0 });
        }
        Ok(())
    }

    fn finish(&mut self) -> Result<(), TranscriptError> {
        self.flush();
        Ok(())
    }
}

impl Gen<'_> {
    /// `sum_i terms_i`.
    fn sum(&mut self, terms: &[E]) -> E {
        let zero = self.zero;
        terms.iter().fold(zero, |acc, &t| self.add(acc, t))
    }

    /// The next opening of the proof: its leaf's committed words and its path, of the shape's sizes.
    fn next_opening(&mut self, leaf_words: usize, row_words: usize, levels: usize) -> (Vec<u64>, Vec<[u64; 4]>) {
        let opening = match self.source {
            ProofSource::Proof(p) => p.merkle.get(self.opening),
            ProofSource::Shape => None,
        };
        self.opening += 1;
        let mut image: Vec<u64> = opening.map_or_else(Vec::new, |o| o.leaf_data.iter().map(|w| w.0).collect());
        image.resize(leaf_words, 0);
        let mut path: Vec<[u64; 4]> = opening.map_or_else(Vec::new, |o| o.path.iter().map(digest_limbs).collect());
        path.resize(levels, [0; 4]);
        (image.split_off(leaf_words - row_words), path)
    }

    /// Open one row at `query`, up to the node its stratum fixes, and return that node and the row's words.
    fn open_row(&mut self, query: &Query, s: Stratum, row_words: usize, leaf_words: usize) -> (D, Vec<K>) {
        assert!(
            leaf_words.is_multiple_of(8) && row_words <= leaf_words,
            "a leaf of whole blocks holds the row"
        );
        let levels = query.depth - s.bits;
        let (row, path) = self.next_opening(leaf_words, row_words, levels);
        // The row's words three to a 32-byte slot, so that three of them that are an element are one where they are.
        self.advice.resize(self.advice.len().next_multiple_of(ELEMENT), 0);
        let mut slots = vec![0; leaf_slot(row.len())];
        for (i, &word) in row.iter().enumerate() {
            slots[leaf_slot(i)] = word;
        }
        let (leaf, siblings) = (self.hint(&slots), self.hint(path.as_flattened()));

        // The value: the leaf's chain from the zero blocks' state, then the path, low bit first.
        let prefix = leaf_words - row_words;
        let zero_blocks = prefix / 8;
        let image: Vec<u64> = std::iter::repeat_n(0, prefix - zero_blocks * 8)
            .chain(row.iter().copied())
            .collect();
        let n_blocks = leaf_words / 8;
        let mut h = zero_prefix(zero_blocks);
        let seed = match self.seeds.get(&zero_blocks) {
            Some(&seed) => seed,
            None => {
                let seed = self.pool(&h);
                self.seeds.insert(zero_blocks, seed);
                seed
            }
        };
        for (j, m) in image.as_chunks::<8>().0.iter().enumerate() {
            let index = zero_blocks + j;
            h = Compression::new(h, *m, 64 * (index as u64 + 1), index + 1 == n_blocks).output();
        }
        let pos = self.k(query.pos);
        for (level, sibling) in path.iter().enumerate() {
            let m = if pos >> level & 1 == 1 {
                [*sibling, h]
            } else {
                [h, *sibling]
            };
            h = Compression::single(*m.as_flattened().first_chunk().expect("eight words")).output();
        }
        let out = self.new_d(h);
        self.ops.push(Op::OpenRow {
            pos: self.ks[query.pos.0 as usize].0,
            levels,
            row_words,
            leaf_words,
            seed,
            leaf,
            path: siblings,
            out: self.d_loc(out),
        });
        let words = (0..row_words)
            .map(|i| self.new_k(leaf.add(leaf_slot(i)), row[i]))
            .collect();
        (out, words)
    }

    fn parent(&mut self, left: D, right: D) -> D {
        let m = [self.d(left), self.d(right)];
        let value = Compression::single(*m.as_flattened().first_chunk().expect("eight words")).output();
        let out = self.new_d(value);
        self.ops.push(Op::Parent {
            left: self.d_loc(left),
            right: self.d_loc(right),
            out: self.d_loc(out),
        });
        out
    }

    fn tie(&mut self, slot: &mut Option<D>, node: D) {
        match *slot {
            Some(known) => self.ops.push(Op::EqD {
                a: self.d_loc(known),
                b: self.d_loc(node),
            }),
            None => *slot = Some(node),
        }
    }
}

impl OpeningVerifier for Gen<'_> {
    type Root = D;
    type K = K;
    type Query = Query;

    fn next_root(&mut self) -> Result<D, TranscriptError> {
        let (lo, hi) = (self.take(), self.take());
        self.observe(lo);
        self.observe(hi);
        Ok(self.halves_to_d(lo, hi))
    }

    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<Query> {
        let per = 192 / depth;
        let all = strata(count, depth);
        let mut out = Vec::with_capacity(count);
        while out.len() < count {
            let v = self.sample();
            let n = per.min(count - out.len());
            let Home::Mem(challenge) = self.es[v.0 as usize].0 else {
                unreachable!("a challenge has a home")
            };
            let c = self.e(v);
            let first = self.scratch(n);
            let limbs = [c.c0, c.c1, c.c2];
            for j in 0..n {
                let s = all[out.len()];
                let at = j * depth;
                let (limb, shift) = (at / 64, at % 64);
                let mut raw = limbs[limb] >> shift;
                if shift + depth > 64 {
                    raw |= limbs[limb + 1] << (64 - shift);
                }
                let low = depth - s.bits;
                let kept = if low == 0 { 0 } else { raw & (u64::MAX >> (64 - low)) };
                let pos = kept | (s.index as u64) << low;
                let k = self.new_k(first.add(j), pos);
                out.push(Query { pos: k, depth });
            }
            self.ops.push(Op::Queries {
                challenge,
                depth,
                strata: all[out.len() - n..out.len()].to_vec(),
                out: first,
            });
        }
        out
    }

    fn open_rows(
        &mut self,
        root: &D,
        _depth: usize,
        queries: &[Query],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<K>>, TranscriptError> {
        // Each query's path stops at the node its stratum fixes; the nodes above are hashed once, level by level.
        let depth = queries[0].depth;
        let strata: Vec<Stratum> = strata(queries.len(), depth);
        let top = strata[0].bits;
        let mut nodes: Vec<Vec<Option<D>>> = (0..=top).map(|s| vec![None; 1 << s]).collect();
        let mut rows = Vec::with_capacity(queries.len());
        for (query, &s) in queries.iter().zip(&strata) {
            let (node, row) = self.open_row(query, s, row_words, leaf_words);
            self.tie(&mut nodes[s.bits][s.index], node);
            rows.push(row);
        }
        for s in (1..=top).rev() {
            for j in 0..1 << (s - 1) {
                let [left, right] =
                    [2 * j, 2 * j + 1].map(|i| nodes[s][i].expect("the largest group covers its level"));
                let node = self.parent(left, right);
                self.tie(&mut nodes[s - 1][j], node);
            }
        }
        self.tie(&mut nodes[0][0], *root);
        Ok(rows)
    }

    fn mul_k_add(&mut self, a: E, k: K, d: E) -> E {
        if a == self.zero {
            return d;
        }
        self.emit_mul_k_add(a, k, (d != self.zero).then_some(d))
    }

    fn e_of_limbs(&mut self, limbs: [K; 3]) -> E {
        // Three words in a row are an element where they are.
        let [(l0, v0), (l1, v1), (l2, v2)] = limbs.map(|k| self.ks[k.0 as usize]);
        if l1 == l0.add(1) && l2 == l0.add(2) {
            return self.new_e(Home::Mem(l0), F192::new(v0, v1, v2));
        }
        let (one, y, y2) = (E(0), E(1), E(2));
        let e = self.emit_mul_k_add(one, limbs[0], None);
        let e = self.emit_mul_k_add(y, limbs[1], Some(e));
        self.emit_mul_k_add(y2, limbs[2], Some(e))
    }

    fn query_point(&mut self, query: &Query) -> E {
        self.k_to_e(query.pos)
    }
}

/// The words of an element's slot: its three limbs, on a 32-byte boundary.
pub(super) const ELEMENT: usize = 4;

/// Where word `i` of an opened row is among its hint's words: three words to a slot.
pub(super) const fn leaf_slot(i: usize) -> usize {
    i + i / 3
}

/// The first chaining value of a hash of words: the parameter block's.
pub(super) const CHAIN_IV: [u64; 4] = PARAM_IV;

/// The proof-of-work tags, for the program's proof of work.
pub(super) const POW_TAGS: [u64; 2] = [DS_POW_BASE.0, DS_POW_NONCE.0];
