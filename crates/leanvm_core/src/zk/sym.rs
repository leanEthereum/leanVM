//! The verifier over a padded transcript: the native verifier's own code, its hidden values held as affine forms over the keys and its checks on them recorded as constraints.
//!
//! - A scalar read while the transcript is hidden is `c + k`: the value sent, plus the key that padded it (characteristic two).
//! - A challenge, a root, a query and every public computation stay values, checked as the native verifier checks them.
//! - A linear step on hidden values is a new form. An element is hidden exactly when its form has a term.
//! - A product of two hidden values, an inverse or a bound value of a hidden one is an auxiliary variable, which the prover supplies after the transcript.
//! - An equality with a hidden side is a linear constraint.
//!
//! What it records is canonical, so that two verifiers agree on it whatever order and scale their own arithmetic takes:
//!
//! - an auxiliary variable is defined on monic forms, its operands divided by their leading coefficient, and a variable defined twice is one variable;
//! - a variable and a linear constraint are named by their digest, the outer constraint system orders them by it, and a constraint stated twice is one constraint.
//!
//! Which values are hidden is fixed by the transcript's shape, so the prover's replay of its own proof records what the verifier records.

use crate::leaf::PublicColumns;
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::TranscriptError;
use pcs::verifier::OpeningVerifier;
use primitives::field::{F64, F192};
use primitives::hash::Hasher;
use primitives::multilinear::mle_eval_par;
use std::collections::{HashMap, HashSet};

/// A variable of the outer constraint system.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Var {
    /// The key of the `i`-th hidden scalar.
    Key(u32),
    /// The `j`-th auxiliary variable made.
    Aux(u32),
}

/// `constant + sum_v coefficient_v v`, its terms sorted by variable, none of them zero.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Form {
    pub(crate) constant: F192,
    pub(crate) terms: Vec<(Var, F192)>,
}

/// An element as the recording verifier holds it: a value, or a form with a term.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Sym {
    /// A public value.
    Pub(F192),
    /// The form at this index of the recorder's arena.
    Hid(u32),
}

/// What defines an auxiliary variable, on monic forms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// `a·b`, its operands in digest order.
    Product = 1,
    /// `1 / a`.
    Inverse = 2,
    /// `a` itself.
    Bind = 3,
}

/// An auxiliary variable: its definition, and its digest.
#[derive(Clone, Debug)]
pub(crate) struct Aux {
    pub(crate) kind: Kind,
    pub(crate) a: Form,
    /// The second operand of a product, empty otherwise.
    pub(crate) b: Form,
    pub(crate) digest: [u8; 32],
}

/// What the recording verifier recorded.
#[derive(Default)]
pub(crate) struct Record {
    pub(crate) forms: Vec<Form>,
    /// Keys read.
    pub(crate) n_keys: u32,
    /// The auxiliary variables, in the order they were made.
    pub(crate) aux: Vec<Aux>,
    /// On the prover's side, each auxiliary variable's value, in the order they were made.
    pub(crate) aux_values: Vec<F192>,
    /// Monic linear forms that must vanish, by digest.
    pub(crate) linear: Vec<([u8; 32], Form)>,
    /// Forms that must be bits, by digest.
    pub(crate) booleans: Vec<([u8; 32], Form)>,
}

impl Record {
    /// The form an element stands for.
    pub(crate) fn form(&self, s: Sym) -> Form {
        match s {
            Sym::Pub(c) => Form {
                constant: c,
                terms: Vec::new(),
            },
            Sym::Hid(i) => self.forms[i as usize].clone(),
        }
    }

    /// The auxiliary variables in the outer system's order, by digest: entry `r` is the variable made `order[r]`-th.
    pub(crate) fn aux_order(&self) -> Vec<u32> {
        let mut order: Vec<u32> = (0..u32::try_from(self.aux.len()).expect("fewer than 2^32 variables")).collect();
        order.sort_unstable_by_key(|&j| self.aux[j as usize].digest);
        order
    }

    /// A form's terms in canonical order: keys by index, then auxiliary variables by digest.
    fn canonical<'f>(&self, f: &'f Form) -> Vec<&'f (Var, F192)> {
        let mut terms: Vec<&(Var, F192)> = f.terms.iter().collect();
        terms.sort_by_key(|(v, _)| match *v {
            Var::Key(i) => (0u8, i, [0u8; 32]),
            Var::Aux(j) => (1, 0, self.aux[j as usize].digest),
        });
        terms
    }

    /// BLAKE2s over a form: its constant, then each term in canonical order, a key as `0, index` and an auxiliary variable as `1, digest`, each with its coefficient. An element of `E` is its three limbs, little-endian.
    pub(crate) fn digest(&self, f: &Form) -> [u8; 32] {
        let mut h = Hasher::new();
        absorb_e(&mut h, f.constant);
        for &&(v, c) in &self.canonical(f) {
            match v {
                Var::Key(i) => {
                    h.update(&[0]);
                    h.update(&i.to_le_bytes());
                }
                Var::Aux(j) => {
                    h.update(&[1]);
                    h.update(&self.aux[j as usize].digest);
                }
            }
            absorb_e(&mut h, c);
        }
        h.finalize()
    }

    /// A form with a term as its leading coefficient, the first term's in canonical order, times its monic form.
    fn monic(&self, f: &Form) -> (F192, Form) {
        let lead = self.canonical(f)[0].1;
        let inv = lead.inv();
        let monic = Form {
            constant: f.constant * inv,
            terms: f.terms.iter().map(|&(v, c)| (v, c * inv)).collect(),
        };
        (lead, monic)
    }
}

/// An element of `E` into a hash, its limbs little-endian.
fn absorb_e(h: &mut Hasher, x: F192) {
    for limb in [x.c0, x.c1, x.c2] {
        h.update(&limb.to_le_bytes());
    }
}

/// The verifier's arithmetic and transcript over a padded proof, read through a native transport `T`.
pub(crate) struct Recorder<T> {
    t: T,
    record: Record,
    /// Each auxiliary variable by its digest.
    by_digest: HashMap<[u8; 32], u32>,
    /// The linear constraints and bits recorded, by digest.
    stated: HashSet<[u8; 32]>,
    /// Each form's value, on the prover's side, which knows the keys.
    values: Option<Vec<F192>>,
    keys: Vec<F192>,
    hidden: bool,
}

impl<T> Recorder<T> {
    /// A verifier that knows no key.
    pub(crate) fn new(t: T) -> Self {
        Self {
            t,
            record: Record::default(),
            by_digest: HashMap::new(),
            stated: HashSet::new(),
            values: None,
            keys: Vec::new(),
            hidden: false,
        }
    }

    /// The prover's replay of its own proof: it knows every key, so it computes each value it records.
    pub(crate) fn with_keys(t: T, keys: Vec<F192>) -> Self {
        let mut r = Self::new(t);
        r.values = Some(Vec::new());
        r.keys = keys;
        r
    }

    /// The transport, to read the rest of the proof natively.
    pub(crate) const fn transport(&mut self) -> &mut T {
        &mut self.t
    }

    /// The transport back, and what was recorded.
    pub(crate) fn finish_record(self) -> (T, Record) {
        (self.t, self.record)
    }

    /// Keys read so far.
    pub(crate) const fn n_keys(&self) -> u32 {
        self.record.n_keys
    }

    /// Auxiliary variables made so far.
    pub(crate) fn n_aux(&self) -> u32 {
        u32::try_from(self.record.aux.len()).expect("fewer than 2^32 variables")
    }

    /// The form an element stands for.
    pub(crate) fn form(&self, s: Sym) -> Form {
        self.record.form(s)
    }

    /// The value an element holds, on the prover's side.
    fn value(&self, s: Sym) -> F192 {
        match s {
            Sym::Pub(c) => c,
            Sym::Hid(i) => self.values.as_ref().map_or(F192::ZERO, |v| v[i as usize]),
        }
    }

    /// A form's value, on the prover's side.
    fn eval(&self, f: &Form) -> F192 {
        (f.terms.iter()).fold(f.constant, |acc, &(v, c)| {
            acc + c * match v {
                Var::Key(i) => self.keys.get(i as usize).copied().unwrap_or(F192::ZERO),
                Var::Aux(j) => self.record.aux_values.get(j as usize).copied().unwrap_or(F192::ZERO),
            }
        })
    }

    /// Store a form: public when it has no term.
    fn push(&mut self, form: Form, value: impl FnOnce(&Self) -> F192) -> Sym {
        if form.terms.is_empty() {
            return Sym::Pub(form.constant);
        }
        if self.values.is_some() {
            let v = value(self);
            if let Some(values) = &mut self.values {
                values.push(v);
            }
        }
        let index = u32::try_from(self.record.forms.len()).expect("fewer than 2^32 forms");
        self.record.forms.push(form);
        Sym::Hid(index)
    }

    /// `ca·a + cb·b`.
    fn lin(&mut self, a: Sym, ca: F192, b: Sym, cb: F192) -> Sym {
        let (fa, fb) = match (a, b) {
            (Sym::Pub(x), Sym::Pub(y)) => return Sym::Pub(ca * x + cb * y),
            _ => (self.form_ref(a), self.form_ref(b)),
        };
        let mut terms = Vec::with_capacity(fa.1.len() + fb.1.len());
        let (mut i, mut j) = (0, 0);
        let (ta, tb) = (fa.1, fb.1);
        while i < ta.len() || j < tb.len() {
            let next = match (ta.get(i), tb.get(j)) {
                (Some(&(va, x)), Some(&(vb, _))) if va < vb => {
                    i += 1;
                    (va, ca * x)
                }
                (Some(&(va, _)), Some(&(vb, y))) if vb < va => {
                    j += 1;
                    (vb, cb * y)
                }
                (Some(&(v, x)), Some(&(_, y))) => {
                    i += 1;
                    j += 1;
                    (v, ca * x + cb * y)
                }
                (Some(&(v, x)), None) => {
                    i += 1;
                    (v, ca * x)
                }
                (None, Some(&(v, y))) => {
                    j += 1;
                    (v, cb * y)
                }
                (None, None) => unreachable!("one side has a term left"),
            };
            if next.1 != F192::ZERO {
                terms.push(next);
            }
        }
        let form = Form {
            constant: ca * fa.0 + cb * fb.0,
            terms,
        };
        self.push(form, |r| ca * r.value(a) + cb * r.value(b))
    }

    /// An element's constant and terms, borrowed.
    fn form_ref(&self, s: Sym) -> (F192, &[(Var, F192)]) {
        match s {
            Sym::Pub(c) => (c, &[]),
            Sym::Hid(i) => {
                let f = &self.record.forms[i as usize];
                (f.constant, &f.terms)
            }
        }
    }

    /// The auxiliary variable of this definition, made unless it exists: a monic form of it.
    fn aux(&mut self, kind: Kind, a: Form, b: Form) -> Sym {
        let mut h = Hasher::new();
        h.update(&[kind as u8]);
        h.update(&self.record.digest(&a));
        if kind == Kind::Product {
            h.update(&self.record.digest(&b));
        }
        let digest = h.finalize();
        let j = match self.by_digest.get(&digest) {
            Some(&j) => j,
            None => {
                let j = self.n_aux();
                if self.values.is_some() {
                    let v = match kind {
                        Kind::Product => self.eval(&a) * self.eval(&b),
                        Kind::Inverse => self.eval(&a).inv(),
                        Kind::Bind => self.eval(&a),
                    };
                    self.record.aux_values.push(v);
                }
                self.record.aux.push(Aux { kind, a, b, digest });
                self.by_digest.insert(digest, j);
                j
            }
        };
        let form = Form {
            constant: F192::ZERO,
            terms: vec![(Var::Aux(j), F192::ONE)],
        };
        self.push(form, |r| {
            r.record.aux_values.get(j as usize).copied().unwrap_or(F192::ZERO)
        })
    }

    /// Record a statement about a form, once.
    fn state(&mut self, f: Form, boolean: bool) {
        if self.values.is_some() {
            let v = self.eval(&f);
            let holds = if boolean { v * v == v } else { v == F192::ZERO };
            debug_assert!(holds, "the prover's own proof satisfies each constraint");
        }
        let mut h = Hasher::new();
        h.update(&[u8::from(boolean)]);
        h.update(&self.record.digest(&f));
        let digest = h.finalize();
        if self.stated.insert(digest) {
            let list = if boolean {
                &mut self.record.booleans
            } else {
                &mut self.record.linear
            };
            list.push((digest, f));
        }
    }

    /// Record that a hidden value is a bit: `b·b = b`.
    pub(crate) fn boolean(&mut self, b: Sym) {
        let f = self.form(b);
        assert!(!f.terms.is_empty(), "a bit the proof hides");
        self.state(f, true);
    }

    /// Whether every element is public, and their values.
    pub(crate) fn publics(xs: &[Sym]) -> Option<Vec<F192>> {
        xs.iter()
            .map(|&x| match x {
                Sym::Pub(c) => Some(c),
                Sym::Hid(_) => None,
            })
            .collect()
    }
}

impl<T> Arith for Recorder<T> {
    type E = Sym;

    fn constant(&mut self, c: F192) -> Sym {
        Sym::Pub(c)
    }

    fn mul_add(&mut self, a: Sym, b: Sym, d: Sym) -> Sym {
        match (a, b) {
            (Sym::Pub(x), Sym::Pub(y)) => self.lin(Sym::Pub(x * y), F192::ONE, d, F192::ONE),
            (Sym::Pub(x), h) | (h, Sym::Pub(x)) => self.lin(h, x, d, F192::ONE),
            (Sym::Hid(_), Sym::Hid(_)) => {
                let (la, ma) = self.record.monic(&self.form(a));
                let (lb, mb) = self.record.monic(&self.form(b));
                let (ma, mb) = if self.record.digest(&ma) <= self.record.digest(&mb) {
                    (ma, mb)
                } else {
                    (mb, ma)
                };
                let p = self.aux(Kind::Product, ma, mb);
                self.lin(p, la * lb, d, F192::ONE)
            }
        }
    }

    fn add(&mut self, a: Sym, d: Sym) -> Sym {
        self.lin(a, F192::ONE, d, F192::ONE)
    }

    fn mul_const_add(&mut self, a: Sym, c: F192, d: Sym) -> Sym {
        self.lin(a, c, d, F192::ONE)
    }

    fn inv(&mut self, a: Sym) -> Sym {
        match a {
            Sym::Pub(x) => Sym::Pub(if x.is_zero() { F192::ZERO } else { x.inv() }),
            Sym::Hid(_) => {
                let (la, ma) = self.record.monic(&self.form(a));
                let y = self.aux(Kind::Inverse, ma, Form::default());
                self.lin(y, la.inv(), Sym::Pub(F192::ZERO), F192::ONE)
            }
        }
    }

    fn frobenius2(&mut self, a: Sym) -> Sym {
        match a {
            Sym::Pub(x) => Sym::Pub(x.frobenius().frobenius()),
            Sym::Hid(_) => unreachable!("the verifier applies the Frobenius to public values only"),
        }
    }

    /// A hidden element gets a variable of its own, tied to its monic form by one linear constraint.
    fn bind(&mut self, a: Sym) -> Sym {
        match a {
            Sym::Pub(_) => a,
            Sym::Hid(_) => {
                let (la, ma) = self.record.monic(&self.form(a));
                let y = self.aux(Kind::Bind, ma, Form::default());
                self.lin(y, la, Sym::Pub(F192::ZERO), F192::ONE)
            }
        }
    }

    fn public_mle(&mut self, values: &[F64], point: &[Sym]) -> Sym {
        Self::publics(point).map_or_else(
            || {
                let eq = self.eq_table(point);
                let zero = self.zero();
                (eq.iter().zip(values)).fold(zero, |acc, (&e, &v)| self.mul_const_add(e, F192::from(v), acc))
            },
            |p| Sym::Pub(mle_eval_par(values, &p)),
        )
    }
}

impl<T> PublicColumns for Recorder<T> {}

impl<T: OpeningVerifier<E = F192, K = F64, Root = Hash, Query = usize>> Verifier for Recorder<T> {
    fn next_scalar(&mut self) -> Result<Sym, TranscriptError> {
        let c = self.t.next_scalar()?;
        if !self.hidden {
            return Ok(Sym::Pub(c));
        }
        let i = self.record.n_keys;
        self.record.n_keys += 1;
        let form = Form {
            constant: c,
            terms: vec![(Var::Key(i), F192::ONE)],
        };
        let key = self.keys.get(i as usize).copied().unwrap_or(F192::ZERO);
        Ok(self.push(form, |_| c + key))
    }

    fn next_round_poly(&mut self, n_coeffs: usize, claim: Sym, eq: Option<Sym>) -> Result<Vec<Sym>, TranscriptError> {
        assert!(n_coeffs >= 2, "a round polynomial has at least two coefficients");
        // The sent coefficients bind in index order, as the native reader binds them.
        let fixed = usize::from(eq.is_none());
        let mut coeffs = vec![Sym::Pub(F192::ZERO); n_coeffs];
        for i in (0..n_coeffs).filter(|&i| i != fixed) {
            coeffs[i] = self.next_scalar()?;
        }
        let zero = self.zero();
        let sum_from = |r: &mut Self, from: usize| coeffs[from..].iter().fold(zero, |acc, &c| r.add(acc, c));
        coeffs[fixed] = match eq {
            None => {
                let s = sum_from(self, 2);
                self.add(claim, s)
            }
            Some(r) => {
                let s = sum_from(self, 1);
                self.mul_add(r, s, claim)
            }
        };
        Ok(coeffs)
    }

    fn sample(&mut self) -> Sym {
        Sym::Pub(self.t.sample())
    }

    fn grind_check(&mut self, bits: u32) -> Result<(), TranscriptError> {
        self.t.grind_check(bits)
    }

    /// Equal values are checked; a hidden difference is one linear constraint, on its monic form.
    fn ensure_eq<Er>(&mut self, a: Sym, b: Sym, err: impl FnOnce() -> Er) -> Result<(), Er> {
        match self.add(a, b) {
            Sym::Pub(d) => {
                if d == F192::ZERO {
                    Ok(())
                } else {
                    Err(err())
                }
            }
            d @ Sym::Hid(_) => {
                let (_, monic) = self.record.monic(&self.form(d));
                self.state(monic, false);
                Ok(())
            }
        }
    }

    /// The proof goes on past the inner verifier's end: the outer proof and its opening follow, so the caller finishes.
    fn finish(&mut self) -> Result<(), TranscriptError> {
        Ok(())
    }

    fn set_hidden(&mut self, hidden: bool) {
        self.hidden = hidden;
    }

    fn sample_vec(&mut self, n: usize) -> Vec<Sym> {
        self.t.sample_vec(n).into_iter().map(Sym::Pub).collect()
    }
}

impl<T: OpeningVerifier<E = F192, K = F64, Root = Hash, Query = usize>> OpeningVerifier for Recorder<T> {
    type Root = Hash;
    type K = F64;
    type Query = usize;

    fn next_root(&mut self) -> Result<Hash, TranscriptError> {
        assert!(!self.hidden, "a root is never hidden");
        self.t.next_root()
    }

    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<usize> {
        self.t.sample_queries(depth, count)
    }

    fn open_rows(
        &mut self,
        root: &Hash,
        depth: usize,
        queries: &[usize],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<F64>>, TranscriptError> {
        self.t.open_rows(root, depth, queries, row_words, leaf_words)
    }

    fn mul_k_add(&mut self, a: Sym, k: F64, d: Sym) -> Sym {
        self.lin(a, F192::from(k), d, F192::ONE)
    }

    fn e_of_limbs(&mut self, limbs: [F64; 3]) -> Sym {
        Sym::Pub(F192::new(limbs[0].0, limbs[1].0, limbs[2].0))
    }

    fn query_point(&mut self, query: &usize) -> Sym {
        Sym::Pub(self.t.query_point(query))
    }
}
