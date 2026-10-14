//! The verifier over a padded transcript: its own code, its hidden values a linear graph over the keys.
//!
//! A zero-knowledge prover sends some scalars as `x + key`, each key used once.
//!
//! The recorder runs the verifier's code over such a transcript without knowing the keys:
//!
//! - a scalar read while hidden is the node `c + key_i`, `c` the value sent;
//! - a challenge, a root, a query and every public computation stay values of the inner verifier;
//! - a linear step on hidden values is one new node;
//! - a product or an inverse of hidden values is an auxiliary value, constrained by one row;
//! - an equality with a hidden side is one row, and so is a bit.
//!
//! The rows form a rank-one system over the keys, which the outer proof proves the keys satisfy.
//!
//! What it records depends on the transcript's shape alone, never on a value:
//!
//! - nodes, auxiliary values and rows are kept in the order they are made;
//! - nothing is merged, sorted or dropped by value.
//!
//! So the inner verifier may build rows of a circuit as well as check values, and both record the same system.

use fiat_shamir::arith::{Arith, PublicMle, Stage, Verifier};
use fiat_shamir::{TranscriptContext, TranscriptError};
use pcs::verifier::OpeningVerifier;
use pcs::whir::WhirError;
use primitives::field::{F64, F192};

/// An element as the recorder holds it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value<E> {
    /// A public value of the inner verifier.
    Public(E),
    /// A hidden value: a node of the record's graph.
    Hidden(Node),
}

impl<E> Value<E> {
    /// The value, if it is public.
    pub fn public(self) -> Option<E> {
        match self {
            Self::Public(x) => Some(x),
            Self::Hidden(_) => None,
        }
    }
}

/// A node of a record's graph: a hidden value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Node(u32);

/// What a node's term refers to.
#[derive(Clone, Copy, Debug)]
enum Ref {
    /// An earlier node.
    Node(u32),
    /// The key of the `i`-th hidden scalar.
    Key(u32),
    /// The `j`-th auxiliary value.
    Aux(u32),
}

/// A hidden value: a constant plus at most two weighted terms.
#[derive(Clone, Copy, Debug)]
struct NodeDef<E> {
    /// The constant part.
    constant: E,
    /// The terms, the second absent for a one-term node.
    terms: [Option<(Ref, E)>; 2],
}

/// One side of a constraint row.
#[derive(Clone, Copy, Debug)]
enum Operand<E> {
    /// A public value.
    Const(E),
    /// A hidden value.
    Node(u32),
    /// An auxiliary value.
    Aux(u32),
}

/// What an auxiliary value is of its node operands.
#[derive(Clone, Copy, Debug)]
enum AuxDef {
    /// `a * b`.
    Product(u32, u32),
    /// `1 / a`.
    Inverse(u32),
}

/// What the recorder recorded: a linear graph over the keys and auxiliary values, and the rows constraining them.
#[derive(Clone, Debug)]
pub struct Record<E> {
    /// Every node, in the order made.
    nodes: Vec<NodeDef<E>>,
    /// Every auxiliary value, in the order made.
    aux: Vec<AuxDef>,
    /// Every constraint row `A * B = C`, in the order made.
    rows: Vec<[Operand<E>; 3]>,
    /// Hidden scalars read.
    n_keys: u32,
}

/// A record's rows pulled back onto the keys.
///
/// ```text
///     sum_x (w_A[x] A_x + w_B[x] B_x + w_C[x] C_x)  =  constant + sum_i keys[i] key_i
/// ```
///
/// Key `i` is the hidden scalars' then the auxiliary values': auxiliary value `j` is key `n_keys + j`.
#[derive(Clone, Debug)]
pub(crate) struct KeyWeights<E> {
    /// The constant part.
    pub(crate) constant: E,
    /// Each key's weight, absent where it is zero.
    pub(crate) keys: Vec<Option<E>>,
}

/// Weights on a range of slots, each absent until something adds to it.
///
/// An absent weight is zero, and costs nothing when it is pulled back.
#[derive(Clone, Debug)]
pub(crate) struct SparseWeights<E>(Vec<Option<E>>);

impl<E: Copy> SparseWeights<E> {
    /// `n` absent weights.
    pub(crate) fn new(n: usize) -> Self {
        Self(vec![None; n])
    }

    /// Add `w` to slot `i`'s weight.
    pub(crate) fn add<A: Arith<E = E>>(&mut self, ar: &mut A, i: usize, w: E) {
        accumulate(ar, &mut self.0[i], w);
    }

    /// Slot `i`'s weight, absent where nothing was added.
    fn get(&self, i: usize) -> Option<E> {
        self.0[i]
    }

    /// Every slot's weight, in order.
    pub(crate) fn into_vec(self) -> Vec<Option<E>> {
        self.0
    }
}

/// Add `w` to an optional sum, which starts at `w` when absent.
fn accumulate<A: Arith>(ar: &mut A, sum: &mut Option<A::E>, w: A::E) {
    *sum = Some(sum.map_or(w, |s| ar.add(s, w)));
}

/// Every node's and auxiliary value's value, as the prover computes them from its keys.
#[derive(Clone, Debug)]
pub(crate) struct Evaluation {
    /// Each node's value.
    nodes: Vec<F192>,
    /// Each auxiliary value's value.
    aux: Vec<F192>,
}

impl Evaluation {
    /// Each auxiliary value's value, in the order made: what the prover sends for them.
    pub(crate) fn aux(&self) -> &[F192] {
        &self.aux
    }
}

impl<E: Copy> Record<E> {
    /// Hidden scalars read.
    pub(crate) const fn n_keys(&self) -> usize {
        self.n_keys as usize
    }

    /// Auxiliary values made.
    pub(crate) const fn n_aux(&self) -> usize {
        self.aux.len()
    }

    /// Constraint rows recorded.
    pub(crate) const fn n_rows(&self) -> usize {
        self.rows.len()
    }

    /// Pull the rows' weights back onto the keys, auxiliary value `j` being `sent[j]` plus its key.
    ///
    /// Each node and each edge of the graph costs one product: the pass is linear in the record.
    ///
    /// # Panics
    ///
    /// Panics unless there is a weight per row on each side, and a sent value per auxiliary value.
    pub(crate) fn weigh<A: Arith<E = E>>(&self, ar: &mut A, sides: [&[E]; 3], sent: &[E]) -> KeyWeights<E> {
        assert!(sides.iter().all(|w| w.len() == self.rows.len()), "a weight per row");
        assert_eq!(sent.len(), self.aux.len(), "a sent value per auxiliary value");
        let mut acc = Accumulator {
            constant: None,
            nodes: SparseWeights::new(self.nodes.len()),
            keys: SparseWeights::new(self.n_keys() + self.n_aux()),
            n_keys: self.n_keys(),
            sent,
        };

        // Phase 1: each row side's weight onto what it refers to.
        for (x, row) in self.rows.iter().enumerate() {
            for (side, weights) in row.iter().zip(sides) {
                acc.add_operand(ar, *side, weights[x]);
            }
        }

        // Phase 2: each node's weight onto its constant and its terms, latest node first.
        //
        // Why latest first: a node's terms refer to earlier nodes, so every weight on a node is final when it is reached.
        for (n, node) in self.nodes.iter().enumerate().rev() {
            let Some(w) = acc.nodes.get(n) else {
                continue;
            };
            let c = ar.mul(w, node.constant);
            acc.add_constant(ar, c);
            for &(r, coefficient) in node.terms.iter().flatten() {
                let wc = ar.mul(w, coefficient);
                acc.add_ref(ar, r, wc);
            }
        }

        let constant = acc.constant.unwrap_or_else(|| ar.zero());
        KeyWeights {
            constant,
            keys: acc.keys.into_vec(),
        }
    }
}

/// The weights a pull-back accumulates.
struct Accumulator<'s, E> {
    /// The constant's weight.
    constant: Option<E>,
    /// Each node's weight.
    nodes: SparseWeights<E>,
    /// Each key's weight.
    keys: SparseWeights<E>,
    /// Hidden scalars read: auxiliary value `j` is key `n_keys + j`.
    n_keys: usize,
    /// The value sent for each auxiliary value.
    sent: &'s [E],
}

impl<E: Copy> Accumulator<'_, E> {
    /// Add `w` to the constant's weight.
    fn add_constant<A: Arith<E = E>>(&mut self, ar: &mut A, w: E) {
        accumulate(ar, &mut self.constant, w);
    }

    /// Add `w` to auxiliary value `j`, which is the value sent for it plus its key.
    fn add_aux<A: Arith<E = E>>(&mut self, ar: &mut A, j: usize, w: E) {
        let c = ar.mul(w, self.sent[j]);
        self.add_constant(ar, c);
        self.keys.add(ar, self.n_keys + j, w);
    }

    /// Add `w` to what a node's term refers to.
    fn add_ref<A: Arith<E = E>>(&mut self, ar: &mut A, r: Ref, w: E) {
        match r {
            Ref::Node(n) => self.nodes.add(ar, n as usize, w),
            Ref::Key(i) => self.keys.add(ar, i as usize, w),
            Ref::Aux(j) => self.add_aux(ar, j as usize, w),
        }
    }

    /// Add `w` to what one side of a row refers to.
    fn add_operand<A: Arith<E = E>>(&mut self, ar: &mut A, operand: Operand<E>, w: E) {
        match operand {
            Operand::Const(c) => {
                let wc = ar.mul(w, c);
                self.add_constant(ar, wc);
            }
            Operand::Node(n) => self.nodes.add(ar, n as usize, w),
            Operand::Aux(j) => self.add_aux(ar, j as usize, w),
        }
    }
}

impl Record<F192> {
    /// Every node's and auxiliary value's value, from the keys of the hidden scalars.
    ///
    /// # Panics
    ///
    /// Panics with fewer keys than hidden scalars read.
    pub(crate) fn evaluate(&self, keys: &[F192]) -> Evaluation {
        assert!(keys.len() >= self.n_keys(), "a key per hidden scalar");
        let mut values = Evaluation {
            nodes: Vec::with_capacity(self.nodes.len()),
            aux: Vec::with_capacity(self.aux.len()),
        };
        // Nodes and auxiliary values interleave in the order made, each reading only earlier ones.
        for node in &self.nodes {
            let mut v = node.constant;
            for &(r, c) in node.terms.iter().flatten() {
                let x = match r {
                    Ref::Node(n) => values.nodes[n as usize],
                    Ref::Key(i) => keys[i as usize],
                    Ref::Aux(j) => self.aux_value(&mut values, j as usize),
                };
                v += c * x;
            }
            values.nodes.push(v);
        }
        // An auxiliary value no node refers to is still a row's.
        if !self.aux.is_empty() {
            self.aux_value(&mut values, self.aux.len() - 1);
        }
        values
    }

    /// Auxiliary value `j`, computing every one before it first.
    fn aux_value(&self, values: &mut Evaluation, j: usize) -> F192 {
        while values.aux.len() <= j {
            let v = match self.aux[values.aux.len()] {
                AuxDef::Product(a, b) => values.nodes[a as usize] * values.nodes[b as usize],
                AuxDef::Inverse(a) => values.nodes[a as usize].inv(),
            };
            values.aux.push(v);
        }
        values.aux[j]
    }

    /// Each row's three sides' values.
    pub(crate) fn sides(&self, values: &Evaluation) -> [Vec<F192>; 3] {
        std::array::from_fn(|side| {
            (self.rows.iter())
                .map(|row| match row[side] {
                    Operand::Const(c) => c,
                    Operand::Node(n) => values.nodes[n as usize],
                    Operand::Aux(j) => values.aux[j as usize],
                })
                .collect()
        })
    }
}

/// The verifier's arithmetic and transcript over a padded proof, read through an inner verifier.
pub struct Recorder<V: Arith> {
    /// The inner verifier: it reads the proof and holds every public value.
    inner: V,
    /// What is recorded.
    record: Record<V::E>,
    /// Whether the next prover message is hidden.
    hidden: bool,
    /// The inner verifier's zero.
    zero: V::E,
    /// The inner verifier's one.
    one: V::E,
}

impl<V: Arith> Recorder<V> {
    /// A recorder over an inner verifier, hiding nothing until told.
    pub fn new(mut inner: V) -> Self {
        let (zero, one) = (inner.zero(), inner.one());
        Self {
            inner,
            record: Record {
                nodes: Vec::new(),
                aux: Vec::new(),
                rows: Vec::new(),
                n_keys: 0,
            },
            hidden: false,
            zero,
            one,
        }
    }

    /// The inner verifier, to read public messages directly.
    pub const fn inner(&mut self) -> &mut V {
        &mut self.inner
    }

    /// The inner verifier back, and what was recorded.
    pub fn finish(self) -> (V, Record<V::E>) {
        (self.inner, self.record)
    }

    /// A new node.
    fn node(&mut self, constant: V::E, first: (Ref, V::E), second: Option<(Ref, V::E)>) -> Value<V::E> {
        let index = u32::try_from(self.record.nodes.len()).expect("fewer than 2^32 nodes");
        self.record.nodes.push(NodeDef {
            constant,
            terms: [Some(first), second],
        });
        Value::Hidden(Node(index))
    }

    /// `ca * a + cb * b`.
    fn lin(&mut self, a: Value<V::E>, ca: V::E, b: Value<V::E>, cb: V::E) -> Value<V::E> {
        match (a, b) {
            (Value::Public(x), Value::Public(y)) => {
                let t = self.inner.mul(cb, y);
                Value::Public(self.inner.mul_add(ca, x, t))
            }
            (Value::Hidden(Node(n)), Value::Public(y)) => {
                let c = self.inner.mul(cb, y);
                self.node(c, (Ref::Node(n), ca), None)
            }
            (Value::Public(x), Value::Hidden(Node(n))) => {
                let c = self.inner.mul(ca, x);
                self.node(c, (Ref::Node(n), cb), None)
            }
            (Value::Hidden(Node(n)), Value::Hidden(Node(m))) => {
                self.node(self.zero, (Ref::Node(n), ca), Some((Ref::Node(m), cb)))
            }
        }
    }

    /// A new auxiliary value: its definition, its row, and the node holding it.
    fn aux(&mut self, def: AuxDef) -> Value<V::E> {
        let j = u32::try_from(self.record.aux.len()).expect("fewer than 2^32 auxiliary values");
        let row = match def {
            AuxDef::Product(a, b) => [Operand::Node(a), Operand::Node(b), Operand::Aux(j)],
            AuxDef::Inverse(a) => [Operand::Node(a), Operand::Aux(j), Operand::Const(self.one)],
        };
        self.record.aux.push(def);
        self.record.rows.push(row);
        self.node(self.zero, (Ref::Aux(j), self.one), None)
    }

    /// Check that a value is a bit: the row `b * b = b`, or the inner verifier's check of a public one.
    pub fn ensure_bit<Er>(&mut self, b: Value<V::E>, err: impl FnOnce() -> Er) -> Result<(), Er>
    where
        V: Verifier,
    {
        match b {
            Value::Public(x) => {
                let square = self.inner.mul(x, x);
                self.inner.ensure_eq(square, x, err)
            }
            Value::Hidden(Node(n)) => {
                self.record.rows.push([Operand::Node(n); 3]);
                Ok(())
            }
        }
    }
}

impl<V: Arith> Arith for Recorder<V> {
    type E = Value<V::E>;

    fn constant(&mut self, c: F192) -> Self::E {
        Value::Public(self.inner.constant(c))
    }

    fn mul_add(&mut self, a: Self::E, b: Self::E, d: Self::E) -> Self::E {
        let one = self.one;
        match (a, b) {
            (Value::Public(x), Value::Public(y)) => match d {
                Value::Public(z) => Value::Public(self.inner.mul_add(x, y, z)),
                Value::Hidden(_) => {
                    let p = self.inner.mul(x, y);
                    self.lin(Value::Public(p), one, d, one)
                }
            },
            (Value::Public(x), h @ Value::Hidden(_)) | (h @ Value::Hidden(_), Value::Public(x)) => {
                self.lin(h, x, d, one)
            }
            (Value::Hidden(Node(n)), Value::Hidden(Node(m))) => {
                let p = self.aux(AuxDef::Product(n, m));
                self.lin(p, one, d, one)
            }
        }
    }

    fn add(&mut self, a: Self::E, d: Self::E) -> Self::E {
        let one = self.one;
        self.lin(a, one, d, one)
    }

    fn mul_const_add(&mut self, a: Self::E, c: F192, d: Self::E) -> Self::E {
        match (a, d) {
            (Value::Public(x), Value::Public(y)) => Value::Public(self.inner.mul_const_add(x, c, y)),
            _ => {
                let (c, one) = (self.inner.constant(c), self.one);
                self.lin(a, c, d, one)
            }
        }
    }

    /// The inverse of a hidden value is an auxiliary value `v` with `a * v = 1`.
    ///
    /// The native verifier takes the inverse of zero as zero, which no `v` satisfies here.
    /// So a hidden zero cannot be inverted: the verifier inverts challenges alone.
    fn inv(&mut self, a: Self::E) -> Self::E {
        match a {
            Value::Public(x) => Value::Public(self.inner.inv(x)),
            Value::Hidden(Node(n)) => self.aux(AuxDef::Inverse(n)),
        }
    }

    fn frobenius2(&mut self, a: Self::E) -> Self::E {
        match a {
            Value::Public(x) => Value::Public(self.inner.frobenius2(x)),
            Value::Hidden(_) => unreachable!("the verifier applies the Frobenius map to challenges alone"),
        }
    }
}

impl<V: PublicMle> PublicMle for Recorder<V> {
    fn public_mle(&mut self, values: &[F64], point: &[Self::E]) -> Self::E {
        match point.iter().map(|&x| x.public()).collect::<Option<Vec<_>>>() {
            Some(point) => Value::Public(self.inner.public_mle(values, &point)),
            None => {
                let eq = self.eq_table(point);
                let zero = self.zero();
                (eq.iter().zip(values)).fold(zero, |acc, (&e, &v)| self.mul_const_add(e, F192::from(v), acc))
            }
        }
    }
}

impl<V: Verifier> Verifier for Recorder<V> {
    fn prover_message(&mut self) -> Result<Self::E, TranscriptError> {
        let c = self.inner.prover_message()?;
        if !self.hidden {
            return Ok(Value::Public(c));
        }
        // A hidden scalar is the value sent plus its key.
        let i = self.record.n_keys;
        self.record.n_keys += 1;
        Ok(self.node(c, (Ref::Key(i), self.one), None))
    }

    fn verifier_message(&mut self) -> Self::E {
        Value::Public(self.inner.verifier_message())
    }

    fn check_pow(&mut self, bits: u32) -> Result<(), TranscriptError> {
        self.inner.check_pow(bits)
    }

    /// Two public values are checked by the inner verifier.
    ///
    /// A hidden difference is the row `d * 1 = 0`.
    fn ensure_eq<Er>(&mut self, a: Self::E, b: Self::E, err: impl FnOnce() -> Er) -> Result<(), Er> {
        match (a, b) {
            (Value::Public(x), Value::Public(y)) => self.inner.ensure_eq(x, y, err),
            _ => {
                let Value::Hidden(Node(n)) = self.add(a, b) else {
                    unreachable!("a sum with a hidden term is hidden")
                };
                let row = [Operand::Node(n), Operand::Const(self.one), Operand::Const(self.zero)];
                self.record.rows.push(row);
                Ok(())
            }
        }
    }

    /// The outer proof follows the recorded verifier, so the caller checks the proof's end.
    fn check_eof(&mut self) -> Result<(), TranscriptError> {
        Ok(())
    }

    fn set_hidden(&mut self, hidden: bool) {
        self.hidden = hidden;
    }

    fn is_hidden(&self) -> bool {
        self.hidden
    }

    fn begin_scope(&mut self, stage: Stage) {
        self.inner.begin_scope(stage);
    }

    fn end_scope(&mut self) {
        self.inner.end_scope();
    }
}

impl<V: OpeningVerifier> OpeningVerifier for Recorder<V> {
    type Root = V::Root;
    type K = V::K;
    type Query = V::Query;

    fn context(&mut self) -> TranscriptContext<Self::K, Self::Root> {
        self.inner.context()
    }

    fn zero_k(&mut self) -> Self::K {
        self.inner.zero_k()
    }

    fn ensure_root_eq(&mut self, actual: Self::Root, expected: Self::Root) -> Result<(), WhirError> {
        self.inner.ensure_root_eq(actual, expected)
    }

    /// # Panics
    ///
    /// Panics while hiding is on: a root is never hidden.
    fn next_root(&mut self) -> Result<Self::Root, TranscriptError> {
        assert!(!self.hidden, "a root is never hidden");
        self.inner.next_root()
    }

    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<Self::Query> {
        self.inner.sample_queries(depth, count)
    }

    fn open_rows(
        &mut self,
        root: &Self::Root,
        depth: usize,
        queries: &[Self::Query],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<Self::K>>, TranscriptError> {
        self.inner.open_rows(root, depth, queries, row_words, leaf_words)
    }

    fn mul_k_add(&mut self, a: Self::E, k: Self::K, d: Self::E) -> Self::E {
        match (a, d) {
            (Value::Public(x), Value::Public(y)) => Value::Public(self.inner.mul_k_add(x, k, y)),
            _ => {
                let (zero, one) = (self.zero, self.one);
                let k = self.inner.mul_k_add(one, k, zero);
                self.lin(a, k, d, one)
            }
        }
    }

    fn e_of_limbs(&mut self, limbs: [Self::K; 3]) -> Self::E {
        Value::Public(self.inner.e_of_limbs(limbs))
    }

    fn query_point(&mut self, query: &Self::Query) -> Self::E {
        Value::Public(self.inner.query_point(query))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::arith::Native;
    use fiat_shamir::{ProverState, SessionId, VerifierState};
    use primitives::test_util::Rng;

    #[test]
    fn the_pulled_back_weights_are_the_weighted_rows() {
        // Invariant: for any row weights w, the keys' weights t and the constant c satisfy
        //
        //     sum_x (w_A[x] A_x + w_B[x] B_x + w_C[x] C_x)  =  c + sum_i t_i key_i
        //
        // on the values the keys give, auxiliary values being what was sent plus their keys.
        let mut rng = Rng::new(0xAB);
        let session = SessionId::new(b"record-test");
        let keys = rng.ext_vec(40);

        // A transcript of 20 hidden scalars, products, inverses, sums, checks and a bit over them.
        let mut ps = ProverState::new(&session, &0u64);
        ps.set_keys(keys.clone());
        ps.set_hidden(true);
        ps.prover_messages(&rng.ext_vec(20));
        let proof = ps.into_proof();
        let mut rec = Recorder::new(VerifierState::new(&session, &0u64, &proof));
        rec.set_hidden(true);
        let xs: Vec<_> = (0..20).map(|_| rec.prover_message().unwrap()).collect();
        let mut acc = xs[0];
        for (i, &x) in xs.iter().enumerate().skip(1) {
            let c = rec.verifier_message();
            acc = match i % 3 {
                0 => rec.mul_add(acc, x, c),
                1 => rec.mul_add(c, x, acc),
                _ => {
                    let inv = rec.inv(x);
                    rec.add(acc, inv)
                }
            };
            let _ = rec.ensure_eq(acc, x, || ());
        }
        let _ = rec.ensure_bit(xs[3], || ());
        let (_, record) = rec.finish();

        // The prover's values, the values sent for the auxiliary values, and the rows' sides.
        let values = record.evaluate(&keys);
        let sent: Vec<F192> = (values.aux().iter().zip(&keys[record.n_keys()..]))
            .map(|(&v, &k)| v + k)
            .collect();
        let sides = record.sides(&values);

        // Random row weights, pulled back, against the weighted rows evaluated directly.
        let w: [Vec<F192>; 3] = std::array::from_fn(|_| rng.ext_vec(record.n_rows()));
        let pulled = record.weigh(&mut Native, [&w[0], &w[1], &w[2]], &sent);
        let direct = (0..record.n_rows()).fold(F192::ZERO, |acc, x| {
            acc + w[0][x] * sides[0][x] + w[1][x] * sides[1][x] + w[2][x] * sides[2][x]
        });
        let by_keys =
            (pulled.keys.iter().zip(&keys)).fold(pulled.constant, |acc, (t, &k)| acc + t.map_or(F192::ZERO, |t| t * k));
        assert_eq!(direct, by_keys);
    }
}
