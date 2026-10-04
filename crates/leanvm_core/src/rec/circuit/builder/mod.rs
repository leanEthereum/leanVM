//! Circuit construction, wire equalities, constants, and public statements.

mod arith;
mod bits;
mod hash;

use super::{Assignment, Circuit, Compression, Dw, Ew, Finished, Kind, Kw, Limbs, PubSource, Rows};
use crate::rec::table::Table;
use primitives::field::F192;
use std::collections::HashMap;

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

/// Builds circuit rows and records an honest assignment to their wires.
///
/// Arithmetic identities involving constant zero or one can avoid emitting rows.
/// Folding depends on circuit constants, never on the values of unconstrained wires.
#[derive(Debug, Default)]
pub struct Builder {
    /// Each wire's value.
    values: Vec<Limbs>,

    /// Each wire's kind.
    kinds: Vec<Kind>,

    /// Parent wire in each equality class, with roots pointing to themselves.
    parent: Vec<u32>,

    /// Wire numbers for every table row and slot.
    rows: Rows,

    /// Sources of public row values, in insertion order.
    pubs: Vec<PubSource>,

    /// Deduplicated constant wires, keyed by kind and padded value.
    consts: HashMap<(Kind, Limbs), u32>,

    /// Cached arithmetic identities used to fold operations.
    units: Units,

    /// Each hash row's compression.
    hash: Vec<Compression>,

    /// The statement's words.
    statement: Vec<Limbs>,

    /// The names the checks run under, outermost first.
    scope: Vec<String>,

    /// Failed checks collected with their enclosing scope names.
    failures: Vec<String>,
}

impl Builder {
    /// An empty circuit.
    pub fn new() -> Self {
        Self::default()
    }

    /// Run `f` under a name, which an equality that fails reports.
    pub fn scope<T>(&mut self, name: impl Into<String>, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scope.push(name.into());
        let out = f(self);
        self.scope.pop();
        out
    }

    /// Record a check that failed on the values and that no equality expresses.
    pub fn fail(&mut self, what: &str) {
        if self.failures.len() < 64 {
            self.failures.push(format!("{}: {what}", self.scope.join(" / ")));
        }
    }

    /// The circuit, its values, and the checks that failed on them.
    ///
    /// A wire class is numbered by its first slot, so a circuit is the same however it was built.
    pub fn finish(mut self) -> Finished {
        let (wires, pubs) = self.statement_first();
        let mut number = vec![u32::MAX; self.values.len()];
        let mut n_classes = 0;
        let classes = wires.map(|w| {
            let root = self.find(w) as usize;
            if number[root] == u32::MAX {
                number[root] = n_classes;
                n_classes += 1;
            }
            number[root]
        });
        let circuit = Circuit {
            classes,
            pubs,
            statement_len: self.statement.len(),
            floor: [0; Table::COUNT],
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
    fn statement_first(&mut self) -> (Rows, Vec<PubSource>) {
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

    fn wire(&mut self, kind: Kind, value: Limbs) -> u32 {
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

    fn union(&mut self, a: u32, b: u32) {
        if self.values[a as usize] != self.values[b as usize] {
            self.fail("unequal wires");
        }
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[rb as usize] = ra;
        }
    }

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
        Ew(self.wire(Kind::E, [value.c0, value.c1, value.c2, 0]))
    }

    /// A free `K` value.
    pub fn free_k(&mut self, value: u64) -> Kw {
        Kw(self.wire(Kind::K, [value, 0, 0, 0]))
    }

    /// A free digest.
    pub fn free_d(&mut self, value: Limbs) -> Dw {
        Dw(self.wire(Kind::D, value))
    }

    /// Hold `a` and `b` equal.
    pub fn eq_e(&mut self, a: Ew, b: Ew) {
        self.union(a.0, b.0);
    }

    /// Hold `a` and `b` equal.
    pub fn eq_k(&mut self, a: Kw, b: Kw) {
        self.union(a.0, b.0);
    }

    /// Hold `a` and `b` equal.
    pub fn eq_d(&mut self, a: Dw, b: Dw) {
        self.union(a.0, b.0);
    }

    /// Hold `a` to a constant.
    pub fn eq_e_const(&mut self, a: Ew, value: F192) {
        let c = self.e_const(value);
        self.eq_e(a, c);
    }

    /// Hold `a` to a constant.
    pub fn eq_k_const(&mut self, a: Kw, value: u64) {
        let c = self.k_const(value);
        self.eq_k(a, c);
    }

    fn constant(&mut self, kind: Kind, value: Limbs) -> u32 {
        if let Some(&w) = self.consts.get(&(kind, value)) {
            return w;
        }
        let w = self.wire(kind, value);
        self.pubs.push(PubSource::Const(value));
        self.row(Table::Pub, &[w]);
        self.consts.insert((kind, value), w);
        let unit = match (kind, value) {
            (Kind::E, [0, 0, 0, 0]) => &mut self.units.e_zero,
            (Kind::E, [1, 0, 0, 0]) => &mut self.units.e_one,
            (Kind::K, [0, 0, 0, 0]) => &mut self.units.k_zero,
            (Kind::K, [1, 0, 0, 0]) => &mut self.units.k_one,
            _ => return w,
        };
        *unit = Some(w);
        w
    }

    /// An extension-field wire bound to a public constant.
    ///
    /// Its three coefficients occupy the first three words, with the fourth word zero.
    pub fn e_const(&mut self, value: F192) -> Ew {
        Ew(self.constant(Kind::E, [value.c0, value.c1, value.c2, 0]))
    }

    /// The constant `K` word `value`.
    pub fn k_const(&mut self, value: u64) -> Kw {
        Kw(self.constant(Kind::K, [value, 0, 0, 0]))
    }

    /// The constant digest `value`.
    pub fn d_const(&mut self, value: Limbs) -> Dw {
        Dw(self.constant(Kind::D, value))
    }

    /// The constant zero of `E`.
    pub fn zero(&mut self) -> Ew {
        self.units.e_zero.map_or_else(|| self.e_const(F192::ZERO), Ew)
    }

    /// The constant one of `E`.
    pub fn one(&mut self) -> Ew {
        self.units.e_one.map_or_else(|| self.e_const(F192::ONE), Ew)
    }

    fn k_zero(&mut self) -> Kw {
        self.units.k_zero.map_or_else(|| self.k_const(0), Kw)
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

    /// Make `w` a word of the statement.
    pub fn expose_k(&mut self, w: Kw) -> usize {
        self.expose(w.0)
    }

    /// Make `w` a word of the statement.
    pub fn expose_d(&mut self, w: Dw) -> usize {
        self.expose(w.0)
    }
}
