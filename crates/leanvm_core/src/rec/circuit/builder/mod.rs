//! Circuit construction, wire equalities, constants, and public statements.

/// `$body`, recorded as the call `$call` when traced (`circuit-trace`) and called from outside the builder's methods.
macro_rules! traced {
    ($self:ident, $call:expr, $body:expr) => {{
        #[cfg(feature = "circuit-trace")]
        $self.begin(|| $call);
        let out = $body;
        #[cfg(feature = "circuit-trace")]
        $self.end();
        out
    }};
}

mod arith;
mod bits;
mod hash;

use super::{
    Assignment, Circuit, Compression, Dw, Ew, Finished, Kw, Limbs, PubSource, TableSlots, Unsatisfied, WireKind,
};
use crate::rec::table::{PerRecTable, Table};
use primitives::field::F192;
#[cfg(feature = "circuit-trace")]
use std::cell::RefCell;
use std::collections::HashMap;
#[cfg(feature = "circuit-trace")]
use std::fmt::Write;
use std::hash::{BuildHasherDefault, Hasher};

#[cfg(feature = "circuit-trace")]
thread_local! {
    /// The calls of every builder made while `traced` runs, one line each.
    static TRACE: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Run `f`, returning with its value the calls it made of every builder it created, in order: the methods called from outside a builder, one line each, their wires as numbers.
///
/// `CheckRec` replays them through the Lean model of the builder and checks the circuit is the one built here.
#[cfg(feature = "circuit-trace")]
pub(crate) fn traced<T>(f: impl FnOnce() -> T) -> (T, String) {
    TRACE.with(|t| *t.borrow_mut() = Some(String::new()));
    let out = f();
    let trace = TRACE.with(|t| t.borrow_mut().take()).unwrap_or_default();
    (out, trace)
}

/// A traced builder's calls so far, and how deep inside its own methods it is.
#[cfg(feature = "circuit-trace")]
#[derive(Debug, Default)]
struct Trace {
    depth: u32,
    out: String,
}

/// A list of numbers as its length, then its numbers.
#[cfg(feature = "circuit-trace")]
fn list(ws: impl ExactSizeIterator<Item = u32>) -> String {
    let mut s = ws.len().to_string();
    for w in ws {
        let _ = write!(s, " {w}");
    }
    s
}

/// Words as their numbers.
#[cfg(feature = "circuit-trace")]
fn numbers(ws: impl IntoIterator<Item = u64>) -> String {
    let mut s = String::new();
    for (i, w) in ws.into_iter().enumerate() {
        let _ = write!(s, "{}{w}", if i == 0 { "" } else { " " });
    }
    s
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

/// An arithmetic row's table and input wires as one key.
fn row_key(table: Table, inputs: [u32; 3]) -> u128 {
    (table as u128) << 96 | u128::from(inputs[0]) << 64 | u128::from(inputs[1]) << 32 | u128::from(inputs[2])
}

/// Hashes a row key: wire numbers the builder made, never adversarial, so two rounds of a 64-bit finalizer suffice.
#[derive(Default)]
struct RowHasher(u64);

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

    /// Each `EMUL` and `EXK` row's output by its `row_key`, `EMUL`'s two factors in order.
    arith: HashMap<u128, u32, BuildHasherDefault<RowHasher>>,

    /// Each hash row's compression.
    hash: Vec<Compression>,

    /// The statement's words.
    statement: Vec<Limbs>,

    /// The names the checks run under, outermost first.
    scope: Vec<String>,

    /// Failed checks collected with their enclosing scope names, the first few only.
    failures: Vec<Unsatisfied>,

    /// The calls made of it, when `traced` is running.
    #[cfg(feature = "circuit-trace")]
    trace: Option<Box<Trace>>,
}

impl Builder {
    /// How many failed checks are recorded by name: a forged proof can fail one per row.
    const RECORDED_FAILURES: usize = 64;

    /// An empty circuit.
    #[cfg_attr(not(feature = "circuit-trace"), allow(clippy::unnecessary_struct_initialization))]
    pub fn new() -> Self {
        Self {
            #[cfg(feature = "circuit-trace")]
            trace: TRACE.with(|t| t.borrow().is_some()).then(Box::default),
            ..Self::default()
        }
    }

    /// Record a call when traced and called from outside the builder's methods.
    #[cfg(feature = "circuit-trace")]
    fn begin(&mut self, call: impl FnOnce() -> String) {
        if let Some(t) = &mut self.trace {
            if t.depth == 0 {
                t.out.push_str(&call());
                t.out.push('\n');
            }
            t.depth += 1;
        }
    }

    /// Close a call.
    #[cfg(feature = "circuit-trace")]
    fn end(&mut self) {
        if let Some(t) = &mut self.trace {
            t.depth -= 1;
        }
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
        #[cfg(feature = "circuit-trace")]
        if let Some(t) = self.trace.take() {
            TRACE.with(|g| g.borrow_mut().as_mut().map(|g| g.push_str(&t.out)));
        }
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
        traced!(self, "free_e".into(), self.free_e_rows(value))
    }

    fn free_e_rows(&mut self, value: F192) -> Ew {
        Ew(self.wire(WireKind::E, [value.c0, value.c1, value.c2, 0]))
    }

    /// A free `K` value.
    pub fn free_k(&mut self, value: u64) -> Kw {
        traced!(self, "free_k".into(), self.free_k_rows(value))
    }

    fn free_k_rows(&mut self, value: u64) -> Kw {
        Kw(self.wire(WireKind::K, [value, 0, 0, 0]))
    }

    /// A free digest.
    pub fn free_d(&mut self, value: Limbs) -> Dw {
        traced!(self, "free_d".into(), self.free_d_rows(value))
    }

    fn free_d_rows(&mut self, value: Limbs) -> Dw {
        Dw(self.wire(WireKind::D, value))
    }

    /// Hold `a` and `b` equal.
    pub fn eq_e(&mut self, a: Ew, b: Ew) {
        traced!(self, format!("eq_e {} {}", a.0, b.0), self.eq_e_rows(a, b));
    }

    fn eq_e_rows(&mut self, a: Ew, b: Ew) {
        self.union(a.0, b.0);
    }

    /// Hold `a` and `b` equal.
    pub fn eq_k(&mut self, a: Kw, b: Kw) {
        traced!(self, format!("eq_k {} {}", a.0, b.0), self.eq_k_rows(a, b));
    }

    fn eq_k_rows(&mut self, a: Kw, b: Kw) {
        self.union(a.0, b.0);
    }

    /// Hold `a` and `b` equal.
    pub fn eq_d(&mut self, a: Dw, b: Dw) {
        traced!(self, format!("eq_d {} {}", a.0, b.0), self.eq_d_rows(a, b));
    }

    fn eq_d_rows(&mut self, a: Dw, b: Dw) {
        self.union(a.0, b.0);
    }

    /// Hold `a` to a constant.
    pub fn eq_e_const(&mut self, a: Ew, value: F192) {
        traced!(
            self,
            format!("eq_e_const {} {} {} {}", a.0, value.c0, value.c1, value.c2),
            self.eq_e_const_rows(a, value)
        );
    }

    fn eq_e_const_rows(&mut self, a: Ew, value: F192) {
        let c = self.e_const(value);
        self.eq_e(a, c);
    }

    /// Hold `a` to a constant.
    pub fn eq_k_const(&mut self, a: Kw, value: u64) {
        traced!(
            self,
            format!("eq_k_const {} {value}", a.0),
            self.eq_k_const_rows(a, value)
        );
    }

    fn eq_k_const_rows(&mut self, a: Kw, value: u64) {
        let c = self.k_const(value);
        self.eq_k(a, c);
    }

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
        traced!(
            self,
            format!("e_const {} {} {}", value.c0, value.c1, value.c2),
            self.e_const_rows(value)
        )
    }

    fn e_const_rows(&mut self, value: F192) -> Ew {
        Ew(self.constant(WireKind::E, [value.c0, value.c1, value.c2, 0]))
    }

    /// The constant `K` word `value`.
    pub fn k_const(&mut self, value: u64) -> Kw {
        traced!(self, format!("k_const {value}"), self.k_const_rows(value))
    }

    fn k_const_rows(&mut self, value: u64) -> Kw {
        Kw(self.constant(WireKind::K, [value, 0, 0, 0]))
    }

    /// The constant digest `value`.
    pub fn d_const(&mut self, value: Limbs) -> Dw {
        traced!(self, format!("d_const {}", numbers(value)), self.d_const_rows(value))
    }

    fn d_const_rows(&mut self, value: Limbs) -> Dw {
        Dw(self.constant(WireKind::D, value))
    }

    /// The constant zero of `E`.
    pub fn zero(&mut self) -> Ew {
        traced!(self, "zero".into(), self.zero_rows())
    }

    fn zero_rows(&mut self) -> Ew {
        self.units.e_zero.map_or_else(|| self.e_const(F192::ZERO), Ew)
    }

    /// The constant one of `E`.
    pub fn one(&mut self) -> Ew {
        traced!(self, "one".into(), self.one_rows())
    }

    fn one_rows(&mut self) -> Ew {
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
        traced!(self, format!("expose_e {}", w.0), self.expose_e_rows(w))
    }

    fn expose_e_rows(&mut self, w: Ew) -> usize {
        self.expose(w.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Builder {
        pub(crate) fn expose_k(&mut self, w: Kw) -> usize {
            self.expose(w.0)
        }

        pub(crate) fn expose_d(&mut self, w: Dw) -> usize {
            self.expose(w.0)
        }
    }
}
