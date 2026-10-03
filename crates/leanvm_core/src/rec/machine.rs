//! The recursion machine's tables as the proof sees them: each table's columns, the tuple each slot carries on
//! the bus, and the identities its rows satisfy.
//!
//! Every slot of row `z` carries `(key, v0, v1, v2, v3)`: it pulls the tuple at its own key `gid << 32 | z`
//! (`gid` the slot's index among all tables' slots, an integer index column) and pushes it at `next`, a public
//! column holding the key of the next slot of its wire's class. The slots of a class, in table, row and slot
//! order, form one cycle, so the bus balances exactly when they all carry one value. A padding row's `next` is
//! its own key, which cancels whatever it carries.
//!
//! The `Hash` table's words are ports of its rows' packed BLAKE2s witnesses, which flock proves; the `Pub`
//! table commits nothing, its blocks being the framework's.

use super::circuit::{Assignment, Circuit, Limbs, N_TABLES, PubSource, Table};
use crate::class_flock;
use crate::colval::ColVal;
use crate::constraints;
use crate::leaf::{Block, BusForm, Coord};
use crate::tables::{self, Part};
use flock::circuit::Circuit as FlockCircuit;
use primitives::field::{F64, F192};
use std::sync::Arc;

/// The tables owning columns: every table but `Pub`, which comes last.
pub const N_OWNED: usize = N_TABLES - 1;
const _: () = assert!(Table::Pub as usize == N_OWNED);

/// The ports of a hash row's packed witness its table reads: the inputs `t`, `f`, `h0..h3`, `m0..m7`, then
/// the outputs `o0..o3`, at the witness's words `0..18`.
pub const N_PORTS: usize = 18;
const T: usize = 0;
const F: usize = 1;
const H: usize = 2;
const M: usize = 6;
const O: usize = 14;
/// The `Hash` table's selector column, after its ports.
const SEL: usize = N_PORTS;

/// How many columns table `t` has, its ports first.
pub const fn n_cols(t: Table) -> usize {
    match t {
        Table::Emul => 9,
        Table::Exk => 7,
        Table::Hash => N_PORTS + 1,
        Table::Split => 65,
        Table::Cast => 4,
        Table::Pub => 0,
    }
}

/// How many of table `t`'s columns are ports of its packed witness: its first.
pub const fn n_ports(t: Table) -> usize {
    if matches!(t, Table::Hash) { N_PORTS } else { 0 }
}

/// The packed witness index of the HASH class circuit, which proves every hash row.
pub fn hash_flock() -> usize {
    let t = tables::table_of(crate::rv::Class::Hash).expect("the HASH class has a table");
    class_flock::flock_index(t, Part::Class)
}

/// The BLAKE2s compression circuit.
pub fn hash_circuit() -> &'static FlockCircuit {
    class_flock::circuit(hash_flock())
}

/// `log2` of a hash row's packed words: the stride between consecutive rows' same-port words.
pub fn hash_stride_log() -> usize {
    class_flock::stride_log(&tables::HASH, Part::Class)
}

/// `log2` of table `t`'s height for `rows` rows: a power of two, at flock's floor for the `Hash` table.
pub fn log_rows(t: Table, rows: usize) -> usize {
    if t == Table::Hash {
        flock::reduction::min_n_blocks_log(rows.max(1))
            .max(class_flock::MIN_CUBE_LOG.saturating_sub(tables::HASH.k_log))
    } else {
        crate::log2_ceil_usize(rows.max(1))
    }
}

/// The value limbs slot `s` of table `t` carries, over the table's local columns.
pub fn slot(t: Table, s: usize) -> [Coord; 4] {
    use Coord::{Col, Prod, Sum};
    let zero = || Coord::Const(F64::ZERO);
    let k = |c: usize| [Col(c), zero(), zero(), zero()];
    let e = |c: usize| [Col(c), Col(c + 1), Col(c + 2), zero()];
    let d = |c: usize| [Col(c), Col(c + 1), Col(c + 2), Col(c + 3)];
    match (t, s) {
        (Table::Emul, 0) => e(0),
        (Table::Emul, 1) => e(3),
        (Table::Emul, 2) => e(6),
        // `a·b + d` modulo `y^3 + y + 1`: `p_i = Σ_{j+l=i} a_j·b_l`, `y^3 = y + 1`, `y^4 = y^2 + y`.
        (Table::Emul, 3) => {
            let p = |i: usize| -> Vec<Coord> {
                (0..3)
                    .filter(|&j| i >= j && i - j < 3)
                    .map(|j| Prod(j, 3 + i - j))
                    .collect()
            };
            let limb = |parts: &[usize], d: usize| Sum(parts.iter().flat_map(|&i| p(i)).chain([Col(d)]).collect());
            [limb(&[0, 3], 6), limb(&[1, 3, 4], 7), limb(&[2, 4], 8), zero()]
        }
        (Table::Exk, 0) => e(0),
        (Table::Exk, 1) => k(3),
        (Table::Exk, 2) => e(4),
        (Table::Exk, 3) => [
            Sum(vec![Prod(0, 3), Col(4)]),
            Sum(vec![Prod(1, 3), Col(5)]),
            Sum(vec![Prod(2, 3), Col(6)]),
            zero(),
        ],
        (Table::Hash, _) => match s {
            0 => d(H),
            1 => [Col(T), Col(F), zero(), zero()],
            // The Merkle mux: the message's left half at `b = 0`, its right half at `b = 1`.
            2 => std::array::from_fn(|i| Sum(vec![Col(M + i), Prod(SEL, M + i), Prod(SEL, M + 4 + i)])),
            3 => k(SEL),
            4 => e(M + 4),
            5 => k(M + 7),
            6 => d(O),
            7 => e(O),
            8..16 => k(M + s - 8),
            _ => unreachable!("{t:?} has no slot {s}"),
        },
        (Table::Split, _) => k(s),
        (Table::Cast, 0) => d(0),
        (Table::Cast, 1) => e(0),
        (Table::Cast, 2) => [Col(0), Col(1), zero(), zero()],
        (Table::Cast, 3) => [Col(2), Col(3), zero(), zero()],
        (Table::Cast, 4..=7) => k(s - 4),
        _ => unreachable!("{t:?} has no slot {s}"),
    }
}

/// The identities table `t`'s rows satisfy, each a degree-two form over its local columns that vanishes.
pub fn identities(t: Table) -> Vec<BusForm> {
    let n = n_cols(t);
    let form = |linear: &[(usize, F192)], prods: Vec<(usize, usize, F192)>, constant: u64| {
        let mut coeffs = vec![F192::ZERO; n];
        for &(c, w) in linear {
            coeffs[c] += w;
        }
        BusForm {
            coeffs,
            prods,
            constant: F192::from(F64(constant)),
        }
    };
    let boolean = |c: usize| form(&[(c, F192::ONE)], vec![(c, c, F192::ONE)], 0);
    match t {
        // A Boolean selector; what a hash row hashes from is its wiring's.
        Table::Hash => vec![boolean(SEL)],
        // A word is its bits, each Boolean.
        Table::Split => {
            let mut word = vec![(0, F192::ONE)];
            word.extend((0..64).map(|i| (1 + i, F192::from(F64(1 << i)))));
            std::iter::once(form(&word, vec![], 0))
                .chain((1..65).map(boolean))
                .collect()
        }
        _ => Vec::new(),
    }
}

/// A table's whole summand in the constraint batch: its bus forms and its identities, already weighted.
pub struct Summand(BusForm);

impl constraints::Summand for Summand {
    #[inline(always)]
    fn eval<V: ColVal>(&self, cols: &[V], quadratic: bool) -> F192 {
        V::reduce(self.0.eval_unreduced(cols, quadratic))
    }
}

/// Each owned table's summand: its push and pull forms weighted `1` and `xi`, then its identities, each with
/// a power of `xi` of its own from `xi^2`, the tables' ranges disjoint.
pub fn summands(forms: &[Vec<BusForm>; 2], xi: F192) -> Vec<Summand> {
    let ids: Vec<Vec<BusForm>> = Table::ALL[..N_OWNED].iter().map(|&t| identities(t)).collect();
    let offsets = constraints::xi_offsets(ids.iter().map(Vec::len));
    let xi2 = xi * xi;
    ids.into_iter()
        .zip(offsets)
        .enumerate()
        .map(|(t, (ids, offset))| {
            let mut power = (0..offset).fold(xi2, |p, _| p * xi);
            let mut parts = vec![forms[0][t].clone(), forms[1][t].scaled(xi)];
            for id in ids {
                parts.push(id.scaled(power));
                power *= xi;
            }
            Summand(BusForm::sum(parts))
        })
        .collect()
}

/// Slot `s` of table `t`'s key at row `z`.
pub const fn key(t: Table, s: usize, z: usize) -> u64 {
    ((t.first_slot() + s) as u64) << 32 | z as u64
}

/// The table and slot of a slot index among all tables' slots.
fn locate(gid: usize) -> (Table, usize) {
    let t = Table::ALL
        .into_iter()
        .rev()
        .find(|t| t.first_slot() <= gid)
        .expect("slot 0 is the first table's");
    (t, gid - t.first_slot())
}

/// Per table, per slot, each row's `next`: the key of the next slot of its wire's class, its own on a padding
/// row.
fn next_keys(circuit: &Circuit, taus: &[usize; N_TABLES]) -> [Vec<Vec<F64>>; N_TABLES] {
    let mut next: [Vec<Vec<F64>>; N_TABLES] = std::array::from_fn(|t| {
        let table = Table::ALL[t];
        (0..table.n_slots())
            .map(|s| (0..1 << taus[t]).map(|z| F64(key(table, s, z))).collect())
            .collect()
    });
    let n_classes = circuit.rows.iter().flatten().max().map_or(0, |&c| c as usize + 1);
    let (mut first, mut last) = (vec![u64::MAX; n_classes], vec![u64::MAX; n_classes]);
    let mut set = |at: u64, to: u64| {
        let (t, s) = locate((at >> 32) as usize);
        next[t as usize][s][(at & u64::from(u32::MAX)) as usize] = F64(to);
    };
    for table in Table::ALL {
        let n = table.n_slots();
        for (i, &c) in circuit.rows[table as usize].iter().enumerate() {
            let (c, k) = (c as usize, key(table, i % n, i / n));
            if last[c] == u64::MAX {
                first[c] = k;
            } else {
                set(last[c], k);
            }
            last[c] = k;
        }
    }
    for (&f, &l) in first.iter().zip(&last) {
        if l != u64::MAX {
            set(l, f);
        }
    }
    next
}

/// The bus's push and pull blocks: the `Pub` table's pair, which no table owns, then every owned table's, one
/// pair per slot.
///
/// `spans[t]` is owned table `t`'s first global column and width; `statement` is the words the `Pub` rows read.
pub fn bus_blocks(
    circuit: &Circuit,
    statement: &[Limbs],
    taus: &[usize; N_TABLES],
    spans: &[(usize, usize); N_OWNED],
) -> (Vec<Block>, Vec<Block>) {
    let mut next = next_keys(circuit, taus);
    let own_key = |t: Table, s: usize| Coord::IntIndex {
        base: F64(key(t, s, 0)),
        shift: 0,
    };
    let (mut push, mut pull) = (Vec::new(), Vec::new());

    let tau = taus[Table::Pub as usize];
    let mut values: [Vec<F64>; 4] = std::array::from_fn(|_| vec![F64::ZERO; 1 << tau]);
    assert_eq!(circuit.pubs.len(), circuit.row_counts()[Table::Pub as usize]);
    for (z, source) in circuit.pubs.iter().enumerate() {
        let v = match *source {
            PubSource::Const(v) => v,
            PubSource::Statement(i) => statement[i],
        };
        for (column, &v) in values.iter_mut().zip(&v) {
            column[z] = F64(v);
        }
    }
    let values: Vec<Coord> = values.into_iter().map(|v| Coord::Public(Arc::new(v))).collect();
    let pub_next = next[Table::Pub as usize].pop().expect("one Pub slot");
    pull.push(Block::framework(
        tau,
        std::iter::once(own_key(Table::Pub, 0))
            .chain(values.iter().cloned())
            .collect(),
    ));
    push.push(Block::framework(
        tau,
        std::iter::once(Coord::Public(Arc::new(pub_next)))
            .chain(values)
            .collect(),
    ));

    for (t, (table, next)) in Table::ALL[..N_OWNED].iter().zip(next).enumerate() {
        let (base, tau) = (spans[t].0, taus[t]);
        for (s, next) in next.into_iter().enumerate() {
            let limbs: Vec<Coord> = slot(*table, s).into_iter().map(|c| c.offset(base)).collect();
            pull.push(Block::table(
                t,
                tau,
                std::iter::once(own_key(*table, s))
                    .chain(limbs.iter().cloned())
                    .collect(),
            ));
            push.push(Block::table(
                t,
                tau,
                std::iter::once(Coord::Public(Arc::new(next))).chain(limbs).collect(),
            ));
        }
    }
    (push, pull)
}

/// A public column of the bus that the circuit fixes: slot `s` of table `t`'s `next`, or limb `j` of the `Pub`
/// rows' constants, the statement's rows zero there.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fixed {
    Next(Table, usize),
    Value(usize),
}

impl Fixed {
    /// The table whose height the column has.
    pub const fn table(self) -> Table {
        match self {
            Self::Next(t, _) => t,
            Self::Value(_) => Table::Pub,
        }
    }
}

/// Every fixed column, in the order a recursive verifier stacks them: each table's slots' `next`, in table and
/// slot order, then the four limbs of the `Pub` constants.
pub fn fixed_columns() -> Vec<Fixed> {
    Table::ALL
        .into_iter()
        .flat_map(|t| (0..t.n_slots()).map(move |s| Fixed::Next(t, s)))
        .chain((0..4).map(Fixed::Value))
        .collect()
}

/// The values of [`fixed_columns`] for `circuit` at heights `taus`.
pub fn fixed_values(circuit: &Circuit, taus: &[usize; N_TABLES]) -> Vec<Vec<F64>> {
    let mut next = next_keys(circuit, taus);
    let mut values: Vec<Vec<F64>> = next.iter_mut().flat_map(std::mem::take).collect();
    let tau = taus[Table::Pub as usize];
    let mut limbs: [Vec<F64>; 4] = std::array::from_fn(|_| vec![F64::ZERO; 1 << tau]);
    for (z, source) in circuit.pubs.iter().enumerate() {
        if let PubSource::Const(v) = *source {
            for (column, &v) in limbs.iter_mut().zip(&v) {
                column[z] = F64(v);
            }
        }
    }
    values.extend(limbs);
    values
}

/// Write table `t`'s committed columns, those past its ports, from the assignment: `windows` are its local
/// columns, each its height long, and padding rows are zero.
pub fn fill_table(t: Table, a: &Assignment, windows: &mut [&mut [F64]]) {
    let n = t.n_slots();
    let rows = &a.rows[t as usize];
    let value = |z: usize, s: usize| -> Limbs { a.values[rows[z * n + s] as usize] };
    // Each committed column as `(column, slot, limb)`: what the column holds is that limb of that slot's wire.
    let sources: Vec<(usize, usize, usize)> = match t {
        Table::Emul => (0..9).map(|c| (c, c / 3, c % 3)).collect(),
        Table::Exk => [
            (0, 0, 0),
            (1, 0, 1),
            (2, 0, 2),
            (3, 1, 0),
            (4, 2, 0),
            (5, 2, 1),
            (6, 2, 2),
        ]
        .to_vec(),
        Table::Split => (0..65).map(|c| (c, c, 0)).collect(),
        Table::Cast => (0..4).map(|c| (c, 0, c)).collect(),
        Table::Hash => {
            let column = &mut windows[SEL];
            column.fill(F64::ZERO);
            for (slot, &b) in column.iter_mut().zip(&a.selector) {
                *slot = F64(b);
            }
            return;
        }
        Table::Pub => return,
    };
    let height = rows.len() / n;
    for (c, s, limb) in sources {
        let column = &mut windows[c];
        for (z, slot) in column[..height].iter_mut().enumerate() {
            *slot = F64(value(z, s)[limb]);
        }
        column[height..].fill(F64::ZERO);
    }
}

#[cfg(test)]
pub(crate) fn eval_coord(c: &Coord, cols: &[F64]) -> F64 {
    match c {
        Coord::Const(v) => *v,
        Coord::Col(i) => cols[*i],
        Coord::Prod(i, j) => cols[*i] * cols[*j],
        Coord::Sum(cs) => cs.iter().fold(F64::ZERO, |acc, c| acc + eval_coord(c, cols)),
        _ => unreachable!("a slot's limbs are formable"),
    }
}
