//! The prover's side of a log's argument.

use super::rounds::{Poly, cube, cubic_times, is_zero, linear, mul2, quadratic_times, rounds};
use super::verify::{Evaluation, Opened, cube_point, opening};
use super::{CHUNK, CHUNK_BITS, ImageClaim, Kind, Link, LinkShare, LogOpening, LogShape, Slot};
use fiat_shamir::arith::Native;
use fiat_shamir::transcript::Transmitter;
use primitives::field::{F64, F192, F192Unreduced, G, g_pow};
use primitives::multilinear::{eq_table, mle_eval_par};

/// Rows per task of a scan.
const TASK_ROWS: usize = 1 << 12;

/// The most cells the tasks' snapshots hold together.
const SNAPSHOT_CELLS: usize = 1 << 22;

/// A log's rows as the prover runs them.
#[derive(Clone, Debug, Default)]
pub(crate) struct LogWitness {
    /// Each group's cell, per row.
    pub(crate) cells: Vec<Vec<u32>>,
    /// Each row's increment: its written cell's old value XOR its new value.
    pub(crate) inc: Vec<F64>,
    /// Each row's flag, for a log whose rows carry one.
    pub(crate) flag: Vec<bool>,
    /// Each live row's groups' cells as the row found them, which the executor records.
    pub(crate) reads: Vec<[u64; 3]>,
    /// The cells before the run.
    pub(crate) initial: Vec<F64>,
    /// The rows that are accesses, first.
    pub(crate) live: usize,
}

impl LogWitness {
    /// Chunk `c` of row `j`'s cell in group `g`.
    #[inline(always)]
    fn chunk(&self, g: usize, c: usize, j: usize) -> usize {
        (self.cells[g][j] as usize >> (CHUNK_BITS * c)) & (CHUNK - 1)
    }

    /// Row `j`'s flag in the field.
    fn flag_at(&self, j: usize) -> F192 {
        F192::from(F64(u64::from(self.flag.get(j).copied().unwrap_or(false))))
    }

    /// Group `g`'s chunk `c` as one-hot words, a row each.
    pub(crate) fn address_words(&self, g: usize, c: usize, out: &mut [F64]) {
        parallel::fill(out, |j| F64(1 << self.chunk(g, c, j)));
    }

    /// The flags packed 64 rows a word, row `j` at bit `j % 64` of word `j / 64`.
    pub(crate) fn flag_words(&self, out: &mut [F64]) {
        parallel::fill(out, |w| {
            let flags = &self.flag[CHUNK * w..CHUNK * (w + 1)];
            F64(flags.iter().rev().fold(0, |acc, &f| acc << 1 | u64::from(f)))
        });
    }

    /// The log at `rows` rows, its dead rows reading its first cell, or cell zero, and writing nothing.
    pub(crate) fn padded(&self, rows: usize) -> Self {
        let mut log = self.clone();
        for group in &mut log.cells {
            let dead = group.first().copied().unwrap_or(0);
            group.resize(rows, dead);
        }
        log.inc.resize(rows, F64::ZERO);
        if !log.flag.is_empty() {
            log.flag.resize(rows, false);
        }
        log
    }
}

/// A log's bus leaves: a live row's `beta + sum_i w_i slot_i`, a dead row's one.
///
/// Every live row's reads are recorded, so each leaf stands alone and the rows are taken in parallel.
pub(crate) fn leaves(shape: &LogShape, w: &LogWitness, weights: &[F192], beta: F192) -> Vec<F192> {
    let rows = w.inc.len();
    let len = rows.min(TASK_ROWS);
    let mut leaves = vec![F192::ONE; rows];
    parallel::chunks_mut(&mut leaves, len, |c, out| {
        let mut time = g_pow(c * len);
        for (leaf, j) in out.iter_mut().zip(c * len..).take_while(|&(_, j)| j < w.live) {
            let before = w.reads[j];
            let after = before[shape.write()] ^ w.inc[j].0;
            *leaf = (shape.slots.iter().zip(weights)).fold(beta, |leaf, (slot, &weight)| {
                let word = match *slot {
                    Slot::Const(c) => c,
                    Slot::Flagged { base, delta } if w.flag[j] => base + delta,
                    Slot::Flagged { base, .. } => base,
                    Slot::Time => time,
                    Slot::Address(g) => shape.address(w.cells[g][j] as usize),
                    Slot::Read(g) => F64(before[g]),
                    Slot::Written(_) => F64(after),
                };
                leaf + weight.mul_base(word)
            });
            time *= G;
        }
    });
    leaves
}

/// Prove a log's argument from the bus's share, mirroring the verifier's transcript.
pub(crate) fn prove(
    ps: &mut impl Transmitter,
    shape: &LogShape,
    w: &LogWitness,
    share: &LinkShare<F192>,
) -> LogOpening<F192> {
    assert_eq!(w.inc.len(), 1 << shape.log_rows, "a log's witness has a row per row");
    let link = Link::new(&mut Native, shape, &share.weights);
    let mut u = eq_table(&share.point);
    u[w.live..].fill(F192::ZERO);

    let tasks = Tasks::new(w.inc.len(), w.initial.len());
    let snapshots = tasks.snapshots(shape, w);
    let fc_cell =
        tracing::info_span!("Cell rounds").in_scope(|| cell_rounds(ps, shape, w, &tasks, &snapshots, &u, &link));
    let eks: Vec<[F192; CHUNK]> = (0..shape.chunks())
        .map(|c| chunk_eq(&fc_cell[CHUNK_BITS * c..][..CHUNK_BITS]))
        .collect();
    let val = cell_values(shape, w, &tasks, &snapshots, &eks);
    drop(snapshots);

    let cycle = Cycle {
        shape,
        w,
        link: &link,
        map: shape.address_mle(&mut Native, &fc_cell),
        eks: &eks,
    };
    let (fc_row, val_j) = tracing::info_span!("Cycle rounds").in_scope(|| cycle.read_write(ps, &u, &val));
    drop((u, val));
    ps.add_scalar(val_j);
    let read_write = open(ps, shape, w, fc_row);

    let lw = Weights::draw(ps, shape);
    let advice = match &shape.kind {
        Kind::Memory(regions) => {
            let (_, point) = regions.at(&mut Native, &fc_cell, regions.advice);
            let words: Vec<F64> = (0..1 << regions.advice.log_words)
                .map(|z| w.initial[regions.advice.cell(z, regions.low)])
                .collect();
            let value = mle_eval_par(&words, &point);
            ps.add_scalar(value);
            Some((point, value))
        }
        Kind::Registers { .. } => None,
    };
    let fc_ev = tracing::info_span!("Evaluation rounds").in_scope(|| cycle.evaluation(ps, &lw, &read_write.point));
    let image = match &shape.kind {
        Kind::Memory(regions) => {
            let (factor, point) = regions.at(&mut Native, &fc_cell, regions.ram);
            let weight = fc_ev.iter().fold(factor, |acc, &r| acc * r);
            let value = weight * regions.image.eval(&point);
            Some(ImageClaim { weight, point, value })
        }
        Kind::Registers { .. } => None,
    };
    let opened = open(ps, shape, w, fc_ev);
    opening(read_write, Evaluation { opened, advice, image })
}

/// The evaluation sumcheck's challenges, drawn in the verifier's order.
struct Weights {
    r_col: Vec<F192>,
    col: Vec<F192>,
    ptr: F192,
    part: F192,
    out: Vec<F192>,
}

impl Weights {
    fn draw(ps: &mut impl Transmitter, shape: &LogShape) -> Self {
        let r_col = ps.sample_vec(CHUNK_BITS);
        let col = ps.sample_vec(shape.groups() * shape.chunks());
        let (ptr, part, out) = match &shape.kind {
            Kind::Registers { outputs } => (ps.sample(), F192::ZERO, ps.sample_vec(outputs.len())),
            Kind::Memory(regions) => {
                let part = if regions.partial().is_some() {
                    ps.sample()
                } else {
                    F192::ZERO
                };
                (F192::ZERO, part, Vec::new())
            }
        };
        Self {
            r_col,
            col,
            ptr,
            part,
            out,
        }
    }
}

/// Open the log at a sumcheck's final point: send each address word's slices, the increment, and the flags' slices.
fn open(ps: &mut impl Transmitter, shape: &LogShape, w: &LogWitness, point: Vec<F192>) -> Opened<F192> {
    let eq = eq_table(&point);
    let slices = slices(shape, w, &eq);
    slices.iter().for_each(|s| ps.add_scalars(s));
    let inc = mle_eval_par(&w.inc, &point);
    ps.add_scalar(inc);
    let flag = shape.flagged().then(|| {
        let eq = eq_table(&point[CHUNK_BITS..]);
        let mut slices = vec![F192::ZERO; CHUNK];
        for (j, _) in w.flag.iter().enumerate().filter(|(_, f)| **f) {
            slices[j % CHUNK] += eq[j / CHUNK];
        }
        ps.add_scalars(&slices);
        slices
    });
    Opened {
        point,
        slices,
        inc,
        flag,
    }
}

/// Every group's and chunk's 64 slices at the point whose `eq` table is given: slice `k` sums the rows whose chunk is `k`.
fn slices(shape: &LogShape, w: &LogWitness, eq: &[F192]) -> Vec<Vec<F192>> {
    let n = shape.groups() * shape.chunks();
    let len = eq.len().min(TASK_ROWS);
    parallel::map_reduce(
        eq.len() / len,
        || vec![vec![F192::ZERO; CHUNK]; n],
        |t| {
            let mut acc = vec![vec![F192::ZERO; CHUNK]; n];
            for j in t * len..(t + 1) * len {
                for (i, slices) in acc.iter_mut().enumerate() {
                    slices[w.chunk(i / shape.chunks(), i % shape.chunks(), j)] += eq[j];
                }
            }
            acc
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(&b) {
                x.iter_mut().zip(y).for_each(|(x, &y)| *x += y);
            }
            a
        },
    )
}

/// How the scans split a log's rows into tasks, each from a snapshot of the cells.
struct Tasks {
    /// Rows per task.
    len: usize,
    /// Tasks.
    count: usize,
}

impl Tasks {
    /// Tasks of whole chunks of rows, few enough that their snapshots fit the budget.
    fn new(rows: usize, cells: usize) -> Self {
        let count = (rows / TASK_ROWS).clamp(1, (SNAPSHOT_CELLS / cells).max(1));
        let count = 1 << count.ilog2();
        Self {
            len: rows / count,
            count,
        }
    }

    /// The cells at the start of each task.
    fn snapshots(&self, shape: &LogShape, w: &LogWitness) -> Vec<Vec<F64>> {
        let mut memory = w.initial.clone();
        (0..self.count)
            .map(|t| {
                let start = memory.clone();
                for j in t * self.len..(t + 1) * self.len {
                    memory[w.cells[shape.write()][j] as usize] += w.inc[j];
                }
                start
            })
            .collect()
    }
}

/// The read-write sumcheck's cell rounds, lowest cell bit first.
///
/// Round `i` sweeps each task's rows with every group's cells folded at the bound bits:
///
/// ```text
///     T_g[k'] = value_g sum_low eq(r_{<i}, low) cell[k' 2^i + low] + address_g map(r_{<i}, k')
/// ```
///
/// An access with weight `w`, cell bit `b`, and `W = T_g + c_g(j)` adds `w L_b(X) ((1 + X) W_0 + X W_1)`:
///
/// ```text
///     b = 0:   w (W_0, W_1, W_0 + W_1)
///     b = 1:   w (0,   W_0, W_0 + W_1)
/// ```
///
/// A write then adds `value_g eq(r_{<i}, low) inc` to every group's table at its cell.
fn cell_rounds(
    ps: &mut impl Transmitter,
    shape: &LogShape,
    w: &LogWitness,
    tasks: &Tasks,
    snapshots: &[Vec<F64>],
    u: &[F192],
    link: &Link<F192>,
) -> Vec<F192> {
    let (groups, cells) = (shape.groups(), 1usize << shape.cell_bits());
    let constant = |j: usize, g: usize| {
        let mut c = F192::ZERO;
        if g == shape.write() {
            c += link.inc.mul_base(w.inc[j]);
        }
        if g == 0 {
            c += link.flag * w.flag_at(j);
        }
        c
    };
    let mut map: Vec<Vec<F192>> = (0..groups)
        .map(|g| parallel::map_collect(cells, |k| link.address[g].mul_base(shape.address(k))))
        .collect();
    let mut starts: Vec<Vec<F192>> = snapshots
        .iter()
        .map(|s| s.iter().map(|&x| F192::from(x)).collect())
        .collect();
    let mut fc_cell = Vec::with_capacity(shape.cell_bits());
    for i in 0..shape.cell_bits() {
        let prefix = eq_table(&fc_cell);
        let mask = (1usize << i) - 1;
        let sums = parallel::map_reduce(
            tasks.count,
            || [F192Unreduced::ZERO; 3],
            |t| {
                let mut tables: Vec<Vec<F192>> = (0..groups)
                    .map(|g| {
                        (starts[t].iter().zip(&map[g]))
                            .map(|(&s, &m)| link.value[g] * s + m)
                            .collect()
                    })
                    .collect();
                let mut acc = [F192Unreduced::ZERO; 3];
                for (j, &uj) in u.iter().enumerate().take((t + 1) * tasks.len).skip(t * tasks.len) {
                    if !uj.is_zero() {
                        for (g, table) in tables.iter().enumerate() {
                            let cell = w.cells[g][j] as usize;
                            let weight = uj * prefix[cell & mask];
                            let k = cell >> i;
                            let (t0, t1) = (table[k & !1], table[k | 1]);
                            let low = k & 1 == 0;
                            let a = weight.mul_unreduced(if low { t1 } else { t0 } + constant(j, g));
                            let b = weight.mul_unreduced(t0 + t1);
                            acc[1] ^= a;
                            acc[2] ^= b;
                            if low {
                                acc[0] ^= a ^ b;
                            }
                        }
                    }
                    if !w.inc[j].is_zero() {
                        let cell = w.cells[shape.write()][j] as usize;
                        let update = prefix[cell & mask].mul_base(w.inc[j]);
                        for (g, table) in tables.iter_mut().enumerate() {
                            table[cell >> i] += link.value[g] * update;
                        }
                    }
                }
                acc
            },
            |x, y| std::array::from_fn(|d| x[d] ^ y[d]),
        );
        ps.add_round_poly(&sums.map(F192Unreduced::reduce), false);
        let r = ps.sample();
        fc_cell.push(r);
        let fold = |t: &[F192]| -> Vec<F192> {
            t.as_chunks::<2>()
                .0
                .iter()
                .map(|&[lo, hi]| lo + r * (lo + hi))
                .collect()
        };
        map = map.iter().map(|t| fold(t)).collect();
        starts = parallel::map_collect(starts.len(), |t| fold(&starts[t]));
    }
    fc_cell
}

/// `Val(fc_cell, j)` for every row: the cells at `fc_cell`, before row `j` writes.
fn cell_values(
    shape: &LogShape,
    w: &LogWitness,
    tasks: &Tasks,
    snapshots: &[Vec<F64>],
    eks: &[[F192; CHUNK]],
) -> Vec<F192> {
    let eq_cell =
        |cell: usize| (0..shape.chunks()).fold(F192::ONE, |acc, c| acc * eks[c][(cell >> (CHUNK_BITS * c)) % CHUNK]);
    let mut val = vec![F192::ZERO; w.inc.len()];
    parallel::chunks_mut(&mut val, tasks.len, |t, out| {
        let mut cur = (snapshots[t].iter().enumerate())
            .filter(|(_, x)| !x.is_zero())
            .fold(F192::ZERO, |acc, (cell, &x)| acc + eq_cell(cell).mul_base(x));
        for (v, j) in out.iter_mut().zip(t * tasks.len..) {
            *v = cur;
            if !w.inc[j].is_zero() {
                cur += eq_cell(w.cells[shape.write()][j] as usize).mul_base(w.inc[j]);
            }
        }
    });
    val
}

/// The cycle-variable sumchecks, once the cells are bound.
struct Cycle<'a> {
    shape: &'a LogShape,
    w: &'a LogWitness,
    link: &'a Link<F192>,
    /// The address map at the cell point.
    map: F192,
    /// Each chunk's eq table at the cell point.
    eks: &'a [[F192; CHUNK]],
}

/// The registers' read-write rows.
/// The registers' read-write rows: the summand is `U (A Val + B + EW inc + E0 flag)`.
///
/// The three groups share `Val`, so their weights fold into `A` and `B`, each a sum of table lookups.
struct RegisterReadWrite;

impl RegisterReadWrite {
    const U: usize = 0;
    const A: usize = 1;
    const B: usize = 2;
    const VAL: usize = 3;
    const EW: usize = 4;
    const INC: usize = 5;
    const E0: usize = 6;
    const FLAG: usize = 7;
    const N: usize = 8;
}

/// Memory's read-write rows, for `C` chunks.
struct MemoryReadWrite<const C: usize>;

impl<const C: usize> MemoryReadWrite<C> {
    const U: usize = 0;
    const E: usize = 1;
    const VAL: usize = 1 + C;
    const INC: usize = 2 + C;
}

/// The registers' evaluation rows.
struct RegisterEvaluation;

impl RegisterEvaluation {
    const LT: usize = 0;
    const WRITE: usize = 1;
    const INC: usize = 2;
    const EQ: usize = 3;
    const X: usize = 4;
    const Y: usize = 7;
    /// The flag, times its check's weight.
    const FLAG: usize = 8;
    const LIVE: usize = 9;
    const OUT: usize = 10;
    const N: usize = 11;
}

/// Memory's evaluation rows, for `C` chunks.
struct MemoryEvaluation<const C: usize>;

impl<const C: usize> MemoryEvaluation<C> {
    const LT: usize = 0;
    const WRITE: usize = 1;
    const INC: usize = 1 + C;
    const EQ: usize = 2 + C;
    const X: usize = 3 + C;
    const Y: usize = 3 + 2 * C;
    const TOP: usize = 4 + 2 * C;
    const INSIDE: usize = 5 + 2 * C;
}

impl Cycle<'_> {
    /// The read-write sumcheck's cycle rounds: `u sum_g E_g inner_g`. Returns the cycle point and `Val` there.
    fn read_write(&self, ps: &mut impl Transmitter, u: &[F192], val: &[F192]) -> (Vec<F192>, F192) {
        match self.shape.chunks() {
            1 if self.shape.groups() == 3 => self.register_read_write(ps, u, val),
            1 => self.memory_read_write::<1, 4>(ps, u, val),
            2 => self.memory_read_write::<2, 5>(ps, u, val),
            3 => self.memory_read_write::<3, 6>(ps, u, val),
            4 => self.memory_read_write::<4, 7>(ps, u, val),
            chunks => unreachable!("a cell has at most four chunks, not {chunks}"),
        }
    }

    /// Group `g`'s inner factor `value_g Val + address_g map + c_g`, at a pair's two ends.
    fn inner(&self, g: usize, val: (F192, F192), inc: (F192, F192), flag: (F192, F192)) -> (F192, F192) {
        let link = self.link;
        let at = |val: F192, inc: F192, flag: F192| {
            let mut x = link.value[g] * val + link.address[g] * self.map;
            if g == self.shape.write() {
                x += link.inc * inc;
            }
            if g == 0 {
                x += link.flag * flag;
            }
            x
        };
        let lo = at(val.0, inc.0, flag.0);
        (lo, lo + at(val.0 + val.1, inc.0 + inc.1, flag.0 + flag.1))
    }

    fn register_read_write(&self, ps: &mut impl Transmitter, u: &[F192], val: &[F192]) -> (Vec<F192>, F192) {
        type R = RegisterReadWrite;
        let (w, link, ek) = (self.w, self.link, &self.eks[0]);
        // Each group's weights at every cell, so that a row's entries are lookups and sums.
        let scaled = |s: F192| ek.map(|e| s * e);
        let value: [[F192; CHUNK]; 3] = std::array::from_fn(|g| scaled(link.value[g]));
        let address: [[F192; CHUNK]; 3] = std::array::from_fn(|g| scaled(link.address[g] * self.map));
        let (inc, flag) = (scaled(link.inc), scaled(link.flag));
        let row = |j: usize| {
            let cells: [usize; 3] = std::array::from_fn(|g| w.chunk(g, 0, j));
            let mut row = [F192::ZERO; R::N];
            row[R::U] = u[j];
            row[R::A] = value[0][cells[0]] + value[1][cells[1]] + value[2][cells[2]];
            row[R::B] = address[0][cells[0]] + address[1][cells[1]] + address[2][cells[2]];
            (row[R::VAL], row[R::EW], row[R::INC]) = (val[j], inc[cells[2]], F192::from(w.inc[j]));
            (row[R::E0], row[R::FLAG]) = (flag[cells[0]], w.flag_at(j));
            row
        };
        let pair = |lo: &[F192; R::N], hi: &[F192; R::N]| {
            let at = |k| linear(lo, hi, k);
            let mut q = mul2(at(R::A), at(R::VAL));
            let b = at(R::B);
            (q[0], q[1]) = (q[0] + b.0, q[1] + b.1);
            for (weight, x) in [(R::EW, R::INC), (R::E0, R::FLAG)] {
                if !is_zero(at(x)) {
                    let t = mul2(at(weight), at(x));
                    q.iter_mut().zip(t).for_each(|(q, t)| *q += t);
                }
            }
            quadratic_times((q, at(R::U)))
        };
        let (point, last) = rounds(ps, self.shape.log_rows, self.shape.read_write_coeffs(), row, pair);
        (point, last[R::VAL])
    }

    fn memory_read_write<const C: usize, const N: usize>(
        &self,
        ps: &mut impl Transmitter,
        u: &[F192],
        val: &[F192],
    ) -> (Vec<F192>, F192) {
        const { assert!(N == C + 3) };
        let w = self.w;
        let row = |j: usize| {
            let mut row = [F192::ZERO; N];
            row[MemoryReadWrite::<C>::U] = u[j];
            (0..C).for_each(|c| row[MemoryReadWrite::<C>::E + c] = self.eks[c][w.chunk(0, c, j)]);
            (row[MemoryReadWrite::<C>::VAL], row[MemoryReadWrite::<C>::INC]) = (val[j], F192::from(w.inc[j]));
            row
        };
        let pair = |lo: &[F192; N], hi: &[F192; N]| {
            let at = |k| linear(lo, hi, k);
            let mut p = Poly::<N>::linear(at(MemoryReadWrite::<C>::U));
            (0..C).for_each(|c| p.times(at(MemoryReadWrite::<C>::E + c)));
            p.times(self.inner(
                0,
                at(MemoryReadWrite::<C>::VAL),
                at(MemoryReadWrite::<C>::INC),
                (F192::ZERO, F192::ZERO),
            ));
            p.unreduced()
        };
        let (point, last) = rounds(ps, self.shape.log_rows, self.shape.read_write_coeffs(), row, pair);
        (point, last[MemoryReadWrite::<C>::VAL])
    }

    /// The evaluation sumcheck's rounds. Returns its point.
    fn evaluation(&self, ps: &mut impl Transmitter, lw: &Weights, fc_row: &[F192]) -> Vec<F192> {
        let eq_j = eq_table(fc_row);
        let lt = suffix_sums(&eq_j);
        let (twisted, scale) = cube_point(&mut Native, &lw.r_col);
        let (er, et) = (chunk_eq(&lw.r_col), chunk_eq(&twisted));
        let x: Vec<[F192; CHUNK]> = lw.col.iter().map(|&b| er.map(|e| b * e)).collect();
        let y: Vec<[F192; CHUNK]> = (lw.col.iter())
            .map(|&b| {
                let s = b.square() * b * scale;
                et.map(|e| s * e)
            })
            .collect();
        let tables = Lookups { eq_j, lt, x, y };
        match self.shape.chunks() {
            1 if self.shape.groups() == 3 => self.register_evaluation(ps, lw, &tables),
            1 => self.memory_evaluation::<1, 7, 5>(ps, lw, &tables),
            2 => self.memory_evaluation::<2, 10, 5>(ps, lw, &tables),
            3 => self.memory_evaluation::<3, 13, 6>(ps, lw, &tables),
            4 => self.memory_evaluation::<4, 16, 7>(ps, lw, &tables),
            chunks => unreachable!("a cell has at most four chunks, not {chunks}"),
        }
    }

    fn register_evaluation(&self, ps: &mut impl Transmitter, lw: &Weights, t: &Lookups) -> Vec<F192> {
        type R = RegisterEvaluation;
        let Kind::Registers { outputs } = &self.shape.kind else {
            unreachable!("three groups are the registers'")
        };
        let mut psi = [F192::ZERO; CHUNK];
        for (&cell, &lambda) in outputs.iter().zip(&lw.out) {
            psi[cell] += lambda;
        }
        let (w, live) = (self.w, self.w.live);
        let row = |j: usize| {
            let cell = |g: usize| w.chunk(g, 0, j);
            let mut row = [F192::ZERO; R::N];
            (row[R::LT], row[R::WRITE], row[R::INC], row[R::EQ]) =
                (t.lt[j], self.eks[0][cell(2)], F192::from(w.inc[j]), t.eq_j[j]);
            (0..3).for_each(|g| row[R::X + g] = t.x[g][cell(g)]);
            row[R::Y] = (0..3).fold(F192::ZERO, |acc, g| acc + t.y[g][cell(g)]);
            row[R::FLAG] = if w.flag[j] { lw.ptr } else { F192::ZERO };
            row[R::LIVE] = if j < live { F192::ONE } else { F192::ZERO };
            row[R::OUT] = psi[cell(2)];
            row
        };
        let pair = |lo: &[F192; R::N], hi: &[F192; R::N]| {
            let at = |k| linear(lo, hi, k);
            // The zero checks, weighted by `eq`: the collisions' cubes and `y`.
            let mut c = cube(at(R::X));
            for g in 1..3 {
                let t = cube(at(R::X + g));
                c.iter_mut().zip(t).for_each(|(c, t)| *c += t);
            }
            let y = at(R::Y);
            (c[0], c[1]) = (c[0] + y.0, c[1] + y.1);
            let mut sums = cubic_times(c, at(R::EQ));
            // The increment's terms: `Val`'s, the outputs', and the flag's check.
            let inc = at(R::INC);
            if !is_zero(inc) {
                let mut q = mul2(at(R::LT), at(R::WRITE));
                for (a, b) in [(R::LIVE, R::OUT), (R::EQ, R::FLAG)] {
                    if !is_zero(at(b)) {
                        let t = mul2(at(a), at(b));
                        q.iter_mut().zip(t).for_each(|(q, t)| *q += t);
                    }
                }
                let t = quadratic_times((q, inc));
                sums.iter_mut().zip(t).for_each(|(s, t)| *s ^= t);
            }
            sums
        };
        rounds(ps, self.shape.log_rows, self.shape.evaluation_coeffs(), row, pair).0
    }

    fn memory_evaluation<const C: usize, const N: usize, const D: usize>(
        &self,
        ps: &mut impl Transmitter,
        lw: &Weights,
        t: &Lookups,
    ) -> Vec<F192> {
        const { assert!(N == 3 * C + 4) };
        let Kind::Memory(regions) = &self.shape.kind else {
            unreachable!("one group is memory's")
        };
        let partial = regions.partial();
        // The values each low chunk allows a cell of the partial region: all of a chunk it fills.
        let mut allowed = [CHUNK; C];
        for (c, m) in partial.map(|r| regions.allowed(r)).unwrap_or_default() {
            allowed[c] = m;
        }
        let w = self.w;
        let row = |j: usize| {
            let mut row = [F192::ONE; N];
            (
                row[MemoryEvaluation::<C>::LT],
                row[MemoryEvaluation::<C>::INC],
                row[MemoryEvaluation::<C>::EQ],
            ) = (t.lt[j], F192::from(w.inc[j]), t.eq_j[j]);
            for c in 0..C {
                let chunk = w.chunk(0, c, j);
                row[MemoryEvaluation::<C>::WRITE + c] = self.eks[c][chunk];
                row[MemoryEvaluation::<C>::X + c] = t.x[c][chunk];
            }
            row[MemoryEvaluation::<C>::Y] = (0..C).fold(F192::ZERO, |acc, c| acc + t.y[c][w.chunk(0, c, j)]);
            let top = partial.is_some_and(|r| w.chunk(0, C - 1, j) == r.first);
            row[MemoryEvaluation::<C>::TOP] = if top { F192::ONE } else { F192::ZERO };
            for c in 0..C - 1 {
                row[MemoryEvaluation::<C>::INSIDE + c] = if w.chunk(0, c, j) < allowed[c] {
                    F192::ONE
                } else {
                    F192::ZERO
                };
            }
            row
        };
        let pair = |lo: &[F192; N], hi: &[F192; N]| {
            let at = |k| linear(lo, hi, k);
            let mut value = Poly::<D>::linear(at(MemoryEvaluation::<C>::LT));
            (0..C).for_each(|c| value.times(at(MemoryEvaluation::<C>::WRITE + c)));
            value.times(at(MemoryEvaluation::<C>::INC));
            let mut checks = Poly::linear(at(MemoryEvaluation::<C>::Y));
            (0..C).for_each(|c| checks.add(Poly::cube(at(MemoryEvaluation::<C>::X + c))));
            if partial.is_some() {
                let mut excess = Poly::linear((F192::ONE, F192::ZERO));
                (0..C - 1).for_each(|c| excess.times(at(MemoryEvaluation::<C>::INSIDE + c)));
                excess.add(Poly::linear((F192::ONE, F192::ZERO)));
                excess.times(at(MemoryEvaluation::<C>::TOP));
                excess.scale(lw.part);
                checks.add(excess);
            }
            checks.times(at(MemoryEvaluation::<C>::EQ));
            value.add(checks);
            value.unreduced()
        };
        rounds(ps, self.shape.log_rows, self.shape.evaluation_coeffs(), row, pair).0
    }
}

/// The evaluation sumcheck's tables: `eq(fc_row, .)`, `LT(., fc_row)`, and the collision terms' lookups per group and chunk.
struct Lookups {
    eq_j: Vec<F192>,
    lt: Vec<F192>,
    x: Vec<[F192; CHUNK]>,
    y: Vec<[F192; CHUNK]>,
}

/// The eq table of a chunk's point.
fn chunk_eq(point: &[F192]) -> [F192; CHUNK] {
    eq_table(point).try_into().expect("a chunk has six bits")
}

/// `out[j] = sum_{j' > j} eq[j']`: the less-than polynomial at `(j, r)` for the point `r` of `eq`.
fn suffix_sums(eq: &[F192]) -> Vec<F192> {
    let len = eq.len().min(TASK_ROWS);
    let totals = parallel::map_collect(eq.len() / len, |c| {
        eq[c * len..(c + 1) * len].iter().fold(F192::ZERO, |acc, &e| acc + e)
    });
    let mut above = vec![F192::ZERO; totals.len()];
    for c in (1..totals.len()).rev() {
        above[c - 1] = above[c] + totals[c];
    }
    let mut out = vec![F192::ZERO; eq.len()];
    parallel::chunks_mut(&mut out, len, |c, out| {
        let mut acc = above[c];
        for (o, &e) in out.iter_mut().zip(&eq[c * len..]).rev() {
            *o = acc;
            acc += e;
        }
    });
    out
}
