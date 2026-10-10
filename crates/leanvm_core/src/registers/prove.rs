//! The prover's side of the log's argument.

use super::rounds::{cube, cubic_times, is_zero, linear, mul2, quadratic_times, rounds};
use super::verify::{Opened, cube_point, opening};
use super::{CELL_BITS, CELLS, GROUPS, Link, LinkShare, LogOpening, LogShape, WRITE};
use fiat_shamir::arith::{Arith, Native};
use fiat_shamir::transcript::Transmitter;
use primitives::field::{F64, F192, F192Unreduced, G, g_pow};
use primitives::multilinear::{eq_table, mle_eval_par};

/// Rows per task of a scan.
const TASK_ROWS: usize = 1 << 12;

/// The log's rows as the prover runs them.
#[derive(Clone, Debug, Default)]
pub(crate) struct LogWitness {
    /// Each group's cell, per row.
    pub(crate) cells: [Vec<u8>; GROUPS],
    /// Each row's increment: its written cell's old value XOR its new value.
    pub(crate) inc: Vec<F64>,
    /// Each row's flag: a pointer read, which writes nothing.
    pub(crate) flag: Vec<bool>,
    /// The rows that are cycles, first.
    pub(crate) live: usize,
}

impl LogWitness {
    /// Row `j`'s cell in group `g`.
    #[inline(always)]
    fn cell(&self, g: usize, j: usize) -> usize {
        usize::from(self.cells[g][j])
    }

    /// Row `j`'s flag in the field.
    fn flag_at(&self, j: usize) -> F192 {
        F192::from(F64(u64::from(self.flag[j])))
    }

    /// Group `g`'s cells as one-hot words, a row each.
    pub(crate) fn cell_words(&self, g: usize, out: &mut [F64]) {
        parallel::fill(out, |j| F64(1 << self.cell(g, j)));
    }

    /// The flags packed 64 rows a word, row `j` at bit `j % 64` of word `j / 64`.
    pub(crate) fn flag_words(&self, out: &mut [F64]) {
        parallel::fill(out, |w| {
            let flags = &self.flag[CELLS * w..CELLS * (w + 1)];
            F64(flags.iter().rev().fold(0, |acc, &f| acc << 1 | u64::from(f)))
        });
    }

    /// The log at `rows` rows, its dead rows naming the first row's cells and writing nothing.
    pub(crate) fn padded(&self, rows: usize) -> Self {
        let mut log = self.clone();
        for group in &mut log.cells {
            let dead = group.first().copied().unwrap_or(0);
            group.resize(rows, dead);
        }
        log.inc.resize(rows, F64::ZERO);
        log.flag.resize(rows, false);
        log
    }

    /// The registers before each chunk of `len` rows: each chunk's writes are summed in parallel, then chained.
    fn snapshots(&self, len: usize) -> Vec<[u64; CELLS]> {
        let deltas = parallel::map_collect(self.inc.len() / len, |c| {
            let mut delta = [0u64; CELLS];
            for j in c * len..(c + 1) * len {
                delta[self.cell(WRITE, j)] ^= self.inc[j].0;
            }
            delta
        });
        let mut registers = [0u64; CELLS];
        (deltas.iter())
            .map(|delta| {
                let start = registers;
                registers.iter_mut().zip(delta).for_each(|(r, d)| *r ^= d);
                start
            })
            .collect()
    }
}

/// The log's bus leaves: a live row's `beta + sum_i w_i slot_i`, a dead row's one.
///
/// Each chunk of rows replays the register file from its snapshot, in parallel with the others.
pub(crate) fn leaves(shape: &LogShape, w: &LogWitness, weights: &[F192], beta: F192) -> Vec<F192> {
    let rows = w.inc.len();
    let len = rows.min(TASK_ROWS);
    let snapshots = w.snapshots(len);
    // The slots' weights by role, so that a row's leaf is a few products.
    let link = Link::new(&mut Native, shape, weights);
    let constant = beta + link.constant;
    let mut leaves = vec![F192::ONE; rows];
    parallel::chunks_mut(&mut leaves, len, |c, out| {
        let mut registers = snapshots[c];
        let mut time = g_pow(c * len);
        for (leaf, j) in out.iter_mut().zip(c * len..) {
            let before: [u64; GROUPS] = std::array::from_fn(|g| registers[w.cell(g, j)]);
            let written = &mut registers[w.cell(WRITE, j)];
            *written ^= w.inc[j].0;
            if j < w.live {
                let mut x = constant + link.time.mul_base(time);
                for (g, &read) in before.iter().enumerate() {
                    x += link.address[g].mul_base(F64(w.cells[g][j].into()));
                    x += link.value[g].mul_base(F64(read));
                }
                x += link.inc.mul_base(w.inc[j]);
                if w.flag[j] {
                    x += link.flag;
                }
                *leaf = x;
            }
            time *= G;
        }
    });
    leaves
}

/// Prove the log's argument from the bus's share, mirroring the verifier's transcript.
pub(crate) fn prove(
    ps: &mut impl Transmitter,
    shape: &LogShape,
    w: &LogWitness,
    share: &LinkShare<F192>,
) -> LogOpening<F192> {
    assert_eq!(w.inc.len(), 1 << shape.log_rows, "the log's witness has a row per row");
    let link = Link::new(&mut Native, shape, &share.weights);
    let mut u = eq_table(&share.point);
    u[w.live..].fill(F192::ZERO);

    let fc_cell = tracing::info_span!("Cell rounds").in_scope(|| cell_rounds(ps, w, &u, &link));
    let ek = cell_eq(&fc_cell);
    let val = cell_values(w, &ek);
    let cycle = Cycle {
        w,
        link: &link,
        map: Native.int_index(F64::ZERO, 0, &fc_cell),
        ek: &ek,
    };
    let (fc_row, val_j) = tracing::info_span!("Cycle rounds").in_scope(|| cycle.read_write(ps, &u, &val));
    drop((u, val));
    ps.add_scalar(val_j);
    let read_write = open(ps, w, fc_row);

    let lw = Weights::draw(ps, shape);
    let fc_ev =
        tracing::info_span!("Evaluation rounds").in_scope(|| cycle.evaluation(ps, shape, &lw, &read_write.point));
    let evaluation = open(ps, w, fc_ev);
    opening(read_write, evaluation)
}

/// The evaluation sumcheck's batching weights, drawn in the verifier's order.
struct Weights {
    r_col: Vec<F192>,
    col: Vec<F192>,
    ptr: F192,
    out: Vec<F192>,
}

impl Weights {
    fn draw(ps: &mut impl Transmitter, shape: &LogShape) -> Self {
        Self {
            r_col: ps.sample_vec(CELL_BITS),
            col: ps.sample_vec(GROUPS),
            ptr: ps.sample(),
            out: ps.sample_vec(shape.outputs.len()),
        }
    }
}

/// Open the log at a sumcheck's final point: send each cell word's slices, the increment, and the flags' slices.
fn open(ps: &mut impl Transmitter, w: &LogWitness, point: Vec<F192>) -> Opened<F192> {
    let eq = eq_table(&point);
    let slices = slices(w, &eq);
    slices.iter().for_each(|s| ps.add_scalars(s));
    let inc = mle_eval_par(&w.inc, &point);
    ps.add_scalar(inc);
    let eq = eq_table(&point[CELL_BITS..]);
    let mut flag = vec![F192::ZERO; CELLS];
    for (j, _) in w.flag.iter().enumerate().filter(|(_, f)| **f) {
        flag[j % CELLS] += eq[j / CELLS];
    }
    ps.add_scalars(&flag);
    Opened {
        point,
        slices,
        inc,
        flag,
    }
}

/// Every group's 64 slices at the point whose `eq` table is given: slice `k` sums the rows whose cell is `k`.
fn slices(w: &LogWitness, eq: &[F192]) -> [Vec<F192>; GROUPS] {
    let len = eq.len().min(TASK_ROWS);
    let zero = || std::array::from_fn(|_| vec![F192::ZERO; CELLS]);
    parallel::map_reduce(
        eq.len() / len,
        zero,
        |t| {
            let mut acc: [Vec<F192>; GROUPS] = zero();
            for j in t * len..(t + 1) * len {
                for (g, slices) in acc.iter_mut().enumerate() {
                    slices[w.cell(g, j)] += eq[j];
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
fn cell_rounds(ps: &mut impl Transmitter, w: &LogWitness, u: &[F192], link: &Link<F192>) -> Vec<F192> {
    let rows = w.inc.len();
    let tasks = (rows / TASK_ROWS).max(1);
    let len = rows / tasks;
    let constant = |j: usize, g: usize| {
        let mut c = F192::ZERO;
        if g == WRITE {
            c += link.inc.mul_base(w.inc[j]);
        }
        if g == 0 {
            c += link.flag * w.flag_at(j);
        }
        c
    };
    // The registers at the start of each task, and the address map, folded with the cell bits.
    let mut starts: Vec<Vec<F192>> = {
        let mut registers = [F192::ZERO; CELLS];
        (0..tasks)
            .map(|t| {
                let start = registers.to_vec();
                for j in t * len..(t + 1) * len {
                    registers[w.cell(WRITE, j)] += F192::from(w.inc[j]);
                }
                start
            })
            .collect()
    };
    let mut map: [Vec<F192>; GROUPS] =
        std::array::from_fn(|g| (0..CELLS).map(|k| link.address[g].mul_base(F64(k as u64))).collect());
    let mut fc_cell = Vec::with_capacity(CELL_BITS);
    for i in 0..CELL_BITS {
        let prefix = eq_table(&fc_cell);
        let mask = (1usize << i) - 1;
        let sums = parallel::map_reduce(
            tasks,
            || [F192Unreduced::ZERO; 3],
            |t| {
                let mut tables: [Vec<F192>; GROUPS] = std::array::from_fn(|g| {
                    (starts[t].iter().zip(&map[g]))
                        .map(|(&s, &m)| link.value[g] * s + m)
                        .collect()
                });
                let mut acc = [F192Unreduced::ZERO; 3];
                for (j, &uj) in u.iter().enumerate().take((t + 1) * len).skip(t * len) {
                    if !uj.is_zero() {
                        for (g, table) in tables.iter().enumerate() {
                            let cell = w.cell(g, j);
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
                        let cell = w.cell(WRITE, j);
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
        map = map.each_ref().map(|t| fold(t));
        starts = parallel::map_collect(starts.len(), |t| fold(&starts[t]));
    }
    fc_cell
}

/// `Val(fc_cell, j)` for every row: the registers at `fc_cell`, before row `j` writes.
fn cell_values(w: &LogWitness, ek: &[F192; CELLS]) -> Vec<F192> {
    let rows = w.inc.len();
    let len = rows.min(TASK_ROWS);
    // Each task's value at its start: the writes of the tasks before it.
    let writes = parallel::map_collect(rows / len, |t| {
        (t * len..(t + 1) * len).fold(F192::ZERO, |acc, j| acc + ek[w.cell(WRITE, j)].mul_base(w.inc[j]))
    });
    let starts: Vec<F192> = writes
        .iter()
        .scan(F192::ZERO, |acc, &x| {
            let start = *acc;
            *acc += x;
            Some(start)
        })
        .collect();
    let mut val = vec![F192::ZERO; rows];
    parallel::chunks_mut(&mut val, len, |t, out| {
        let mut cur = starts[t];
        for (v, j) in out.iter_mut().zip(t * len..) {
            *v = cur;
            cur += ek[w.cell(WRITE, j)].mul_base(w.inc[j]);
        }
    });
    val
}

/// The cycle-variable sumchecks, once the cells are bound.
struct Cycle<'a> {
    w: &'a LogWitness,
    link: &'a Link<F192>,
    /// The address map at the cell point.
    map: F192,
    /// The eq table at the cell point.
    ek: &'a [F192; CELLS],
}

/// The read-write rows' entries: the summand is `U (A Val + B + EW inc + E0 flag)`.
///
/// The three groups share `Val`, so their weights fold into `A` and `B`, each a sum of table lookups.
struct ReadWrite;

impl ReadWrite {
    /// `u(j)`.
    const U: usize = 0;
    /// `sum_g value_g E_g(j)`.
    const A: usize = 1;
    /// `map sum_g address_g E_g(j)`.
    const B: usize = 2;
    /// `Val(fc_cell, j)`.
    const VAL: usize = 3;
    /// `inc_weight E_write(j)`.
    const EW: usize = 4;
    /// `inc(j)`.
    const INC: usize = 5;
    /// `flag_weight E_0(j)`.
    const E0: usize = 6;
    /// `flag(j)`.
    const FLAG: usize = 7;
    /// Entries per row.
    const N: usize = 8;
}

/// The evaluation rows' entries: the summand is `INC (LT WRITE + LIVE OUT + EQ FLAG) + EQ (Y + sum_g X_g^3)`.
struct Evaluation;

impl Evaluation {
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
    /// Entries per row.
    const N: usize = 11;
}

impl Cycle<'_> {
    /// The read-write sumcheck's cycle rounds. Returns the cycle point and `Val` there.
    fn read_write(&self, ps: &mut impl Transmitter, u: &[F192], val: &[F192]) -> (Vec<F192>, F192) {
        type R = ReadWrite;
        let (w, link, ek) = (self.w, self.link, self.ek);
        // Each group's weights at every cell, so that a row's entries are lookups and sums.
        let scaled = |s: F192| ek.map(|e| s * e);
        let value: [[F192; CELLS]; GROUPS] = std::array::from_fn(|g| scaled(link.value[g]));
        let address: [[F192; CELLS]; GROUPS] = std::array::from_fn(|g| scaled(link.address[g] * self.map));
        let (inc, flag) = (scaled(link.inc), scaled(link.flag));
        let row = |j: usize| {
            let cells: [usize; GROUPS] = std::array::from_fn(|g| w.cell(g, j));
            let mut row = [F192::ZERO; R::N];
            row[R::U] = u[j];
            row[R::A] = value[0][cells[0]] + value[1][cells[1]] + value[2][cells[2]];
            row[R::B] = address[0][cells[0]] + address[1][cells[1]] + address[2][cells[2]];
            (row[R::VAL], row[R::EW], row[R::INC]) = (val[j], inc[cells[WRITE]], F192::from(w.inc[j]));
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
        let log_rows = w.inc.len().ilog2() as usize;
        let (point, last) = rounds(ps, log_rows, LogShape::READ_WRITE_COEFFS, row, pair);
        (point, last[R::VAL])
    }

    /// The evaluation sumcheck's rounds. Returns its point.
    fn evaluation(&self, ps: &mut impl Transmitter, shape: &LogShape, lw: &Weights, fc_row: &[F192]) -> Vec<F192> {
        type R = Evaluation;
        let eq_j = eq_table(fc_row);
        let lt = suffix_sums(&eq_j);
        let (twisted, scale) = cube_point(&mut Native, &lw.r_col);
        let (er, et) = (cell_eq(&lw.r_col), cell_eq(&twisted));
        let x: [[F192; CELLS]; GROUPS] = std::array::from_fn(|g| er.map(|e| lw.col[g] * e));
        let y: [[F192; CELLS]; GROUPS] = std::array::from_fn(|g| {
            let s = lw.col[g].square() * lw.col[g] * scale;
            et.map(|e| s * e)
        });
        let mut psi = [F192::ZERO; CELLS];
        for (&cell, &lambda) in shape.outputs.iter().zip(&lw.out) {
            psi[cell] += lambda;
        }
        let (w, live) = (self.w, self.w.live);
        let row = |j: usize| {
            let cell = |g: usize| w.cell(g, j);
            let mut row = [F192::ZERO; R::N];
            (row[R::LT], row[R::WRITE], row[R::INC], row[R::EQ]) =
                (lt[j], self.ek[cell(WRITE)], F192::from(w.inc[j]), eq_j[j]);
            (0..GROUPS).for_each(|g| row[R::X + g] = x[g][cell(g)]);
            row[R::Y] = (0..GROUPS).fold(F192::ZERO, |acc, g| acc + y[g][cell(g)]);
            row[R::FLAG] = if w.flag[j] { lw.ptr } else { F192::ZERO };
            row[R::LIVE] = if j < live { F192::ONE } else { F192::ZERO };
            row[R::OUT] = psi[cell(WRITE)];
            row
        };
        let pair = |lo: &[F192; R::N], hi: &[F192; R::N]| {
            let at = |k| linear(lo, hi, k);
            let eq = at(R::EQ);
            // The zero checks, weighted by `eq`: the collisions' cubes and `y`.
            let mut c = cube(at(R::X));
            for g in 1..GROUPS {
                let t = cube(at(R::X + g));
                c.iter_mut().zip(t).for_each(|(c, t)| *c += t);
            }
            let y = at(R::Y);
            (c[0], c[1]) = (c[0] + y.0, c[1] + y.1);
            let mut sums = cubic_times(c, eq);
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
        rounds(ps, shape.log_rows, LogShape::EVALUATION_COEFFS, row, pair).0
    }
}

/// The eq table of a cell point.
fn cell_eq(point: &[F192]) -> [F192; CELLS] {
    eq_table(point).try_into().expect("a cell has six bits")
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
