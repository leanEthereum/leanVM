//! `K`-valued columns stacked into one committed witness (§sec:stacking, §sec:jagged).
//!
//! A column is `2^row_vars` rows of `2^stride_log` words, of which only the first
//! `rows` are committed: every row past them repeats the last committed one. The
//! committed rows are cut into aligned power-of-two pieces (the binary expansion of
//! the rows before the last, then the last row alone), and every piece of every
//! column is laid end to end, largest first at aligned offsets, into one multilinear
//! `q` over `F64`. An evaluation claim on a column becomes a claim on `q` whose
//! weight is one scaled equality term per piece ([`Column::terms`]).
//!
//! Every witness builder writes its pieces straight into place ([`split_pieces`]).
//! The prover also keeps every column that commits only some of its rows at those
//! rows, in a stack of its own ([`live_windows`]): that is what the bus and the
//! table sumcheck read, taking the rows past them as the last.

use primitives::field::{F64, F192};
use zk_alloc::ArenaVec;

/// What a column is, before it is placed.
#[derive(Clone, Copy, Debug)]
pub enum Source {
    /// A committed column of `2^row_vars` rows of `2^stride_log` words, the first
    /// `rows` of them committed and every later one a copy of row `rows - 1`.
    Committed {
        row_vars: usize,
        stride_log: usize,
        rows: usize,
    },
    /// Not committed: port `port` of every instance of the committed column `column`, a
    /// packed witness whose instances are `2^stride_log` words apart. It carries data
    /// for the bus, while its evaluation claims settle against that witness.
    Port {
        column: usize,
        port: usize,
        stride_log: usize,
    },
}

impl Source {
    /// A column of `2^kappa` words, all of them committed.
    pub const fn full(kappa: usize) -> Self {
        Self::Committed {
            row_vars: kappa,
            stride_log: 0,
            rows: 1 << kappa,
        }
    }
}

/// The aligned pieces a column of `2^row_vars` rows commits its first `rows` in, as
/// `(first row, log2 of its rows)`: the whole column when every row is committed,
/// otherwise the binary expansion of `rows - 1`, largest first, then the last
/// committed row alone, which every row after it repeats.
pub fn pieces(row_vars: usize, rows: usize) -> Vec<(usize, usize)> {
    assert!(
        (1..=1usize << row_vars).contains(&rows),
        "a column commits 1..=2^{row_vars} rows"
    );
    if rows == 1 << row_vars {
        return vec![(0, row_vars)];
    }
    let live = rows - 1;
    let mut out = Vec::new();
    let mut first = 0;
    for bit in (0..row_vars).rev().filter(|&bit| (live >> bit) & 1 == 1) {
        out.push((first, bit));
        first += 1 << bit;
    }
    out.push((live, 0));
    out
}

/// `eq(point[from..], first >> from)`: the weight a point puts on the aligned rows
/// `[first, first + 2^from)`.
fn eq_bits(point: &[F192], first: usize, from: usize) -> F192 {
    point[from..].iter().enumerate().fold(F192::ONE, |e, (k, &r)| {
        e * if (first >> (from + k)) & 1 == 1 {
            r
        } else {
            F192::ONE + r
        }
    })
}

/// One aligned piece of a committed column: `2^log_rows` rows from `first_row`,
/// at `offset` in the committed stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Piece {
    pub first_row: usize,
    pub log_rows: usize,
    pub offset: usize,
}

/// A committed column's place in the committed stack: its shape and its pieces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Column {
    pub row_vars: usize,
    pub stride_log: usize,
    pub rows: usize,
    pub pieces: Vec<Piece>,
}

impl Column {
    /// What the column's rows at `row_point` put on each piece (§sec:jagged). Piece
    /// `[a, a + 2^e)` takes `eq(row_point[e..], a >> e)`, the share of the point's
    /// equality weight its rows carry; the last committed row, when later rows repeat
    /// it, takes the weight of every row from it on, `1 - Σ` of the others.
    pub fn scales(&self, row_point: &[F192]) -> Vec<F192> {
        assert_eq!(row_point.len(), self.row_vars, "a row point names a row");
        if self.rows == 1 << self.row_vars {
            return vec![F192::ONE];
        }
        let (live, last) = self.pieces.split_at(self.pieces.len() - 1);
        let mut scales: Vec<F192> = live
            .iter()
            .map(|p| eq_bits(row_point, p.first_row, p.log_rows))
            .collect();
        debug_assert_eq!(last[0].log_rows, 0);
        scales.push(scales.iter().fold(F192::ONE, |acc, &s| acc + s));
        scales
    }

    /// The stack terms of a claim on the column at `row_point`, whose first `low_vars`
    /// coords are a row's own (`0` when the claim fixes them to a slot): one per piece
    /// whose scale is not zero, each over its piece's rows and those coords.
    pub fn terms(&self, row_point: &[F192], low_vars: usize) -> Vec<(usize, usize, F192)> {
        self.pieces
            .iter()
            .zip(self.scales(row_point))
            .filter(|&(_, scale)| scale != F192::ZERO)
            .map(|(p, scale)| (p.offset, low_vars + p.log_rows, scale))
            .collect()
    }

    /// Words committed.
    pub fn committed_len(&self) -> usize {
        self.pieces
            .iter()
            .map(|p| 1usize << (p.log_rows + self.stride_log))
            .sum()
    }
}

/// Where a column sits in the committed stack.
#[derive(Clone, Debug)]
pub enum Placement {
    Committed(Column),
    /// Port `port` of every instance of the committed column `column`, instances
    /// `2^stride_log` words apart.
    Port {
        column: usize,
        port: usize,
        stride_log: usize,
    },
}

impl Placement {
    /// The column, if it is committed.
    pub const fn column(&self) -> Option<&Column> {
        match self {
            Self::Committed(column) => Some(column),
            Self::Port { .. } => None,
        }
    }
}

/// The committed stack's shape. `mu` is the log size everything public is derived
/// from (the claims' selector coords, the PCS level ladder), while `n_lanes` counts
/// the `2^(mu - LOG_BATCH)`-word lane blocks that actually carry data: the PCS
/// commits `committed_len()` words and never encodes or hashes the zero tail past
/// them. Only the prover needs `n_lanes`; the verifier's view of the commitment is
/// the same `2^mu`-word witness either way.
#[derive(Clone, Copy, Debug)]
pub struct StackShape {
    pub mu: usize,
    pub n_lanes: usize,
}

impl StackShape {
    /// Words actually committed: the placed columns rounded up to a whole lane.
    pub fn committed_len(&self) -> usize {
        // Both fields are `pub`, and in release the shift below would mask an
        // underflowed amount into a plausible wrong length rather than panic.
        assert!(self.mu >= crate::pcs::LOG_BATCH, "a stack is at least one lane block");
        self.n_lanes << (self.mu - crate::pcs::LOG_BATCH)
    }
}

/// Lay `2^kappa`-sized items end to end, largest first at aligned offsets and ties
/// broken by index, returning the per-item offset and `Σ 2^kappa`. A `None`
/// kappa takes no space and its offset is meaningless. Depends only on the sizes, so
/// the verifier reconstructs the same tiling.
pub(crate) fn stack_offsets(kappas: &[Option<usize>]) -> (Vec<usize>, usize) {
    let n = kappas.len();
    let mut order: Vec<usize> = (0..n).filter(|&i| kappas[i].is_some()).collect();
    order.sort_by(|&a, &b| kappas[b].unwrap().cmp(&kappas[a].unwrap()).then(a.cmp(&b)));

    let mut offsets = vec![0usize; n];
    let mut off = 0usize;
    for &i in &order {
        let kappa = kappas[i].unwrap();
        assert!(
            kappa < usize::BITS as usize,
            "kappa {kappa} is a log-size, not a length"
        );
        offsets[i] = off;
        off += 1 << kappa;
    }
    (offsets, off)
}

/// The committed pieces' total length, before the stack's zero pad: the real witness size.
pub fn committed_len(placements: &[Placement]) -> usize {
    placements
        .iter()
        .filter_map(Placement::column)
        .map(Column::committed_len)
        .sum()
}

/// Per-column placements and the committed stack's [`StackShape`] from the columns'
/// sources alone: every piece of every committed column, in column then piece order,
/// stacked largest first at aligned offsets. Depends only on the sizes, so the
/// verifier can reconstruct it.
pub fn placements_of(sources: &[Source]) -> (Vec<Placement>, StackShape) {
    let shapes: Vec<Option<(usize, usize, usize)>> = sources
        .iter()
        .map(|s| match *s {
            Source::Committed {
                row_vars,
                stride_log,
                rows,
            } => Some((row_vars, stride_log, rows)),
            Source::Port { .. } => None,
        })
        .collect();
    let cut: Vec<Vec<(usize, usize)>> = shapes
        .iter()
        .map(|s| s.map_or_else(Vec::new, |(row_vars, _, rows)| pieces(row_vars, rows)))
        .collect();
    let kappas: Vec<Option<usize>> = cut
        .iter()
        .zip(&shapes)
        .flat_map(|(pieces, s)| pieces.iter().map(move |&(_, log_rows)| Some(log_rows + s.unwrap().1)))
        .collect();
    let (offsets, placed) = stack_offsets(&kappas);
    let mut offsets = offsets.into_iter();
    let placements = sources
        .iter()
        .zip(shapes.iter().zip(cut))
        .map(|(s, (shape, cut))| match (*s, *shape) {
            (_, Some((row_vars, stride_log, rows))) => Placement::Committed(Column {
                row_vars,
                stride_log,
                rows,
                pieces: cut
                    .into_iter()
                    .map(|(first_row, log_rows)| Piece {
                        first_row,
                        log_rows,
                        offset: offsets.next().expect("one offset per piece"),
                    })
                    .collect(),
            }),
            (
                Source::Port {
                    column,
                    port,
                    stride_log,
                },
                None,
            ) => {
                assert!(shapes[column].is_some(), "a port is of a committed column");
                Placement::Port {
                    column,
                    port,
                    stride_log,
                }
            }
            (Source::Committed { .. }, None) => unreachable!("a committed column has a shape"),
        })
        .collect();
    // Floor at the PCS minimum (WHIR's level ladder needs room); tiny
    // witnesses zero-pad up. Both sides derive this identically from the sizes.
    let mu = crate::log2_ceil_usize(placed.max(1)).max(crate::pcs::MIN_MU);
    // The pieces tile from 0, so the padding is the tail: round it up to a whole
    // lane and the lanes past that are never committed at all.
    let n_lanes = placed.div_ceil(1 << (mu - crate::pcs::LOG_BATCH)).max(1);
    (placements, StackShape { mu, n_lanes })
}

/// A column's window in the prover's live stack: `len` words from `offset`.
#[derive(Clone, Copy, Debug)]
pub struct Window {
    pub offset: usize,
    pub len: usize,
}

/// Every column of one word a row that commits only some of its rows, at its
/// committed rows (the rows past them repeat the last), laid end to end, and the
/// total: the prover's working copy, which the bus and the table sumcheck read and
/// nothing commits. A column committed whole has no window, the committed stack
/// holding it in one piece; neither has a port, nor a packed witness (rows of
/// several words), whose words its flock batch already holds.
pub fn live_windows(sources: &[Source]) -> (Vec<Option<Window>>, usize) {
    let mut total = 0;
    let windows = (sources.iter())
        .map(|s| match *s {
            Source::Committed {
                row_vars,
                stride_log: 0,
                rows,
            } if rows < 1 << row_vars => {
                let window = Window {
                    offset: total,
                    len: rows,
                };
                total += rows;
                Some(window)
            }
            Source::Committed { .. } | Source::Port { .. } => None,
        })
        .collect();
    (windows, total)
}

/// The uninitialized `len`-word live stack. Arena-backed: it is born and dies inside
/// one `cpu::Program::prove` phase.
///
/// # Safety
/// Every slot must be written before it is read. [`split_stack`] hands out one
/// window per committed column, which together cover the whole allocation, so the
/// obligation reduces to each column's fill writing its own window.
pub unsafe fn alloc_live(len: usize) -> ArenaVec<F64> {
    // SAFETY: forwarded to the caller by the contract above.
    unsafe { ArenaVec::<F64>::uninitialized(len) }
}

/// Carve the live stack into one mutable window per column that has one, in column
/// order, and an empty window for the others.
///
/// Writing each column into its final place is what lets the whole witness be
/// written once. Safe despite [`alloc_live`]'s uninitialized allocation:
/// [`live_windows`] tiles the columns from offset 0 with no gap, checked here, so
/// consecutive `split_at_mut` hands out disjoint windows covering all of it.
pub fn split_stack<'a>(q: &'a mut [F64], windows: &[Option<Window>]) -> Vec<&'a mut [F64]> {
    let mut out: Vec<&mut [F64]> = Vec::with_capacity(windows.len());
    let mut rest = q;
    let mut placed = 0usize;
    for w in windows {
        out.push(match w {
            Some(w) => {
                assert_eq!(w.offset, placed, "the stacked columns must tile from 0 with no gap");
                let (window, tail) = std::mem::take(&mut rest).split_at_mut(w.len);
                rest = tail;
                placed += w.len;
                window
            }
            None => &mut [],
        });
    }
    assert!(rest.is_empty(), "the windows must cover the whole stack");
    out
}

/// Carve the committed stack into its pieces, `pieces[i][k]` being piece `k` of
/// column `i` (none for a port), and the tail past the last piece, which the
/// commitment takes as zeros. Every witness builder writes its pieces in place, so
/// the committed stack is written once and never gathered.
///
/// The pieces tile `[0, placed)` with no gap ([`placements_of`]), checked here, so
/// consecutive `split_at_mut` hand out disjoint slices covering all of `q`.
#[allow(clippy::type_complexity)]
pub fn split_pieces<'a>(q: &'a mut [F64], placements: &[Placement]) -> (Vec<Vec<&'a mut [F64]>>, &'a mut [F64]) {
    let mut order: Vec<(usize, usize, usize, usize)> = (placements.iter().enumerate())
        .filter_map(|(i, p)| Some((i, p.column()?)))
        .flat_map(|(i, c)| {
            (c.pieces.iter().enumerate()).map(move |(k, p)| (p.offset, i, k, 1usize << (p.log_rows + c.stride_log)))
        })
        .collect();
    order.sort_unstable_by_key(|&(offset, ..)| offset);

    let mut out: Vec<Vec<&mut [F64]>> = placements
        .iter()
        .map(|p| {
            let n = p.column().map_or(0, |c| c.pieces.len());
            let mut pieces = Vec::with_capacity(n);
            pieces.resize_with(n, || &mut [][..]);
            pieces
        })
        .collect();
    let mut rest = q;
    let mut placed = 0usize;
    for (offset, i, k, len) in order {
        assert_eq!(offset, placed, "the pieces must tile the stack from 0 with no gap");
        let (piece, tail) = rest.split_at_mut(len);
        out[i][k] = piece;
        rest = tail;
        placed += len;
    }
    (out, rest)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The shape has to cover the placed pieces with as few lanes as possible: the
    /// prover commits `committed_len()` words, so anything short of `placed` would
    /// leave a claim outside the commitment, and any extra whole lane is work the
    /// change exists to avoid. `mu` stays the announced `2^mu` size both sides
    /// derive their layout from.
    #[test]
    fn placements_cover_the_columns_in_the_fewest_lanes() {
        let lanes = 1usize << crate::pcs::LOG_BATCH;
        // A power-of-two total, one word over one, one just under, a port
        // in the middle, jagged columns, and a stack far below the MIN_MU floor.
        let port = Source::Port {
            column: 0,
            port: 1,
            stride_log: 2,
        };
        let jagged = |row_vars, stride_log, rows| Source::Committed {
            row_vars,
            stride_log,
            rows,
        };
        let cases: [Vec<Source>; 6] = [
            vec![Source::full(20), Source::full(20)],
            vec![Source::full(20), Source::full(20), Source::full(0)],
            vec![Source::full(20), Source::full(19), Source::full(18), Source::full(17)],
            vec![Source::full(21), port, Source::full(19), port, Source::full(15)],
            vec![Source::full(3), Source::full(2)],
            vec![
                jagged(20, 4, 600_001),
                port,
                jagged(13, 0, 1),
                jagged(18, 0, 1 << 18),
                jagged(19, 3, 77),
            ],
        ];
        for sources in cases {
            let placed: usize = sources
                .iter()
                .map(|s| match *s {
                    Source::Committed { stride_log, rows, .. } => rows << stride_log,
                    Source::Port { .. } => 0,
                })
                .sum();
            let (placements, shape) = placements_of(&sources);
            let lane_block = 1usize << (shape.mu - crate::pcs::LOG_BATCH);

            assert_eq!(shape.mu, crate::log2_ceil_usize(placed).max(crate::pcs::MIN_MU));
            assert!((1..=lanes).contains(&shape.n_lanes), "lane count out of range");
            assert!(shape.committed_len() >= placed, "columns must fit the commitment");
            assert!(
                shape.committed_len() - placed < lane_block,
                "a whole lane of the commitment carries no data"
            );
            assert!(shape.committed_len() <= 1usize << shape.mu);
            // Every piece lives inside those lanes, aligned to its size, and covers
            // exactly its column's committed rows.
            for c in placements.iter().filter_map(Placement::column) {
                let mut rows = 0;
                for p in &c.pieces {
                    let len = 1usize << (p.log_rows + c.stride_log);
                    assert!(p.offset.is_multiple_of(len) && p.offset + len <= shape.committed_len());
                    assert_eq!(p.first_row, rows, "pieces cover the rows in order");
                    rows += 1 << p.log_rows;
                }
                assert_eq!(rows, c.rows);
            }
        }
    }

    /// A claim on a column, as the sum of its pieces' terms against the committed
    /// rows, is the column's multilinear extension at its full height, the rows past
    /// the committed ones repeating the last.
    #[test]
    fn piece_terms_evaluate_the_padded_column() {
        let mut rng = primitives::test_rng::Rng::new(7);
        for (row_vars, rows) in [(5, 32), (5, 1), (5, 2), (5, 17), (5, 31), (6, 45), (3, 8)] {
            let column = Column {
                row_vars,
                stride_log: 0,
                rows,
                pieces: pieces(row_vars, rows)
                    .into_iter()
                    .map(|(first_row, log_rows)| Piece {
                        first_row,
                        log_rows,
                        offset: first_row,
                    })
                    .collect(),
            };
            let committed: Vec<F64> = (0..rows).map(|_| F64(rng.next_u64())).collect();
            let padded: Vec<F64> = (0..1 << row_vars).map(|j| committed[j.min(rows - 1)]).collect();
            let point = rng.ext_vec(row_vars);
            let expected = primitives::multilinear::mle_eval(&padded, &point);
            let actual = column
                .terms(&point, 0)
                .into_iter()
                .fold(F192::ZERO, |acc, (offset, n_vars, scale)| {
                    let eq = primitives::multilinear::eq_table(&point[..n_vars]);
                    let dot = eq
                        .iter()
                        .zip(&committed[offset..offset + (1 << n_vars)])
                        .fold(F192::ZERO, |s, (&e, &v)| s + e.mul_base(v));
                    acc + scale * dot
                });
            assert_eq!(actual, expected, "{rows} of 2^{row_vars} rows");
        }
    }
}
