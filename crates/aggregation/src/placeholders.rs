//! The constants baked into the guest.

use super::MAX_RECURSIONS;
use super::cells::pack_16_bytes;
use super::child::{QUERY_WINDOW_BITS, QUERY_WINDOWS_CAP, STREAM_CAP, STREAM_CHUNK, merkle_cap_depth, whir_levels};
use super::deferred::{BATCH_LAM_GRIND_BITS, RECURSION_AGG_LABEL};
use super::hints::{DIGIT_GROUP, LX_DIGIT_GROUP, LX_WINDOW};
use super::statement::{BIG_GROUPS, CLAIM_GROUP, STATEMENT_HEADER};
use super::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
use fiat_shamir_prover::merkle::hash_to_scalars;
use fiat_shamir_prover::{FiatShamirState, RATE_SCALARS, grinding_bits};
use lean_da::{CELLS_PER_ROW, DA_MAX_ROWS, LOG_BLOB_SYMBOLS, LOG_CELL_SYMBOLS, LOG_CODEWORD_SYMBOLS};
use lean_vm_core::cpu::{from_scalar, to_scalar};
use lean_vm_core::keccak::{MIN_SHAPE as KECCAK_MIN_SHAPE, SLOT_LOG};
use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F128, g_pow};
use std::collections::BTreeMap;
use verifier::layout::{BYTECODE_SLOT_BITS, N_TABLES, TABLE_LOG_FLOORS};
use verifier::{BATCH_GRINDING_BITS, FOLD_GRINDING_BITS, OOD_GRINDING_BITS, QUERY_GRINDING_BITS};

/// A value as the guest's literal for it: an integer in decimal, a field element as the integer its limbs spell, a
/// list as `[a, b, ...]`.
trait Literal {
    fn literal(&self) -> String;
}

macro_rules! integer_literal {
    ($($t:ty),*) => {$(
        impl Literal for $t {
            fn literal(&self) -> String {
                self.to_string()
            }
        }
    )*};
}
integer_literal!(u32, u64, u128, usize);

impl Literal for F128 {
    fn literal(&self) -> String {
        zkdsl_compiler::f128_literal(to_scalar(self))
    }
}

impl<T: Literal> Literal for [T] {
    fn literal(&self) -> String {
        format!("[{}]", self.iter().map(T::literal).collect::<Vec<_>>().join(", "))
    }
}

impl<T: Literal, const N: usize> Literal for [T; N] {
    fn literal(&self) -> String {
        self.as_slice().literal()
    }
}

impl<T: Literal> Literal for Vec<T> {
    fn literal(&self) -> String {
        self.as_slice().literal()
    }
}

impl<T: Literal + ?Sized> Literal for &T {
    fn literal(&self) -> String {
        (**self).literal()
    }
}

/// The placeholder map being built: `NAME_PLACEHOLDER` to its literal.
#[derive(Default)]
struct Placeholders(BTreeMap<String, String>);

impl Placeholders {
    fn set(&mut self, name: &str, value: impl Literal) {
        let previous = self.0.insert(format!("{name}_PLACEHOLDER"), value.literal());
        assert!(previous.is_none(), "{name} is set twice");
    }

    fn list<T: Literal>(&mut self, name: &str, values: impl IntoIterator<Item = T>) {
        self.set(name, values.into_iter().collect::<Vec<_>>());
    }
}

/// A greedy (Paar) straight-line program computing each row's sum, or product where a row repeats an input:
/// value `inputs + k` is op `k`, the sum or product of two earlier values, the pair most rows share first.
/// Returns the ops and the value holding each (nonempty) row.
fn straight_line(rows: &[Vec<usize>], inputs: usize) -> (Vec<(usize, usize)>, Vec<usize>) {
    let mut rows: Vec<Vec<usize>> = rows.to_vec();
    let mut ops = Vec::new();
    let pairs = |row: &Vec<usize>| {
        let mut out = std::collections::BTreeSet::new();
        for (i, &a) in row.iter().enumerate() {
            for &b in &row[i + 1..] {
                out.insert((a.min(b), a.max(b)));
            }
        }
        out
    };
    loop {
        let mut counts = std::collections::BTreeMap::<(usize, usize), usize>::new();
        for row in &rows {
            for pair in pairs(row) {
                *counts.entry(pair).or_default() += 1;
            }
        }
        // The most shared pair, the first of them; once none is shared, any pair left.
        let Some((&(a, b), _)) = counts.iter().rev().max_by_key(|&(_, &n)| n) else {
            break;
        };
        let new = inputs + ops.len();
        ops.push((a, b));
        for row in &mut rows {
            if let Some(i) = row.iter().position(|&v| v == a) {
                row.remove(i);
                if let Some(j) = row.iter().position(|&v| v == b) {
                    row.remove(j);
                    row.push(new);
                } else {
                    row.insert(i, a);
                }
            }
        }
    }
    let outputs = rows
        .iter()
        .map(|row| {
            assert_eq!(row.len(), 1, "a straight-line row is nonempty");
            row[0]
        })
        .collect();
    (ops, outputs)
}

/// Binary polynomials: the quotient and the remainder of `a` by `m`.
fn poly_divmod(mut a: u64, m: u64) -> (u64, u64) {
    let dm = m.ilog2();
    let mut q = 0;
    while a != 0 && a.ilog2() >= dm {
        let shift = a.ilog2() - dm;
        q |= 1 << shift;
        a ^= m << shift;
    }
    (q, a)
}

/// `p`'s irreducible factors, with multiplicity, smallest first.
fn poly_factors(mut p: u64) -> Vec<u64> {
    let mut factors = Vec::new();
    let mut q = 2u64;
    while p > 1 && 64 - q.leading_zeros() <= (64 - p.leading_zeros()) {
        let (quotient, rem) = poly_divmod(p, q);
        if rem == 0 {
            factors.push(q);
            p = quotient;
        } else {
            q += 1;
        }
    }
    factors
}

/// The recursion program's placeholder map depends on table structure and bytecode
/// size, so one compiled guest serves every proof layout.
pub(super) fn placeholder_map(kbc: usize) -> BTreeMap<String, String> {
    let mut ph = Placeholders::default();
    constants(&mut ph);
    keccak_placeholders(&mut ph);
    field_placeholders(&mut ph);
    opening_placeholders(&mut ph, kbc);
    bytecode_placeholders(&mut ph, kbc);
    da_placeholders(&mut ph);
    signature_placeholders(&mut ph);
    stack_placeholders(&mut ph);
    link_placeholders(&mut ph, kbc);
    ph.0
}

/// The placeholders that do not depend on the bytecode: copies of the protocol's, the schemes' and this crate's
/// constants, and the grinds, each `grinding_bits` of its challenge's numerator as the prover takes it (zero bits is
/// no nonce).
fn constants(ph: &mut Placeholders) {
    use lean_sphincs::internals as sp;
    use lean_xmss::internals as lx;
    use verifier::keccak::{PACK, PRODUCT_BITS};
    let nonces = |bits: u32| usize::from(bits > 0);
    // The guest takes the ring switch's packed draw from a grind's permutation: every cell but the proof of work's.
    const { assert!(BATCH_GRINDING_BITS > 0, "the ring switch grinds") };
    // The F128 tower F64[Y]/(Y^2 + xY + 1): Y_TOWER embeds Y to reassemble a word `lo + hi·Y`; Y_INV = Y + x splits
    // a word into its two K limbs.
    let y_tower = F128::new(0, 1);
    let shape = KECCAK_MIN_SHAPE;
    let constants: &[(&str, &dyn Literal)] = &[
        // Buffer caps and memory bounds.
        ("STREAM_CAP", &STREAM_CAP),
        ("STREAM_CHUNK", &STREAM_CHUNK),
        ("QW", &QUERY_WINDOW_BITS),
        ("QUERY_WINDOWS_CAP", &QUERY_WINDOWS_CAP),
        ("MIN_LOG_MEM", &verifier::MIN_LOG_MEMORY),
        ("MAX_LOG_MEM", &verifier::MAX_LOG_MEMORY),
        ("INV_GEN", &F128::from(F64::G.inv())),
        ("Y_TOWER", &y_tower),
        ("Y_INV", &y_tower.inv()),
        // The tables.
        ("N_TABLES", &N_TABLES),
        ("FLOORS", &TABLE_LOG_FLOORS),
        // The grinds: a sumcheck round of degree `d`, eq factor included, then each other challenge the guest
        // grinds for.
        ("ROUND2_GRIND_BITS", &grinding_bits(2)),
        ("ROUND3_GRIND_BITS", &grinding_bits(3)),
        // The Keccak segment then the lane, 25 lanes in five coordinates.
        ("KECCAK_SEG_GRIND_BITS", &grinding_bits((shape.seg_log() + 5) as u128)),
        ("KECCAK_S_GRIND_BITS", &grinding_bits(PRODUCT_BITS as u128 - 1)),
        ("KECCAK_BETA_GRIND_BITS", &grinding_bits(2)),
        ("BATCH_LAM_GRIND_BITS", &BATCH_LAM_GRIND_BITS),
        ("FOLD_GRIND_BITS", &FOLD_GRINDING_BITS),
        ("OOD_GRIND_BITS", &OOD_GRINDING_BITS),
        ("QUERY_GRIND_BITS", &QUERY_GRINDING_BITS),
        ("BATCH_GRIND_BITS", &BATCH_GRINDING_BITS),
        // The batching hints: the challenge's nonce, if it grinds, then per round (g1, g_inf) and its nonce, if any.
        ("BC_LAM_WORDS", &nonces(BATCH_LAM_GRIND_BITS)),
        ("BC_ROUND_WORDS", &(2 + nonces(grinding_bits(2)))),
        // The Keccak reduction (`keccak_gkr`).
        ("KECCAK_DEPTH", &shape.depth()),
        ("KECCAK_SEGMENTS", &shape.segments()),
        ("KECCAK_SEG_LOG", &shape.seg_log()),
        ("KECCAK_PACK", &PACK),
        ("KECCAK_PROD_BITS", &PRODUCT_BITS),
        ("KECCAK_PI", &keccak256::PI),
        ("KECCAK_RHO", &keccak256::RHO),
        ("KECCAK_STATE", &isa::STATE_CELLS),
        ("QKECCAK_SLOT_LOG", &SLOT_LOG),
        ("QKECCAK_VARS_CAP", &(33 + SLOT_LOG)),
        // The stacked opening and the statement.
        ("N_COLUMN_LOGS", &(verifier::MAX_STACKED_LOG + 1)),
        ("LIG_N_RATES", &(MAX_LOG_INV_RATE - MIN_LOG_INV_RATE + 1)),
        ("LOG2_BYTECODE_COLS", &BYTECODE_SLOT_BITS),
        ("STMT_HEADER", &STATEMENT_HEADER),
        // LeanDA (`doc/leanvm` §sec:leanda).
        ("LOG_BLOB_SYMBOLS", &LOG_BLOB_SYMBOLS),
        ("LOG_CELL_SYMBOLS", &LOG_CELL_SYMBOLS),
        ("DA_MAX_ROWS", &DA_MAX_ROWS),
        ("DA_LOG_MAX_ROWS", &DA_MAX_ROWS.ilog2()),
        // Both signature schemes (WOTS+C's chain length is both's) and the coverage caps.
        ("W", &lx::W),
        ("DIGIT_GROUP", &DIGIT_GROUP),
        ("LX_V", &lx::V),
        ("LX_TARGET_SUM", &lx::TARGET_SUM),
        ("LX_HEIGHT", &lx::LAYER_HEIGHT),
        ("LX_WINDOW", &LX_WINDOW),
        ("LX_DIGIT_GROUP", &LX_DIGIT_GROUP),
        ("CLAIM_GROUP", &CLAIM_GROUP),
        ("BIG_GROUPS", &BIG_GROUPS),
        ("MAX_RECURSIONS", &MAX_RECURSIONS),
        ("SP_V", &sp::V),
        ("SP_TARGET_SUM", &sp::TARGET_SUM),
        ("SP_FORS_TREES", &sp::FORS_TREES),
        ("SP_FORS_HEIGHT", &sp::FORS_HEIGHT),
        ("SP_DIGEST_BYTES", &sp::DIGEST_BYTES),
    ];
    for &(name, value) in constants {
        ph.set(name, value);
    }
}

/// Where each of the lists of these lengths starts in their concatenation.
fn prefix_sums(lens: impl Iterator<Item = usize>) -> Vec<usize> {
    lens.scan(0, |at, len| {
        let start = *at;
        *at += len;
        Some(start)
    })
    .collect()
}

/// The Keccak reduction's RMFE projection and embedding as straight-line programs, and its iota and linear layer, as
/// index lists the guest unrolls.
fn keccak_placeholders(ph: &mut Placeholders) {
    use verifier::keccak::{EMBED_BITS, PACK, PRODUCT_BITS, RMFE_EMBED, RMFE_PROJECT};
    let shape = KECCAK_MIN_SHAPE;
    let (depth, segments) = (shape.depth(), shape.segments());
    // `starts[i]..starts[i + 1]` indexes row `i`'s entries of the flat list: each row's
    // offset, then the end.
    let mut lists = |starts: &str, entries: &str, rows: Vec<Vec<usize>>| {
        ph.set(starts, prefix_sums(rows.iter().map(Vec::len).chain([0])));
        ph.set(entries, rows.concat());
    };
    let bits = |word: u64, n: usize| (0..n).filter(|b| word >> b & 1 == 1).collect::<Vec<_>>();
    assert!(segments > 1, "the guest opens a committed segment output");
    // Each unit vector's embedding is a product of small irreducible factors (the modulus's,
    // by the CRT): the factors' monomials, then a straight line of products over them.
    let factored: Vec<Vec<u64>> = RMFE_EMBED.iter().map(|&e| poly_factors(e as u64)).collect();
    let clmul = |a: u64, b: u64| (0..64).filter(|i| b >> i & 1 == 1).fold(0, |acc, i| acc ^ a << i);
    for (row, &e) in factored.iter().zip(&RMFE_EMBED) {
        assert_eq!(row.iter().fold(1, |acc, &f| clmul(acc, f)), e as u64);
    }
    let mut factors: Vec<u64> = factored.concat();
    factors.sort_unstable();
    factors.dedup();
    lists(
        "KECCAK_FAC_START",
        "KECCAK_FAC_IDX",
        factors.iter().map(|&f| bits(f, EMBED_BITS)).collect(),
    );
    // The positions iota flips are `2^i - 1`; per (layer, segment), which `i`.
    lists(
        "KECCAK_IOTA_START",
        "KECCAK_IOTA_IDX",
        (0..depth * segments)
            .map(|at| {
                let round = shape.round(at % segments, at / segments);
                (0..7)
                    .filter(|i| keccak256::positions::iota_bit(round, (1 << i) - 1))
                    .collect()
            })
            .collect(),
    );
    // Each product coefficient's reader, the sum of the instance weights whose projection reads
    // it, as a straight line of sums over the PACK weights.
    let (ops, outputs) = straight_line(
        &(0..PRODUCT_BITS)
            .map(|c| (0..PACK).filter(|&i| RMFE_PROJECT[i] >> c & 1 == 1).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        PACK,
    );
    ph.list("KECCAK_PROJ_A", ops.iter().map(|op| op.0));
    ph.list("KECCAK_PROJ_B", ops.iter().map(|op| op.1));
    ph.set("KECCAK_PROJ_OUT", outputs);
    ph.set("KECCAK_PROJ_CELLS", PACK + ops.len());
    ph.set(
        "KECCAK_FAC_DEG",
        factors.iter().map(|f| 63 - f.leading_zeros()).max().unwrap() + 1,
    );
    let (ops, outputs) = straight_line(
        &factored
            .iter()
            .map(|row| {
                row.iter()
                    .map(|f| factors.binary_search(f).unwrap())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>(),
        factors.len(),
    );
    ph.list("KECCAK_EMB_A", ops.iter().map(|op| op.0));
    ph.list("KECCAK_EMB_B", ops.iter().map(|op| op.1));
    ph.set("KECCAK_EMB_OUT", outputs);
    ph.set("KECCAK_FAC_N", factors.len());
    ph.set("KECCAK_EMB_CELLS", factors.len() + ops.len());
    // The rotations the linear layer's transpose reads a slice table at.
    let mut used = [0usize; 64];
    for rot in keccak256::RHO {
        used[rot as usize] = 1;
        used[(rot as usize + 1) % 64] = 1;
    }
    ph.set("KECCAK_SHIFT_USED", used);
}

/// The F128 coordinate basis and the ring switch's points.
fn field_placeholders(ph: &mut Placeholders) {
    // 1 + g^(2^i).
    let g_squarings = std::iter::successors(Some(F128::from(F64::G)), |g| Some(*g * *g));
    ph.list("INDEX_MLE_FACTORS", g_squarings.take(34).map(|g| F128::ONE + g));
    // Coordinate basis e_i of F128 over F2 (spans the whole field): the 64 binary
    // basis vectors in each of the two tower limbs. The guest uses these vectors to
    // reconstruct a word from its 128 coordinate bits.
    ph.list(
        "COORD_BASIS",
        (0..128).map(|i| match i / 64 {
            0 => F128::new(1u64 << i, 0),
            _ => F128::new(0, 1u64 << (i - 64)),
        }),
    );
    // The ring-switch target's Horner points, inverted: w_p = 1 / z_p, z_p = x^(2^(64 - 8p)) in K.
    ph.list(
        "RING_W",
        (0..8).map(|p| (0..(64 - 8 * p) % 64).fold(F128::new(2, 0), |z, _| z.square()).inv()),
    );
}

/// One candidate of the stacked opening: the WHIR ladder of one size at one rate.
struct OpeningShape {
    folds: Vec<usize>,
    queries: &'static [usize],
    /// The message's columns after each level's folds.
    log_message_columns: Vec<usize>,
    tree_depths: Vec<usize>,
}

/// A value of an opening candidate, and a per-level one.
type Scalar = fn(&OpeningShape) -> usize;
type Level = fn(&OpeningShape, usize) -> usize;

impl OpeningShape {
    fn new(mu: usize, log_inv_rate: usize) -> Self {
        let (config, log_message_columns, tree_depths) =
            whir_levels(mu, log_inv_rate).expect("every candidate stack has a WHIR config");
        let shape = Self {
            folds: config.folds,
            queries: config.queries,
            log_message_columns,
            tree_depths,
        };
        assert!(
            shape.per_level(Self::row_words).iter().enumerate().all(|(lv, &n)| {
                let bytes = if lv == 0 { 8 * n } else { 16 * n };
                bytes <= 1024 && n % 4 == 0
            }),
            "recursive WHIR guest supports Merkle rows of at most 1024 bytes, packed four words to two cells"
        );
        shape
    }

    /// Every level is committed and queried, the yr level last.
    fn levels(&self) -> usize {
        self.folds.len()
    }

    fn yr_log_len(&self) -> usize {
        self.log_message_columns[self.levels() - 1]
    }

    fn per_level(&self, f: Level) -> Vec<usize> {
        (0..self.levels()).map(|lv| f(self, lv)).collect()
    }

    /// A Merkle row's words, one a lane.
    fn row_words(&self, lv: usize) -> usize {
        1 << self.folds[lv]
    }

    fn cap_depth(&self, lv: usize) -> usize {
        merkle_cap_depth(self.queries[lv], self.tree_depths[lv])
    }

    /// The query positions one squeezed word carries.
    fn positions(&self, lv: usize) -> usize {
        128 / self.tree_depths[lv]
    }

    fn squeezes(&self, lv: usize) -> usize {
        self.queries[lv].div_ceil(self.positions(lv))
    }

    fn folds_before(&self, lv: usize) -> usize {
        self.folds[..lv].iter().sum()
    }

    /// The query positions of the levels before `lv`, as many as each squeezes, the levels one after another.
    fn positions_before(&self, lv: usize) -> usize {
        (0..lv).map(|l| self.squeezes(l) * self.positions(l)).sum()
    }
}

/// The stacked opening's candidate tables, one per committed size and rate: every size the native verifier accepts of
/// an execution of the guest's bytecode, `min_execution_stacked_log(kbc)..=MAX_STACKED_LOG`.
fn opening_placeholders(ph: &mut Placeholders, kbc: usize) {
    let (minm, maxm) = (
        verifier::layout::min_execution_stacked_log(kbc),
        verifier::MAX_STACKED_LOG,
    );
    let n_log_sizes = maxm - minm + 1;
    // The guest's rate selector is `g^rate / g`.
    const _: () = assert!(MIN_LOG_INV_RATE == 1);
    let cands: Vec<OpeningShape> = (MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE)
        .flat_map(|r| (minm..=maxm).map(move |m| OpeningShape::new(m, r)))
        .collect();
    let maxlev = cands.iter().map(OpeningShape::levels).max().unwrap();
    // The guest rotates the terminal point by the lane-fold count to index it by
    // witness coordinate, and the residual segment is what it rotates the last
    // lane challenges past, so the residual may never be longer than that fold
    // (`RESIDUAL_MAX_LOG` < `INITIAL_FOLDING_FACTOR` keeps this true by a margin).
    assert!(
        cands.iter().all(|c| c.yr_log_len() <= c.folds[0]),
        "residual longer than the lane fold: the guest's point rotation has no room"
    );
    // A high part's index bits; the guest's HIGH_BITS_CAP is 3.
    assert!(cands.iter().all(|c| c.folds.iter().all(|&k| k <= 8)));
    let per_candidate: [(&str, Scalar); 6] = [
        ("LIG_N_LEVELS", OpeningShape::levels),
        ("LIG_YR_LEVEL", |c| c.levels() - 1),
        ("LIG_YR_LOG_LEN", OpeningShape::yr_log_len),
        ("LIG_YR_LEN", |c| 1 << c.yr_log_len()),
        ("LIG_TOTAL_FOLDS", |c| c.folds.iter().sum()),
        ("LIG_POS_TOTAL", |c| c.positions_before(c.levels())),
    ];
    let per_level: [(&str, Level); 12] = [
        ("LIG_QUERIES", |c, lv| c.queries[lv]),
        ("LIG_FOLDS", |c, lv| c.folds[lv]),
        // 128-bit cells per leaf row: level 0's committed rows are base-field
        // F64 (8 bytes/lane, two lanes a cell); deeper levels are native F128,
        // one word a cell.
        ("LIG_LEAF_CELLS", |c, lv| {
            if lv == 0 { c.row_words(lv) / 2 } else { c.row_words(lv) }
        }),
        ("LIG_TREE_DEPTH", |c, lv| c.tree_depths[lv]),
        ("LIG_CAP_DEPTH", OpeningShape::cap_depth),
        ("LIG_SQUEEZES", OpeningShape::squeezes),
        ("LIG_LOG_MSG_COLS", |c, lv| c.log_message_columns[lv]),
        ("LIG_RESIDUAL_FOLD_OFF", |c, lv| c.folds_before(lv + 1)),
        ("LIG_RESIDUAL_PREFIX_LEN", |c, lv| {
            c.log_message_columns[lv] - c.yr_log_len()
        }),
        ("LIG_HIGH_BITS", |c, lv| {
            c.folds[lv].next_power_of_two().trailing_zeros() as usize
        }),
        ("LIG_FOLDS_OFF", OpeningShape::folds_before),
        ("LIG_POS_OFF", OpeningShape::positions_before),
    ];
    // `open_stacked` has one arm per size and reads these at the size's first-rate row: a rate changes none of them.
    const SIZE_ONLY: [&str; 8] = [
        "LIG_N_LEVELS",
        "LIG_YR_LEVEL",
        "LIG_YR_LOG_LEN",
        "LIG_FOLDS",
        "LIG_LOG_MSG_COLS",
        "LIG_LEAF_CELLS",
        "LIG_FOLDS_OFF",
        "LIG_RESIDUAL_FOLD_OFF",
    ];
    // One row per candidate, rates outer, sizes inner.
    let mut table = |name: &str, rows: Vec<Vec<usize>>| {
        assert!(
            !SIZE_ONLY.contains(&name) || rows.iter().enumerate().all(|(i, row)| *row == rows[i % n_log_sizes]),
            "the size-only opening table {name} varies by rate"
        );
        ph.set(name, rows.concat());
    };
    for (name, f) in per_candidate {
        table(name, cands.iter().map(|c| vec![f(c)]).collect());
    }
    for (name, f) in per_level {
        let padded = |c: &OpeningShape| {
            let mut row = c.per_level(f);
            row.resize(maxlev, 0);
            row
        };
        table(name, cands.iter().map(padded).collect());
    }
    // A per-level value's most over every candidate.
    let most = |f: Level| cands.iter().flat_map(|c| c.per_level(f)).max().unwrap();
    // `decode_query_windows`: a squeezed word's positions, each its path bits QW at a time, then the cap
    // child bit and the cap index, read back through `win_tabs`' 128 bit patterns.
    let windows = most(|c, lv| {
        let (depth, cap) = (c.tree_depths[lv], c.cap_depth(lv));
        assert!((2..=8).contains(&cap), "a cap of {cap} levels");
        c.positions(lv) * ((depth - cap).div_ceil(QUERY_WINDOW_BITS) + 2)
    });
    assert!(
        windows <= QUERY_WINDOWS_CAP,
        "a squeezed word's windows past QUERY_WINDOWS_CAP"
    );
    let max_cols = most(|c, lv| c.log_message_columns[lv]);
    ph.set("LIG_LOG_MSG_COLS_CAP", max_cols);
    ph.set("YR_LOG_CAP", most(|c, _| c.yr_log_len()));
    // A row is its hinted words, one a lane: K at level 0, packed two to a cell, E deeper.
    ph.set("LIG_ROW_CAP", most(OpeningShape::row_words));
    ph.set("LIG_PACKED_ROW_CAP", most(|c, _| c.row_words(0) / 2));
    ph.set("LIG_PATH_CAP", most(|c, lv| 2 * (c.tree_depths[lv] - c.cap_depth(lv))));
    ph.set("LIG_MAX_LEVELS", maxlev);
    ph.set("LIG_MIN_LOG_SIZE", minm);
    ph.set("LIG_N_LOG_SIZES", n_log_sizes);
    ph.set("LIG_MIN_SHIFT_INV", F128::from(g_pow(minm).inv()));
    // The subspace-vanishing values of a level's message columns and their inverses, by the column count: block `n`
    // at n(n+1)/2.
    let by_cols: Vec<F64> = (0..=max_cols)
        .flat_map(|cols| {
            let values = verifier::subspace_roots(cols);
            assert_eq!(values.len(), cols + 1);
            values.into_iter().map(|v| F64(v.0))
        })
        .collect();
    ph.list("VANISH_BY_COLS", by_cols.iter().map(|&v| F128::from(v)));
    ph.list("VANISH_INVS_BY_COLS", by_cols.iter().map(|v| F128::from(v.inv())));
}

/// The stack's blocks and their groups, as `certify_stack` reads them.
fn stack_placeholders(ph: &mut Placeholders) {
    let blocks = verifier::layout::stack_blocks();
    let starts = super::child::block_groups(&blocks);
    ph.set("N_STK_BLOCKS", blocks.len());
    ph.list(
        "STK_SRC",
        blocks.iter().map(|block| super::child::source_index(block.source)),
    );
    ph.list("STK_ADJ", blocks.iter().map(|block| block.adj));
    ph.set("N_STK_GROUPS", starts.len());
    ph.list("STK_GROUP_START", starts.iter().copied().chain([blocks.len()]));
    ph.set("STK_STRIDE", blocks.len() + 1);
    ph.set("STK_MIN_LOG", verifier::layout::MIN_STACKED_LOG);
}

/// The deferred claim on the split program, the batch's seed, and the statement's layout.
fn bytecode_placeholders(ph: &mut Placeholders, kbc: usize) {
    use super::split::{KIND_ADDR, KIND_BC, KIND_WORD, SPLIT_LOG, split_terms};
    ph.set("BYTECODE_LOG", kbc);
    let (columns, terms) = split_terms();
    // A fresh claim is the link point's instruction coordinates and the split columns' values there; a carried one,
    // the point (instructions, then columns) and its value.
    let defer_size = kbc + columns.len();
    ph.set("DEFER_SIZE", defer_size);
    ph.set("N_SPLIT", columns.len());
    ph.set("SPLIT_LOG", SPLIT_LOG);
    ph.set("BYTECODE_VARS", kbc + SPLIT_LOG);
    ph.set("N_SPLIT_TERMS", terms.len());
    ph.list("PW_COL", terms.iter().map(|t| t.column));
    ph.list("PW_FRAME", terms.iter().map(|t| usize::from(t.frame)));
    ph.list("PW_KIND", terms.iter().map(|t| t.kind));
    ph.list("PW_ARG", terms.iter().map(|t| t.arg));
    ph.list("PW_COEF", terms.iter().map(|t| from_scalar(t.coef)));
    assert_eq!([KIND_BC, KIND_ADDR, KIND_WORD], [0, 1, 2], "the guest's term kinds");
    let agg_seed = FiatShamirState::<F128>::from_label(RECURSION_AGG_LABEL).capacity_cells();
    for (c, cell) in agg_seed.iter().enumerate() {
        ph.set(&format!("AGG_SEED_{c}"), cell);
    }
    // A child's words: its statement's two, its fresh claim, and its carried claim's cells.
    let child_words = 2 + defer_size + kbc + SPLIT_LOG + 1;
    ph.set(
        "AGG_CHILD_PAD",
        child_words.next_multiple_of(RATE_SCALARS) - child_words,
    );
}

/// LeanDA (`doc/leanvm` §sec:leanda).
fn da_placeholders(ph: &mut Placeholders) {
    let [pad_0, pad_1]: [F128; 2] = hash_to_scalars(&lean_da::root_of_padding_blob());
    ph.set("DA_PAD_BLOB_0", pad_0);
    ph.set("DA_PAD_BLOB_1", pad_1);
    // `Vhat_j` at the domain point whose bits above `j` are `y`'s, `Σ_l bit_l(y) · β_(j+1+l)`: the NTT's twiddles.
    // `Vhat_j(β_j) = 1` and the bits below `j` vanish, so `Vhat_j` at point `i` is `bit_j(i)` plus this at
    // `i >> (j + 1)`: the factors the guest builds `L` from.
    let ntt = AdditiveNttF64::standard(LOG_CODEWORD_SYMBOLS);
    let vhat = |j: usize, y: usize| {
        assert!(
            j <= LOG_BLOB_SYMBOLS && y >> (LOG_BLOB_SYMBOLS - j) == 0,
            "bits above {j} only"
        );
        ntt.twiddle(LOG_BLOB_SYMBOLS - j, y)
    };
    // `Vhat_j` at each parent node `n` of a product tree over bits `top, top - 1, ...`, in heap
    // order: `j` the bit `n` splits, the point its path's bits make.
    let tree = |top: usize, depth: usize| -> Vec<u64> {
        (0..1usize << depth)
            .map(|n| n.checked_ilog2().map_or(0, |d| vhat(top - d as usize, n - (1 << d)).0))
            .collect()
    };
    let cell_bits = CELLS_PER_ROW.ilog2() as usize;
    let (top_tree, cell_tree) = (
        tree(LOG_BLOB_SYMBOLS, cell_bits),
        tree(LOG_CELL_SYMBOLS - 1, LOG_CELL_SYMBOLS),
    );
    ph.list("DA_VHAT", top_tree.into_iter().chain(cell_tree));
    // `Vhat_j(beta_(LOG_CELL_SYMBOLS + b))` for each factor `j` inside a cell and bit `b` of the cell index.
    let column = (0..cell_bits).flat_map(|b| (0..LOG_CELL_SYMBOLS).map(move |j| (j, b)));
    ph.list(
        "DA_VHAT_COLUMN",
        column.map(|(j, b)| vhat(j, 1 << (LOG_CELL_SYMBOLS - 1 - j + b)).0),
    );
}

// A leanSPHINCS chain step's address is WOTS_HASH's, the type the guest leaves zero.
const _: () = assert!(lean_sphincs::internals::WOTS_HASH == 0);

/// Both signature schemes' addresses and dispatch tables.
fn signature_placeholders(ph: &mut Placeholders) {
    use lean_sphincs::internals::{self as sp, Adrs};
    use lean_xmss::internals as lx;
    // Both schemes' WOTS+C: the digit sums of a dispatched group.
    let widest = LX_DIGIT_GROUP.max(DIGIT_GROUP);
    ph.list(
        "DIGIT_SUMS",
        (0..lx::CHAIN_LEN.pow(widest as u32)).map(|k| {
            (0..widest)
                .map(|r| k / lx::CHAIN_LEN.pow(r as u32) % lx::CHAIN_LEN)
                .sum::<usize>()
        }),
    );
    // leanXMSS: its hash types as its address lane holds them. Its addresses are
    // derived per signature from the leaf index the signature carries.
    let address = |tw| pack_16_bytes(&lx::address(&tw));
    for (name, tag) in [
        ("TW_CHAIN", lx::TWEAK_CHAIN),
        ("TW_LEAF", lx::TWEAK_LEAF),
        ("TW_NODE", lx::TWEAK_NODE),
        ("TW_MSG", lx::TWEAK_MSG),
    ] {
        ph.set(name, address(lx::tweak(tag, 0, 0)));
    }
    ph.set("LX_TOP", address(lx::tweak(0, lx::TOP, 0)));
    ph.list(
        "LX_GROUP_SIZES",
        (0..lx::V.div_ceil(LX_DIGIT_GROUP)).map(|p| LX_DIGIT_GROUP.min(lx::V - LX_DIGIT_GROUP * p)),
    );
    // A chain index: zero and the powers of two are cells the guest has, the others a
    // slot of the tags it carries.
    let (mut slots, mut logs, mut n_tags) = (Vec::new(), Vec::new(), 0usize);
    for i in 0..lx::V {
        let carried = i != 0 && !i.is_power_of_two();
        n_tags += usize::from(carried);
        slots.push(if carried { n_tags } else { 0 });
        logs.push(i.checked_ilog2().unwrap_or(0));
    }
    ph.set("LX_TAG_SLOT", slots);
    ph.set("LX_TAG_LOG", logs);
    ph.set("LX_N_TAGS", n_tags);

    // The leanSPHINCS instance: each address type as A1, the address's second cell,
    // holds it, and the cell bit each address field's low bytes start at.
    // The guest derives the rest of every address from the digest.
    let cell = |adrs: Adrs, half: usize| pack_16_bytes(&adrs.as_bytes()[16 * half..][..16]);
    let at = Adrs::new(0, 0);
    for (name, adrs, half) in [
        ("SP_LAYER_MUL", Adrs::new(1, 0), 0),
        ("SP_TREE_MUL_0", Adrs::new(0, 1), 0),
        ("SP_TREE_MUL_1", Adrs::new(0, 1 << 8), 0),
        ("SP_TREE_MUL_2", Adrs::new(0, 1 << 16), 0),
        ("SP_KEY_MUL_0", at.with_key_pair(1), 1),
        ("SP_KEY_MUL_1", at.with_key_pair(1 << 8), 1),
        ("SP_WORD2_MUL", at.with_chain(1), 1),
        ("SP_WORD3_MUL_0", at.with_tree_index(1), 1),
        ("SP_WORD3_MUL_1", at.with_tree_index(1 << 8), 1),
    ] {
        ph.set(name, cell(adrs, half));
    }
    for (layer, height) in sp::LAYER_HEIGHTS.iter().enumerate() {
        ph.set(&format!("SP_HEIGHT_{layer}"), height);
    }
    for (name, t) in [
        ("SP_WOTS_PK", sp::WOTS_PK),
        ("SP_TREE", sp::TREE),
        ("SP_FORS_TREE", sp::FORS_TREE),
        ("SP_FORS_ROOTS", sp::FORS_ROOTS),
        ("SP_WOTS_ENC", sp::WOTS_ENC),
    ] {
        ph.set(name, cell(at.with_type(t), 1));
    }
}

/// A form term's missing column, and an output lane's claim target: it reaches no stack block.
const NO_POS: usize = 1000;

/// The link's table structure, from `verifier::layout::tables()`, as `verify_link` reads it.
///
/// The non-pointer columns' values arrive in one run, table by table in local column order (`SENT_*`), so every
/// column a form names is a position in that run. Forms are lists of terms `TERM_COEF * a * b`, a missing factor
/// `NO_POS`. A sent column's claim lands on its own stack block, on a slot of q_keccak (`N_STK_BLOCKS + slot`), or
/// nowhere (an output lane, `NO_POS`).
fn link_placeholders(ph: &mut Placeholders, kbc: usize) {
    use verifier::layout::{
        GLOBAL_COLUMN_BASES, KECCAK_OUT, MEMORY_0, MEMORY_1, OP_JUMP, OP_KECCAK, QKECCAK, qkeccak_slot, stack_blocks,
        tables,
    };
    let tables = tables();
    let blocks = stack_blocks();
    let block_of = |column: usize| blocks.iter().position(|b| b.column == column);
    assert_eq!(
        [MEMORY_0, MEMORY_1, QKECCAK].map(&block_of),
        [Some(0), Some(1), Some(2)],
        "the framework blocks lead the stack"
    );
    // The guest reads q_keccak's claims at h5 + QKECCAK_SLOT_LOG coordinates, its block's size.
    assert_eq!(
        (blocks[2].source, blocks[2].adj),
        (verifier::layout::SizeSource::Table(OP_KECCAK), SLOT_LOG)
    );
    let outputs = KECCAK_OUT..KECCAK_OUT + keccak256::STATE_LANES;

    // The sent run: each table's non-pointer columns.
    let mut sent_pos: Vec<Vec<usize>> = Vec::new();
    let mut sent_target = Vec::new();
    for table in &tables {
        let pointers = table.links.pointers();
        let base = GLOBAL_COLUMN_BASES[table.opcode];
        let mut pos = vec![NO_POS; table.width()];
        for (c, slot) in pos.iter_mut().enumerate().filter(|(c, _)| !pointers.contains(c)) {
            *slot = sent_target.len();
            let column = base + c;
            sent_target.push(match qkeccak_slot(column) {
                _ if table.opcode == OP_KECCAK && outputs.contains(&c) => NO_POS,
                Some(s) => blocks.len() + s,
                None => block_of(column).expect("a sent column is committed"),
            });
        }
        sent_pos.push(pos);
    }
    let n_sent = sent_target.len();

    // Forms over the sent run.
    let (mut form_start, mut coef, mut term_a, mut term_b) = (vec![0], Vec::new(), Vec::new(), Vec::new());
    let mut form = |t: usize, f: &verifier::layout::Form| {
        for (monomial, c) in f.terms() {
            let at = |i: usize| {
                monomial.get(i).map_or(NO_POS, |&local| {
                    let p = sent_pos[t][local];
                    assert_ne!(p, NO_POS, "a form reads a pointer column");
                    p
                })
            };
            assert!(monomial.len() <= 2);
            coef.push(from_scalar(c));
            term_a.push(at(0));
            term_b.push(at(1));
        }
        form_start.push(coef.len());
        form_start.len() - 2
    };
    let pos = |t: usize, local: usize| {
        let p = sent_pos[t][local];
        assert_ne!(p, NO_POS);
        p
    };
    let (mut next0, mut next1, mut pc, mut fp) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let (mut op_start, mut op_form, mut op_slot) = (Vec::new(), Vec::new(), Vec::new());
    let (mut acc_start, mut acc_addr, mut acc_value, mut acc_gate, mut acc_shift, mut acc_ptr) =
        (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    // The word reads: the pointer whose word they weigh, their access, and their scale.
    let (mut wr_ptr, mut wr_acc, mut wr_scale) = (Vec::new(), Vec::new(), Vec::new());
    let (mut ptr_start, mut ptr_block) = (Vec::new(), Vec::new());
    for (t, table) in tables.iter().enumerate() {
        assert_eq!(table.opcode, t);
        let links = &table.links;
        let state = links.state();
        let bc = links.bytecode_link();
        assert_eq!(bc.pc, state.pc, "the program is read at the row's pc");
        pc.push(pos(t, state.pc));
        fp.push(pos(t, state.fp));
        next0.push(form(t, &state.next[0]));
        next1.push(form(t, &state.next[1]));
        op_start.push(op_form.len());
        for (slots, operand) in &bc.operands {
            let f = form(t, operand);
            op_form.push(f);
            op_slot.push(slots[0]);
        }
        let pointers = links.pointers();
        ptr_start.push(ptr_block.len());
        acc_start.push(acc_addr.len());
        for access in &links.memory {
            for read in &access.reads {
                if let verifier::layout::Read::Word { pointer, scale } = read {
                    wr_ptr.push(ptr_start[t] + pointers.iter().position(|p| p == pointer).unwrap());
                    wr_acc.push(acc_addr.len());
                    wr_scale.push(form(t, scale));
                }
            }
            acc_addr.push(form(t, &access.address));
            acc_value.push(form(t, &access.value));
            acc_gate.push(access.gate.map_or(NO_POS, |g| pos(t, g)));
            acc_shift.push(access.shift);
            let k = pointers.iter().position(|&p| p == access.pointer).unwrap();
            assert!(k >= 2, "an access reads its own pointer");
            acc_ptr.push(ptr_start[t] + k);
        }
        // A pointer column on a q_keccak slot is `N_STK_BLOCKS + slot`, as a sent one is.
        for &p in &pointers {
            let column = GLOBAL_COLUMN_BASES[t] + p;
            ptr_block.push(match qkeccak_slot(column) {
                Some(s) => blocks.len() + s,
                None => block_of(column).expect("a pointer column has a block or a slot"),
            });
        }
        assert_eq!(table.n_constraints() > 0, t == OP_JUMP, "only JUMP has identities");
    }
    op_start.push(op_form.len());
    acc_start.push(acc_addr.len());
    ptr_start.push(ptr_block.len());
    let n_pointers = ptr_block.len();
    // The guest weighs a table's pointer columns with one row, at the table's height: each is a block of the table's
    // height, or a q_keccak slot of KECCAK's.
    for (t, w) in ptr_start.windows(2).enumerate() {
        assert!(
            ptr_block[w[0]..w[1]].iter().all(|&b| match blocks.get(b) {
                Some(block) => block.source == verifier::layout::SizeSource::Table(t) && block.adj == 0,
                None => t == OP_KECCAK,
            }),
            "a table's pointer columns share its height"
        );
    }
    let max_shift = tables.iter().map(|t| t.links.max_shift()).max().unwrap();

    // The columns of JUMP's identities, (b + v_cond w, v_cond (b + 1), pc' + b v_pc + (b + 1) g pc,
    // fp' + b v_fp + (b + 1) fp), the successor being the state link's (`guest_jump_identities_match_native`).
    let jump = &tables[OP_JUMP];
    let named = |name: &str| jump.columns.iter().position(|c| c == name).unwrap();
    let [cond, inv, flag, dest, frame] = ["v_cond", "w", "b", "v_pc", "v_fp"].map(named);

    // Pointer chunks by width: the guest's `match` reads row `w`. Its eq tables sit at chunk 0's stride, the widest
    // chunk's from the program's width on, and a shift stays in chunk 0.
    const CHUNK_CAP: usize = 9;
    let (mut d, mut widths, mut idx, mut word) = (vec![0], vec![0; CHUNK_CAP], vec![0; CHUNK_CAP], vec![0; CHUNK_CAP]);
    assert!(max_shift < 1 << verifier::WINDOW_BITS);
    for width in 1..=verifier::MAX_POINTER_WIDTH {
        let chunks = verifier::Chunks::new(width).unwrap();
        let ws = &chunks.widths;
        assert!(ws.len() <= CHUNK_CAP);
        assert!(width < kbc || ws.iter().all(|&w| w <= ws[0]));
        d.push(ws.len());
        let (mut at_idx, mut at_word) = (0usize, 0usize);
        for i in 0..CHUNK_CAP {
            let w = ws.get(i).copied().unwrap_or(0);
            widths.push(w);
            idx.push(at_idx);
            word.push(at_word);
            at_idx += w;
            at_word += if i < ws.len() { 1 << w } else { 0 };
        }
    }
    // The link's grind is one count at every tallest table (at most the width) and every width from the program's
    // on, for a bytecode of at least 2^16 instructions.
    assert!(
        kbc >= 16,
        "the link grind is fixed for programs of 2^16 instructions or more"
    );
    let link_grind = verifier::link_grind_bits(verifier::MAX_POINTER_WIDTH, verifier::MAX_POINTER_WIDTH);
    // The guest always reads the link's nonce after the OOD value, its permutation drawing `θ_0`.
    assert!(link_grind > 0, "the link grinds");
    assert!(
        (kbc..=verifier::MAX_POINTER_WIDTH)
            .all(|w| (0..=verifier::MAX_POINTER_WIDTH).all(|n| verifier::link_grind_bits(n, w) == link_grind))
    );
    let q_vars = n_pointers.next_power_of_two().trailing_zeros() as usize;

    ph.set("LINK_N_SENT", n_sent);
    ph.set("LINK_NO_POS", NO_POS);
    ph.list("SENT_TARGET", sent_target);
    ph.set("SENT_OUT_LANES", sent_pos[OP_KECCAK][KECCAK_OUT]);
    ph.list("FORM_START", form_start);
    ph.list("TERM_COEF", coef);
    ph.list("TERM_A", term_a);
    ph.list("TERM_B", term_b);
    ph.list("STATE_PC", pc);
    ph.list("STATE_FP", fp);
    ph.list("STATE_NEXT0", next0);
    ph.list("STATE_NEXT1", next1);
    ph.list("BC_OP_START", op_start);
    ph.list("BC_OP_FORM", op_form);
    ph.list("BC_OP_SLOT", op_slot);
    ph.list("ACC_START", acc_start);
    ph.list("ACC_ADDR", acc_addr);
    ph.list("ACC_VALUE", acc_value);
    ph.set("N_WORD_READS", wr_ptr.len());
    ph.list("WR_PTR", wr_ptr);
    ph.list("WR_ACC", wr_acc);
    ph.list("WR_SCALE", wr_scale);
    ph.list("ACC_GATE", acc_gate);
    ph.list("ACC_SHIFT", acc_shift);
    ph.set("N_ACCESSES", acc_ptr.len());
    ph.list("ACC_PTR", acc_ptr);
    ph.list("PTR_START", ptr_start);
    ph.list("PTR_BLOCK", ptr_block);
    ph.set("N_POINTERS", n_pointers);
    ph.set("LINK_Q_VARS", q_vars);
    ph.set("LINK_MAX_SHIFT", max_shift);
    ph.set("LINK_GRIND_BITS", link_grind);
    ph.list("JUMP_IDS", [cond, inv, flag, dest, frame].map(|c| sent_pos[OP_JUMP][c]));
    ph.set("MAX_PTR_WIDTH", verifier::MAX_POINTER_WIDTH);
    ph.set("CHUNK_CAP", CHUNK_CAP);
    ph.list("CHUNK_D", d.clone());
    ph.list("CHUNK_WIDTH", widths);
    ph.list("CHUNK_IDX", idx);
    ph.list("CHUNK_WORD", word);
    // The row and pointer rounds' grinds (link::round_coefficients), by the chunks d of the pointer width.
    ph.list(
        "LINK_ROW_GRIND",
        (0..=CHUNK_CAP).map(|d| grinding_bits((d + 2).max(4) as u128) as usize),
    );
    ph.list(
        "LINK_PTR_GRIND",
        (0..=CHUNK_CAP).map(|d| grinding_bits((d + 1).max(3) as u128) as usize),
    );
    ph.set("LINK_D_MIN", d[kbc]);
    ph.set("LINK_JUMP_TABLE", OP_JUMP);
}
