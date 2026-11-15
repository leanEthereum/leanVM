//! The constants baked into the guest.

use super::MAX_RECURSIONS;
use super::cells::pack_16_bytes;
use super::child::{
    MU_CAP, QUERY_WINDOW_BITS, QUERY_WINDOWS_CAP, STREAM_CAP, block_groups, col_groups, merkle_cap_depth, whir_levels,
};
use super::claim_pool::{ClaimSite, claim_pool, coord_difference, coord_kind, coord_scale, push_coord_terms};
use super::deferred::{BATCH_LAM_GRIND_BITS, RECURSION_AGG_LABEL};
use super::hints::{DIGIT_GROUP, LX_DIGIT_GROUP, LX_WINDOW};
use super::statement::{BIG_GROUPS, CLAIM_GROUP, STATEMENT_HEADER};
use super::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
use fiat_shamir_prover::merkle::hash_to_scalars;
use fiat_shamir_prover::{FiatShamirState, RATE_SCALARS, grinding_bits};
use lean_da::{CELLS_PER_ROW, DA_MAX_ROWS, LOG_BLOB_SYMBOLS, LOG_CELL_SYMBOLS, LOG_CODEWORD_SYMBOLS};
use lean_vm_core::constraints::xi_offsets;
use lean_vm_core::cpu::{
    KeccakLane, QKECCAK, block_kappa_sources, col_kappa_sources, keccak_value, layout_of, n_xi_powers, to_scalar,
    xi_form_base,
};
use lean_vm_core::gkr::{ROUND_GRIND, y_grind};
use lean_vm_core::keccak::{MIN_SHAPE as KECCAK_MIN_SHAPE, SLOT_LOG};
use lean_vm_core::leaf::{self, Block, Coord};
use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F128, g_pow};
use std::collections::BTreeMap;
use verifier::bus_grinding_bits;
use verifier::layout::BUS_BITS;
use verifier::layout::{GLOBAL_COLUMN_BASES, N_TABLES, TABLE_LOG_FLOORS, TABLE_WIDTHS, tables};
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

struct ClaimDescriptor {
    buffer: usize,
    column: usize,
    qkeccak_slot: usize,
    /// The kappa source `(src, adj)` of the claim's low dimension.
    source: (usize, usize),
}

// The guest's `POINT_BUF_*`, the point a pooled claim is made at: the bus's `zeta`, the table
// sumcheck's point, the public input's, that point on a slot of `q_keccak`, and none for an
// output lane's, which the Keccak reduction takes as its claim on the permutation's output and
// the opening never sees.
const POINT_BUF_ZETA: usize = 0;
const POINT_BUF_RHO: usize = 1;
const POINT_BUF_PI: usize = 2;
const POINT_BUF_QKECCAK_RHO: usize = 3;
const POINT_BUF_KECCAK_OUT: usize = 4;

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
    // Only block and coordinate structure is used here; stand-in sizes let us derive it before the guest's
    // bytecode exists.
    let layout = layout_of(kbc, 20, [1 << 10; N_TABLES]);
    let sides = [layout.push, layout.pull, layout.count];
    let mut ph = Placeholders::default();
    constants(&mut ph);
    let (pool, coord_claims) = claim_pool(&sides, kbc);
    bus_placeholders(&mut ph, &sides, kbc, &coord_claims);
    claim_placeholders(&mut ph, &pool, kbc);
    keccak_placeholders(&mut ph);
    // The bus's least push depth over every execution of this bytecode: the least memory, every table at its floor.
    // The bus grind sends a nonce at every depth the guest admits, which it absorbs with the OOD sample's value, and
    // the root-most layer is binary and never the last.
    let bus_min_mu = leaf::layout(&layout_of(kbc, verifier::MIN_LOG_MEMORY, [0; N_TABLES]).push).mu;
    assert!(bus_grinding_bits(bus_min_mu) > 0 && bus_min_mu > 2);
    ph.set("BUS_MIN_MU", bus_min_mu);
    field_placeholders(&mut ph);
    opening_placeholders(&mut ph, kbc);
    bytecode_placeholders(&mut ph, &sides, kbc);
    da_placeholders(&mut ph);
    signature_placeholders(&mut ph);
    ph.0
}

/// The placeholders that do not depend on the bytecode: copies of the protocol's, the schemes' and this crate's
/// constants, and the grinds, each `grinding_bits` of its challenge's numerator as the prover takes it (zero bits is
/// no nonce).
fn constants(ph: &mut Placeholders) {
    use lean_sphincs::internals as sp;
    use lean_xmss::internals as lx;
    use verifier::N_BUS_TREES;
    use verifier::keccak::{EMBED_BITS, PACK, PRODUCT_BITS};
    let nonces = |bits: u32| usize::from(bits > 0);
    // The F128 tower F64[Y]/(Y^2 + xY + 1): Y_TOWER embeds Y for AIR lane reassembly; Y_INV = Y + x splits a word
    // into its two K limbs.
    let y_tower = F128::new(0, 1);
    let shape = KECCAK_MIN_SHAPE;
    let constants: &[(&str, &dyn Literal)] = &[
        // Buffer caps and memory bounds.
        ("STREAM_CAP", &STREAM_CAP),
        ("QW", &QUERY_WINDOW_BITS),
        ("QUERY_WINDOWS_CAP", &QUERY_WINDOWS_CAP),
        ("MU_CAP", &MU_CAP),
        ("GKR_ROUNDS_CAP", &(MU_CAP * (MU_CAP + 1) / 2 + MU_CAP + 2)),
        ("GKR_POINTS_CAP", &((MU_CAP + 1) * MU_CAP)),
        ("MIN_LOG_MEM", &verifier::MIN_LOG_MEMORY),
        ("MAX_LOG_MEM", &verifier::MAX_LOG_MEMORY),
        ("INV_GEN", &F128::from(F64::G.inv())),
        ("Y_TOWER", &y_tower),
        ("Y_INV", &y_tower.inv()),
        // The tables, and the table sumcheck's xi layout from the native verifier's own numbers: a disjoint range of
        // identities per table, then one power per bus tree (verifier::N_BUS_TREES), shared by every table. Sharing
        // is what lets the target be derived from the trees' leaf claims instead of trusted (xi_form_base).
        ("N_TABLES", &N_TABLES),
        ("NO_TABLE", &N_TABLES),
        ("FLOORS", &TABLE_LOG_FLOORS),
        ("ETA_OFFSET", &xi_offsets(tables().iter().map(|t| t.n_constraints()))),
        ("ETA_FORM_BASE", &xi_form_base()),
        ("N_ETA_POWS", &n_xi_powers()),
        ("N_TABLE_COLS", &TABLE_WIDTHS),
        ("TABLE_COL_BASE", &xi_offsets(TABLE_WIDTHS.iter().copied())),
        ("N_COL_EVALS", &TABLE_WIDTHS.iter().sum::<usize>()),
        ("TABLE_COLS_CAP", &(TABLE_WIDTHS.iter().max().unwrap() + 1)),
        // The grinds: the bus's by the push depth, a sumcheck round of degree `d`, eq factor included, then each
        // other challenge the guest grinds for.
        ("BUS_GRIND_BITS", &(0..64).map(bus_grinding_bits).collect::<Vec<_>>()),
        ("ROUND2_GRIND_BITS", &grinding_bits(2)),
        ("ROUND3_GRIND_BITS", &grinding_bits(3)),
        ("ROUND5_GRIND_BITS", &ROUND_GRIND),
        ("GKR_COMBINER_GRIND_BITS", &grinding_bits(N_BUS_TREES as u128 - 1)),
        // y: a binary layer's (only ever the root-most, never the last), a radix-four one's, the last layer's doubled.
        ("GKR_Y1_GRIND_BITS", &y_grind(1, false)),
        ("GKR_Y_GRIND_BITS", &y_grind(2, false)),
        ("GKR_Y_LAST_GRIND_BITS", &y_grind(2, true)),
        ("XI_GRIND_BITS", &grinding_bits(n_xi_powers() as u128 - 1)),
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
        ("KECCAK_EMBED_BITS", &EMBED_BITS),
        ("KECCAK_PROD_BITS", &PRODUCT_BITS),
        ("KECCAK_PI", &keccak256::PI),
        ("KECCAK_RHO", &keccak256::RHO),
        ("KECCAK_STATE", &isa::STATE_CELLS),
        ("QKECCAK_SLOT_LOG", &SLOT_LOG),
        ("QKECCAK_VARS_CAP", &(33 + SLOT_LOG)),
        // The stacked opening and the statement.
        ("N_COLUMN_LOGS", &(verifier::MAX_STACKED_LOG + 1)),
        ("PCS_MIN_MU", &verifier::MIN_STACKED_LOG),
        ("LIG_N_RATES", &(MAX_LOG_INV_RATE - MIN_LOG_INV_RATE + 1)),
        ("LOG2_BYTECODE_COLS", &BUS_BITS),
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

/// The bus blocks and their coordinates and terms, given each coordinate's `(fresh, slot)` in the claim pool.
fn bus_placeholders(ph: &mut Placeholders, sides: &[Vec<Block>; 3], kbc: usize, coord_claims: &[(usize, usize)]) {
    let bks = block_kappa_sources(kbc);
    // Each side's first block, then the end.
    let sblk = xi_offsets(sides.iter().map(Vec::len).chain([0]));
    assert_eq!(bks.len(), sblk[3], "a kappa source per block");
    // A TABLE block's coordinates, flattened into terms: the guest rebuilds each as
    // `Σ_terms`, so a derived value (an XOR/MUL result, a DEREF store, a JUMP
    // successor) costs terms rather than columns. A framework coordinate has none:
    // it decomposes into pooled claims instead.
    // Per coordinate: its kind, its constant, its value on its table's padding row (zero for a framework
    // coordinate) and its terms.
    let (mut block_coords, mut coordinates, mut terms) = (Vec::new(), Vec::new(), Vec::new());
    for (blk, &(source, _)) in sides.iter().flatten().zip(&bks) {
        block_coords.push(coordinates.len()..coordinates.len() + blk.coords.len());
        for (i, c) in blk.coords.iter().enumerate() {
            let start = terms.len();
            if let Some(t) = source.checked_sub(2) {
                push_coord_terms(c, GLOBAL_COLUMN_BASES[t], &mut terms);
            }
            let padding = blk.padding.get(i).map_or(0, |v| v.0);
            coordinates.push((coord_kind(c), u128::from(coord_scale(c)), padding, start..terms.len()));
        }
    }
    ph.set("SIDE_BLOCK_START", &sblk);
    ph.set("N_BLOCKS", sblk[3]);
    ph.set("N_COORDS", coordinates.len());
    // Push and pull emit bus blocks in matched pairs, so their baked kappa-source
    // segments are identical; the guest computes only push's side total and
    // aliases pull's mu to push's on this basis.
    assert_eq!(
        bks[sblk[0]..sblk[1]],
        bks[sblk[1]..sblk[2]],
        "push/pull kappa sources must match"
    );
    // The guest also reuses push's padding term for pull, which needs the same padding
    // tuples (a padding row's counts are zero, so a count's `g·` changes nothing).
    assert!(
        sides[0].iter().zip(&sides[1]).all(|(a, b)| a.padding == b.padding),
        "push/pull padding tuples must match"
    );
    let bgroups = block_groups(&bks, &sblk);
    ph.set("N_BLOCK_GROUPS", bgroups.len());
    ph.list("BLOCK_GROUP_START", bgroups.iter().copied().chain([bks.len()]));
    ph.list(
        "SIDE_GROUP_START",
        sblk.iter().map(|&b| bgroups.partition_point(|&start| start < b)),
    );
    ph.list("BLOCK_KAPPA_SRC", bks.iter().map(|&(s, _)| s));
    ph.list("BLOCK_KAPPA_ADJ", bks.iter().map(|&(_, a)| a));
    ph.list(
        "BLOCK_TABLE",
        bks.iter().map(|&(s, _)| s.checked_sub(2).unwrap_or(N_TABLES)),
    );
    ph.list(
        "BLOCK_SIDE",
        sides
            .iter()
            .enumerate()
            .flat_map(|(s, blocks)| std::iter::repeat_n(s, blocks.len())),
    );
    ph.list("BLOCK_COORD_OFF", block_coords.iter().map(|r| r.start));
    ph.list("BLOCK_COORD_COUNT", block_coords.iter().map(|r| r.len()));
    ph.list("COORD_TYPE", coordinates.iter().map(|c| c.0));
    ph.list("COORD_CONST", coordinates.iter().map(|c| c.1));
    ph.list("COORD_PADDING", coordinates.iter().map(|c| c.2));
    ph.list("COORD_TERM_OFF", coordinates.iter().map(|c| c.3.start));
    ph.list("COORD_TERM_COUNT", coordinates.iter().map(|c| c.3.len()));
    let fresh = coord_claims.iter().map(|c| c.0);
    ph.list("COORD_FRESH", fresh.clone());
    // A fresh coordinate's place in the run of words the decomposition absorbs, which
    // decides where it waits in the Fiat-Shamir sponge.
    ph.list("COORD_FRESH_POS", xi_offsets(fresh.clone()));
    ph.set("N_FRESH", fresh.clone().sum::<usize>());
    ph.set("N_BUS_CLAIMS", fresh.sum::<usize>());
    ph.list("COORD_CLAIM_SLOT", coord_claims.iter().map(|c| c.1));
    // A pull table-block coordinate's difference from its push twin's, as merged terms
    // appended after every coordinate's own: the guest counts a pull block's form as
    // push's plus these, the two blocks sharing eq_hi.
    let (mut diff_off, mut diff_count) = (vec![0usize; coordinates.len()], vec![0usize; coordinates.len()]);
    for b in sblk[1]..sblk[2] {
        let (pull, push) = (block_coords[b].clone(), block_coords[b - sblk[1]].clone());
        assert!(
            bks[b] == bks[b - sblk[1]] && pull.len() == push.len(),
            "pull block {b} must mirror its push twin"
        );
        for (p, q) in pull.zip(push) {
            let merged = coord_difference(&terms[coordinates[p].3.clone()], &terms[coordinates[q].3.clone()]);
            diff_off[p] = terms.len();
            diff_count[p] = merged.len();
            terms.extend(merged);
        }
    }
    ph.set("COORD_DIFF_OFF", diff_off);
    ph.set("COORD_DIFF_COUNT", diff_count);
    ph.list("TERM_TYPE", terms.iter().map(|t| t.kind));
    ph.list("TERM_CONST", terms.iter().map(|t| t.constant));
    ph.list("TERM_COL_A", terms.iter().map(|t| t.column_a));
    ph.list("TERM_COL_B", terms.iter().map(|t| t.column_b));
    // 1 + g^(2^i).
    let g_squarings = std::iter::successors(Some(F128::from(F64::G)), |g| Some(*g * *g));
    ph.list("INDEX_MLE_FACTORS", g_squarings.take(34).map(|g| F128::ONE + g));
}

/// The claim pool's descriptors.
fn claim_placeholders(ph: &mut Placeholders, pool: &[ClaimSite], kbc: usize) {
    // Each column's index among the committed ones.
    let mut committed = 0..;
    let compact: Vec<Option<usize>> = (col_kappa_sources(kbc).iter())
        .map(|source| source.map(|_| committed.next().unwrap()))
        .collect();
    let compact_col = |column: usize| compact[column].expect("a claim targets a committed column");
    let qkeccak = compact_col(QKECCAK);
    let claims: Vec<ClaimDescriptor> = (pool.iter())
        .map(|site| match *site {
            ClaimSite::Framework { column, source } => (POINT_BUF_ZETA, compact_col(column), 0, source),
            // A table column's claim is at its table's chi[..tau].
            ClaimSite::TableColumn { column, table } => match keccak_value(column) {
                None => (POINT_BUF_RHO, compact_col(column), 0, (2 + table, 0)),
                Some(KeccakLane::Slot(slot)) => (POINT_BUF_QKECCAK_RHO, qkeccak, slot, (2 + table, 0)),
                Some(KeccakLane::Output(_)) => (POINT_BUF_KECCAK_OUT, qkeccak, 0, (2 + table, 0)),
            },
            ClaimSite::MemoryLimb { column } => (POINT_BUF_PI, compact_col(column), 0, (1, 0)),
        })
        .map(|(buffer, column, qkeccak_slot, source)| ClaimDescriptor {
            buffer,
            column,
            qkeccak_slot,
            source,
        })
        .collect();
    ph.set("N_CLAIMS", claims.len());
    ph.list("CLAIM_POINT_BUF", claims.iter().map(|c| c.buffer));
    ph.list("CLAIM_COMMITTED_COL", claims.iter().map(|c| c.column));
    ph.list("CLAIM_KAPPA_SRC", claims.iter().map(|c| c.source.0));
    ph.list("CLAIM_KAPPA_ADJ", claims.iter().map(|c| c.source.1));
    ph.list(
        "CLAIM_QKECCAK_SLOT_BITS",
        claims
            .iter()
            .flat_map(|c| (0..SLOT_LOG).map(move |k| (c.qkeccak_slot >> k) & 1)),
    );
    // The output lanes' claims, consecutive in the pool: the reduction's claim on the output.
    let out_pool = claims
        .iter()
        .position(|c| c.buffer == POINT_BUF_KECCAK_OUT)
        .expect("the output lanes' claims");
    assert!(
        (0..claims.len()).all(|j| (claims[j].buffer == POINT_BUF_KECCAK_OUT)
            == (out_pool..out_pool + keccak256::STATE_LANES).contains(&j))
    );
    ph.set("KECCAK_OUT_POOL", out_pool);
    // The stacked opening batches the ring-switched claim, the pool's on-stack claims and the
    // Keccak reduction's claim on its output word and level 0's OOD claim; the batching is accounted for up to a cap.
    let stacked = 2 + claims.iter().filter(|c| c.buffer != POINT_BUF_KECCAK_OUT).count() + 1;
    assert!(stacked <= verifier::MAX_STACKED_CLAIMS, "too many stacked claims");
    ph.set("QKECCAK_COMMITTED_COL", qkeccak);
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
        ph.set(starts, xi_offsets(rows.iter().map(Vec::len).chain([0])));
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
        let (config, log_message_columns, tree_depths) = whir_levels(mu, log_inv_rate);
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
}

/// The stacked opening's candidate tables, one per committed size and rate: every size the native verifier accepts of
/// an execution of the guest's bytecode, `min_execution_stacked_log(kbc)..=MAX_STACKED_LOG`.
fn opening_placeholders(ph: &mut Placeholders, kbc: usize) {
    let (minm, maxm) = (verifier::min_execution_stacked_log(kbc), verifier::MAX_STACKED_LOG);
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
    let per_candidate: [(&str, Scalar); 5] = [
        ("LIG_N_LEVELS", OpeningShape::levels),
        ("LIG_YR_LEVEL", |c| c.levels() - 1),
        ("LIG_YR_LOG_LEN", OpeningShape::yr_log_len),
        ("LIG_YR_LEN", |c| 1 << c.yr_log_len()),
        ("LIG_TOTAL_FOLDS", |c| c.folds.iter().sum()),
    ];
    let per_level: [(&str, Level); 11] = [
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
    ph.set("LIG_PATH_CAP", most(|c, lv| 4 * (c.tree_depths[lv] - c.cap_depth(lv))));
    ph.set(
        "LIG_LEVEL_POSITIONS_CAP",
        most(|c, lv| c.squeezes(lv) * c.positions(lv)),
    );
    ph.set("LIG_MAX_LEVELS", maxlev);
    ph.set("LIG_MIN_LOG_SIZE", minm);
    ph.set("LIG_N_LOG_SIZES", n_log_sizes);
    ph.set("LIG_MIN_SHIFT_INV", F128::from(g_pow(minm).inv()));
    let cks: Vec<(usize, usize)> = col_kappa_sources(kbc).into_iter().flatten().collect();
    ph.set("N_COMMITTED_COLS", cks.len());
    ph.list("COL_KAPPA_SRC", cks.iter().map(|&(s, _)| s));
    ph.list("COL_KAPPA_ADJ", cks.iter().map(|&(_, a)| a));
    let groups = col_groups(&cks);
    ph.set("N_COL_GROUPS", groups.len());
    ph.list("COL_GROUP_START", groups.iter().copied().chain([cks.len()]));
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

/// The stacked bytecode's claim, the batch's seed, and the statement's layout.
fn bytecode_placeholders(ph: &mut Placeholders, sides: &[Vec<Block>; 3], kbc: usize) {
    ph.set("BYTECODE_LOG", kbc);
    // The stacked bytecode: an encoding column per side for each two public coordinates, aligned with the bus
    // tuple, so their slots span the fingerprint's own bits. The defer region is
    // the claim's point (row, then slot) and its value.
    let public = sides
        .iter()
        .flatten()
        .flat_map(|b| &b.coords)
        .filter(|c| matches!(c, Coord::Public(_)));
    ph.set("BYTECODE_COLS", public.count() / 2);
    let defer_size = kbc + BUS_BITS + 1;
    ph.set("DEFER_SIZE", defer_size);
    ph.set("BYTECODE_VARS", kbc + BUS_BITS);
    let agg_seed = FiatShamirState::<F128>::from_label(RECURSION_AGG_LABEL).capacity_cells();
    for (c, cell) in agg_seed.iter().enumerate() {
        ph.set(&format!("AGG_SEED_{c}"), cell);
    }
    // A child's words: its statement's two, its fresh claim, and its carried claim's cells.
    let child_words = 2 + 2 * defer_size;
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
