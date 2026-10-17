//! SPARK for the block matrices, prover side: a proof that `value = uᵀ(A_0 + αB_0 + α²C_0)w` for lincheck's terminal
//! weights, against a commitment to the block's sparse structure made once. The protocol and its verifier are
//! `verifier::binary_spartan::spark`.
//!
//! The statement (`α`, the weights, `value`) must already be fixed by the caller's transcript: nothing of it is
//! re-observed here.

use crate::block::{BlockMatrices, Csr};
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::ProverState;
use leanvm_core::gkr::{RootShape, prove_product_triple};
use pcs::whir::{ProverConfig, ProverData, commit as whir_commit, config_for_rate, recursive_prover_with_basis};
use primitives::field::{F64, F192, mul_by_g, powers};
use primitives::log2_ceil_usize;
use primitives::multilinear::{eq_table, interp, mle_eval, poly_eval};

pub use verifier::binary_spartan::spark::Key as SparkVerifierKey;

/// Smallest committed stack: the WHIR level ladder's floor, shared with leanVM's witness.
const MIN_LOG_N: usize = leanvm_core::pcs::MIN_MU;

// Slots of the preprocessed stack, each `2^max(l, k)` words.
const ROW: usize = 0;
const COL: usize = 1;
const TAG_A: usize = 2;
const READ_TS_ROW: usize = 5;
const READ_TS_COL: usize = 6;
const FINAL_TS_ROW: usize = 7;
const FINAL_TS_COL: usize = 8;
const PRE_SLOTS: usize = 9;

// Slots of the online stack, each `2^l` words: the limbs of `e_u`, then those of `e_w`.
const E_U: usize = 0;
const E_W: usize = 3;
const ONLINE_SLOTS: usize = 6;

/// A committed stack of `slots` columns of `2^slot_log` words, padded to `2^log_n` words of which only the leading
/// `n_lanes` lane blocks are encoded.
struct Layout {
    slot_log: usize,
    log_n: usize,
    n_lanes: usize,
    config: ProverConfig,
}

impl Layout {
    fn new(slots: usize, slot_log: usize, log_inv_rate: usize) -> Self {
        let log_n = (slot_log + log2_ceil_usize(slots)).max(MIN_LOG_N);
        let config = config_for_rate(log_n, log_inv_rate)
            .unwrap_or_else(|e| panic!("whir config for log_n={log_n}, log_inv_rate={log_inv_rate}: {e}"));
        let n_lanes = (slots << slot_log).div_ceil(1 << (log_n - config.initial_k));
        Self {
            slot_log,
            log_n,
            n_lanes,
            config,
        }
    }

    fn committed_len(&self) -> usize {
        self.n_lanes << (self.log_n - self.config.initial_k)
    }

    fn offset(&self, slot: usize) -> usize {
        slot << self.slot_log
    }

    fn commit(&self, stack: &[F64]) -> (Hash, ProverData) {
        let (commitment, data) = whir_commit(stack, self.log_n, self.config.initial_k, self.config.log_inv_rates[0]);
        (commitment.root, data)
    }
}

/// The preprocessed block: its committed stack (rows, columns, tags, timestamps) and the commitment's opening data.
pub struct SparkProverKey {
    k_log: usize,
    nnz_log: usize,
    pre: Layout,
    online: Layout,
    root: Hash,
    stack: Vec<F64>,
    data: ProverData,
}

impl SparkProverKey {
    pub fn verifier_key(&self) -> SparkVerifierKey {
        SparkVerifierKey {
            nnz_log: self.nnz_log,
            root: self.root,
        }
    }

    /// One `2^len_log`-word column of the preprocessed stack.
    fn column(&self, slot: usize, len_log: usize) -> &[F64] {
        &self.stack[self.pre.offset(slot)..][..1 << len_log]
    }
}

/// An opening claim `MLE(stack[offset .. offset + 2^|point|])(point) = value`.
struct Claim {
    offset: usize,
    point: Vec<F192>,
    value: F192,
}

/// Send `MLE(table)(point)` and record it as a claim on the stack slice at `offset`.
fn send(ps: &mut ProverState, claims: &mut Vec<Claim>, offset: usize, table: &[F64], point: &[F192]) {
    let value = mle_eval(table, point);
    ps.add_scalar(value);
    claims.push(Claim {
        offset,
        point: point.to_vec(),
        value,
    });
}

/// Commit the block's nonzeros: preprocessing is deterministic in `block` and `log_inv_rate`.
pub fn preprocess(block: &BlockMatrices, log_inv_rate: usize) -> SparkProverKey {
    let k = block.k_log;
    let size = 1usize << k;
    let matrices: [&Csr; 3] = [&block.a, &block.b, &block.c];
    let nnz: usize = matrices.iter().map(|m| m.nnz()).sum();
    let nnz_log = log2_ceil_usize(nnz).max(1);
    let n = 1usize << nnz_log;
    let pre = Layout::new(PRE_SLOTS, nnz_log.max(k), log_inv_rate);
    let online = Layout::new(ONLINE_SLOTS, nnz_log, log_inv_rate);

    let mut stack = vec![F64::ZERO; pre.committed_len()];
    let mut ts_row = vec![F64::ONE; size];
    let mut ts_col = vec![F64::ONE; size];
    let entries = matrices.iter().enumerate().flat_map(|(tag, matrix)| {
        assert!(matrix.n_rows() <= size, "matrix has more than 2^{k} rows");
        (0..matrix.n_rows()).flat_map(move |row| matrix.row(row).iter().map(move |&col| (row, col as usize, Some(tag))))
    });
    let padding = std::iter::repeat_n((0, 0, None), n - nnz);
    for (entry, (row, col, tag)) in entries.chain(padding).enumerate() {
        assert!(row < size && col < size, "entry ({row}, {col}) outside the 2^{k} block");
        stack[pre.offset(ROW) + entry] = F64(row as u64);
        stack[pre.offset(COL) + entry] = F64(col as u64);
        if let Some(tag) = tag {
            stack[pre.offset(TAG_A + tag) + entry] = F64::ONE;
        }
        stack[pre.offset(READ_TS_ROW) + entry] = ts_row[row];
        stack[pre.offset(READ_TS_COL) + entry] = ts_col[col];
        ts_row[row] = mul_by_g(ts_row[row]);
        ts_col[col] = mul_by_g(ts_col[col]);
    }
    stack[pre.offset(FINAL_TS_ROW)..][..size].copy_from_slice(&ts_row);
    stack[pre.offset(FINAL_TS_COL)..][..size].copy_from_slice(&ts_col);

    let (root, data) = pre.commit(&stack);
    SparkProverKey {
        k_log: k,
        nnz_log,
        pre,
        online,
        root,
        stack,
        data,
    }
}

/// `y·x` in `E = K[y]/(y³ + y + 1)`: a limb shuffle.
#[inline]
fn mul_y(x: F192) -> F192 {
    F192::new(x.c2, x.c0 ^ x.c2, x.c1)
}

/// A cubic round polynomial's coefficients from `h(0)`, `h(∞)` (its leading coefficient), `h(y)` and the running
/// claim `h(0) + h(1)`. No integer node is used: `y` is the fourth point.
fn cubic_coeffs(claim: F192, h0: F192, h_inf: F192, h_y: F192) -> [F192; 4] {
    // s1 = c1 + c2 and s2 = c1·y + c2·y², so c2·(y + y²) = s2 + s1·y.
    let s1 = claim + h_inf;
    let s2 = h_y + h0 + mul_y(mul_y(mul_y(h_inf)));
    let c2 = (s2 + mul_y(s1)) * F192::new(0, 1, 1).inv();
    [h0, s1 + c2, c2, h_inf]
}

/// Prove `claim = Σ_x t0(x)·t1(x)·t2(x)`, binding the lowest variable first. Returns the challenges.
fn sumcheck_prove(mut claim: F192, mut tables: [Vec<F192>; 3], ps: &mut ProverState) -> Vec<F192> {
    let rounds = log2_ceil_usize(tables[0].len());
    let mut point = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let half = tables[0].len() / 2;
        let mut sums = [F192::ZERO; 3];
        for i in 0..half {
            let [a, b, c] = tables.each_ref().map(|t| (t[2 * i], t[2 * i] + t[2 * i + 1]));
            sums[0] += a.0 * b.0 * c.0;
            sums[1] += a.1 * b.1 * c.1;
            sums[2] += (a.0 + mul_y(a.1)) * (b.0 + mul_y(b.1)) * (c.0 + mul_y(c.1));
        }
        let coeffs = cubic_coeffs(claim, sums[0], sums[1], sums[2]);
        ps.add_round_poly(&coeffs, false);
        let r = ps.sample();
        claim = poly_eval(&coeffs, r);
        for table in &mut tables {
            for i in 0..half {
                table[i] = interp(table[2 * i], table[2 * i + 1], r);
            }
            table.truncate(half);
        }
        point.push(r);
    }
    point
}

/// Offsets, inside a memory-checking tree, of its four segments: the row accesses and the column accesses
/// (`2^l` each), then the row memory and the column memory (`2^k` each), the larger ones first so every segment
/// is aligned to its size.
fn segment_offsets(l: usize, k: usize) -> [usize; 4] {
    let (n, size) = (1usize << l, 1usize << k);
    if l >= k {
        [0, n, 2 * n, 2 * n + size]
    } else {
        [2 * size, 2 * size + n, 0, size]
    }
}

/// The memory-checking fingerprint `a·γ² + v·γ + t + τ`.
struct Fingerprint {
    gamma: F192,
    gamma_sq: F192,
    tau: F192,
}

impl Fingerprint {
    fn sample(ps: &mut ProverState) -> Self {
        let gamma = ps.sample();
        let tau = ps.sample();
        Self {
            gamma,
            gamma_sq: gamma.square(),
            tau,
        }
    }

    #[inline]
    fn leaf(&self, address: F64, value: F192, ts: F64) -> F192 {
        self.gamma_sq.mul_base(address) + self.gamma * value + F192::from(ts) + self.tau
    }
}

/// Discharge `claims` against a committed stack in one WHIR run, batched by the powers of one challenge. The claim
/// values already rode the stream.
fn open(ps: &mut ProverState, layout: &Layout, stack: &[F64], data: &ProverData, claims: &[Claim]) {
    let lambdas = powers(ps.sample(), claims.len());
    let mut weight = vec![F192::ZERO; stack.len()];
    let mut target = F192::ZERO;
    for (claim, &lambda) in claims.iter().zip(&lambdas) {
        target += lambda * claim.value;
        for (slot, eq) in weight[claim.offset..].iter_mut().zip(eq_table(&claim.point)) {
            *slot += lambda * eq;
        }
    }
    recursive_prover_with_basis(
        &layout.config,
        layout.log_n,
        stack,
        weight,
        target,
        &data.codeword,
        &data.merkle_tree,
        ps,
    );
}

/// Proves `value = uᵀ(A_0 + αB_0 + α²C_0)w` for the dense weights `u`, `w` over the block's `2^k_log` rows and
/// columns, appending to the caller's transcript, and returns `value`.
pub fn prove(pk: &SparkProverKey, alpha: F192, u: &[F192], w: &[F192], ps: &mut ProverState) -> F192 {
    let (k, l) = (pk.k_log, pk.nnz_log);
    let (n, size) = (1usize << l, 1usize << k);
    assert_eq!(u.len(), size, "row weights must cover the 2^k_log rows");
    assert_eq!(w.len(), size, "column weights must cover the 2^k_log columns");
    let rows = pk.column(ROW, l);
    let cols = pk.column(COL, l);
    let e_u: Vec<F192> = rows.iter().map(|r| u[r.0 as usize]).collect();
    let e_w: Vec<F192> = cols.iter().map(|c| w[c.0 as usize]).collect();

    let mut online = vec![F64::ZERO; pk.online.committed_len()];
    for (base, values) in [(E_U, &e_u), (E_W, &e_w)] {
        for (i, v) in values.iter().enumerate() {
            online[pk.online.offset(base) + i] = F64(v.c0);
            online[pk.online.offset(base + 1) + i] = F64(v.c1);
            online[pk.online.offset(base + 2) + i] = F64(v.c2);
        }
    }
    let (online_root, online_data) = pk.online.commit(&online);
    ps.add_root(&online_root);
    let limb = |slot: usize| &online[pk.online.offset(slot)..][..n];

    let alpha_sq = alpha.square();
    let tags = [0, 1, 2].map(|t| pk.column(TAG_A + t, l));
    let val: Vec<F192> = (0..n)
        .map(|i| F192::from(tags[0][i]) + alpha.mul_base(tags[1][i]) + alpha_sq.mul_base(tags[2][i]))
        .collect();
    let value = (0..n).fold(F192::ZERO, |acc, i| acc + val[i] * e_u[i] * e_w[i]);

    let r_sc = sumcheck_prove(value, [val, e_u.clone(), e_w.clone()], ps);
    let mut pre_claims = Vec::new();
    let mut online_claims = Vec::new();
    for (t, tag) in tags.iter().enumerate() {
        send(ps, &mut pre_claims, pk.pre.offset(TAG_A + t), tag, &r_sc);
    }
    for slot in 0..ONLINE_SLOTS {
        send(ps, &mut online_claims, pk.online.offset(slot), limb(slot), &r_sc);
    }

    let fp = Fingerprint::sample(ps);
    let col_bit = F64(1 << k);
    let offsets = segment_offsets(l, k);
    let len = 2 * (n + size);
    let mut init_writes = vec![F192::ONE; len];
    let mut reads_final = vec![F192::ONE; len];
    let read_ts = [pk.column(READ_TS_ROW, l), pk.column(READ_TS_COL, l)];
    let final_ts = [pk.column(FINAL_TS_ROW, k), pk.column(FINAL_TS_COL, k)];
    let accesses = [(rows, &e_u, F64::ZERO), (cols, &e_w, col_bit)];
    for (memory, (addresses, values, bit)) in accesses.into_iter().enumerate() {
        let offset = offsets[memory];
        for i in 0..n {
            let (address, ts) = (addresses[i] + bit, read_ts[memory][i]);
            init_writes[offset + i] = fp.leaf(address, values[i], mul_by_g(ts));
            reads_final[offset + i] = fp.leaf(address, values[i], ts);
        }
    }
    for (memory, (table, bit)) in [(u, F64::ZERO), (w, col_bit)].into_iter().enumerate() {
        let offset = offsets[2 + memory];
        for a in 0..size {
            let address = F64(a as u64) + bit;
            init_writes[offset + a] = fp.leaf(address, table[a], F64::ONE);
            reads_final[offset + a] = fp.leaf(address, table[a], final_ts[memory][a]);
        }
    }
    let products = prove_product_triple(
        [init_writes, reads_final, vec![F192::ONE]],
        ps,
        RootShape::FirstTwoShared,
    );
    let (z_l, z_k) = (&products.point[..l], &products.point[..k]);
    for (slot, len_log) in [(ROW, l), (COL, l), (READ_TS_ROW, l), (READ_TS_COL, l)] {
        send(ps, &mut pre_claims, pk.pre.offset(slot), pk.column(slot, len_log), z_l);
    }
    for slot in 0..ONLINE_SLOTS {
        send(ps, &mut online_claims, pk.online.offset(slot), limb(slot), z_l);
    }
    for slot in [FINAL_TS_ROW, FINAL_TS_COL] {
        send(ps, &mut pre_claims, pk.pre.offset(slot), pk.column(slot, k), z_k);
    }

    open(ps, &pk.pre, &pk.stack, &pk.data, &pre_claims);
    open(ps, &pk.online, &online, &online_data, &online_claims);
    value
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// A random GF(2) matrix: one row in `sparsity` on average gets 1 or 2 nonzeros.
    fn random_csr(rng: &mut Rng, k: usize, sparsity: u32) -> Csr {
        let mut row_ptr = vec![0];
        let mut cols = Vec::new();
        for _ in 0..1usize << k {
            let count = if rng.next_u32().is_multiple_of(sparsity) {
                1 + rng.next_u32() % 2
            } else {
                0
            };
            let mut row: Vec<u32> = (0..count).map(|_| rng.next_u32() & ((1 << k) - 1)).collect();
            row.sort_unstable();
            row.dedup();
            cols.extend(row);
            row_ptr.push(cols.len() as u32);
        }
        Csr { row_ptr, cols }
    }

    /// The value SPARK proves is the block's matrix form, with more entries than rows and with fewer.
    #[test]
    fn proves_the_matrix_form() {
        let mut rng = Rng::new(1);
        for (k, sparsity) in [(7, 1), (10, 1), (12, 1), (7, 16), (10, 16)] {
            let block = BlockMatrices {
                k_log: k,
                a: random_csr(&mut rng, k, sparsity),
                b: random_csr(&mut rng, k, sparsity),
                c: random_csr(&mut rng, k, sparsity),
            };
            let pk = preprocess(&block, leanvm_core::pcs::TEST_LOG_INV_RATE);
            let (u, w) = (rng.ext_vec(1 << k), rng.ext_vec(1 << k));
            let alpha = rng.ext();
            let value = prove(&pk, alpha, &u, &w, &mut ProverState::from_label(b"spark-test"));
            let direct = [&block.a, &block.b, &block.c]
                .iter()
                .zip([F192::ONE, alpha, alpha.square()])
                .fold(F192::ZERO, |acc, (matrix, coeff)| {
                    let form = (0..matrix.n_rows()).fold(F192::ZERO, |acc, row| {
                        let dot = matrix
                            .row(row)
                            .iter()
                            .fold(F192::ZERO, |acc, &col| acc + w[col as usize]);
                        acc + u[row] * dot
                    });
                    acc + coeff * form
                });
            assert_eq!(value, direct, "k_log = {k}, sparsity = {sparsity}");
        }
    }
}
