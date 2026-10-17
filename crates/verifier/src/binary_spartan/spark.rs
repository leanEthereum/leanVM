//! SPARK for the block matrices: a proof that `value = u^T (A0 + alpha B0 + alpha^2 C0) w` for lincheck's terminal
//! weights `u`, `w`, which the verifier only evaluates as MLEs, against a commitment to the block's nonzeros made once.
//!
//! The nonzeros of `A0`, `B0`, `C0` are concatenated and padded to `2^l` entries with zero-valued ones (row 0, column
//! 0, no tag). Entry `k` has `row_k`, `col_k` and one-hot tag bits, so `val_k(alpha) = [A] + alpha [B] + alpha^2 [C]`.
//! Preprocessing commits, as one `K` stack: rows, columns, the three tag columns, the read timestamps of the row and
//! column memories (`g^t`, `t` the number of earlier reads of that address) and their final timestamps.
//!
//! Online, the prover commits `e_u[k] = u[row_k]` and `e_w[k] = w[col_k]` as their three `K` limbs and runs a
//! sumcheck for `sum_k val_k e_u[k] e_w[k]`. Offline memory checking then shows `e_u`, `e_w` are reads of `u`, `w`: the
//! row and column memories are one memory of `2^(k+1)` cells (a column address carries bit `k`), a tuple `(a, v, t)`
//! fingerprints as `a gamma^2 + v gamma + t + tau`, and the multisets `Init ∪ Writes` and `Reads ∪ Final` have one
//! product, proven by the GKR grand product with a shared root. Every leaf evaluation the GKR leaves is opened
//! against the two commitments.

use super::{column_weights_mle, row_weights_mle};
use crate::bus::verify_gkr_grand_products;
use crate::field::{E, GEN, K, ONE, ZERO};
use crate::flock::FlockClaims;
use crate::hash::Digest;
use crate::layout::MIN_STACKED_LOG;
use crate::multilinear::{Placement, eq_eval, log2_ceil};
use crate::transcript::{Transcript, sumcheck};
use crate::{StackClaim, VerifierError, require, verify_stacked_opening};

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

/// What the verifier keeps of a preprocessed block: the nonzero count's logarithm and the commitment root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Key {
    pub nnz_log: usize,
    pub root: [u8; 32],
}

/// A committed stack of `slots` columns of `2^slot_log` words, padded to `2^log_n` words.
struct Layout {
    slot_log: usize,
    log_n: usize,
    placed: u64,
}

impl Layout {
    fn new(slots: usize, slot_log: usize) -> Self {
        Self {
            slot_log,
            log_n: (slot_log + log2_ceil(slots as u64)).max(MIN_STACKED_LOG),
            placed: (slots as u64) << slot_log,
        }
    }

    fn offset(&self, slot: usize) -> u64 {
        (slot as u64) << self.slot_log
    }
}

/// Opening claims on one stack: an MLE of the slice at `offset` at a point, each value read off the stream.
struct Claims<'a> {
    layout: &'a Layout,
    claims: Vec<StackClaim<'static>>,
}

impl<'a> Claims<'a> {
    fn new(layout: &'a Layout) -> Self {
        Self {
            layout,
            claims: Vec::new(),
        }
    }

    fn receive(&mut self, transcript: &mut Transcript, slot: usize, point: &[E]) -> Result<E, VerifierError> {
        let value = transcript.next_scalar()?;
        let at = Placement {
            variables: point.len(),
            index: self.layout.offset(slot),
            low: 0,
        }
        .stack_point(point, self.layout.log_n);
        self.claims.push((Box::new(move |x| eq_eval(&at, x)), value));
        Ok(value)
    }

    fn open(self, transcript: &mut Transcript, root: Digest, log_inv_rate: usize) -> Result<(), VerifierError> {
        verify_stacked_opening(
            transcript,
            root,
            self.layout.log_n,
            self.layout.placed,
            log_inv_rate,
            &self.claims,
        )
    }
}

/// `c0 + y c1 + y^2 c2`: an `E` value from its limbs' evaluations.
fn from_limbs(limbs: &[E]) -> E {
    let y = E::new(0, 1, 0);
    limbs[0] + y * (limbs[1] + y * limbs[2])
}

/// The memory-checking fingerprint `a gamma^2 + v gamma + t + tau`.
struct Fingerprint {
    gamma: E,
    tau: E,
}

impl Fingerprint {
    fn eval(&self, address: E, value: E, ts: E) -> E {
        (address * self.gamma + value) * self.gamma + ts + self.tau
    }
}

/// Offsets, inside a memory-checking tree, of its four segments: the row accesses and the column accesses (`2^l`
/// each), then the row memory and the column memory (`2^k` each), the larger ones first so every segment is aligned to
/// its size.
fn segment_offsets(l: usize, k: usize) -> [usize; 4] {
    let (n, size) = (1usize << l, 1usize << k);
    if l >= k {
        [0, n, 2 * n, 2 * n + size]
    } else {
        [2 * size, 2 * size + n, 0, size]
    }
}

/// The MLE at `point` of a tree whose segments evaluate to `segments` at the point's low coordinates, padded with ones
/// past them (the GKR's identity padding).
fn tree_mle(point: &[E], l: usize, k: usize, segments: [E; 4]) -> E {
    let mut covered = ZERO;
    let mut total = ZERO;
    for ((offset, log), value) in segment_offsets(l, k).into_iter().zip([l, l, k, k]).zip(segments) {
        let high = &point[log..];
        let bits: Vec<E> = (0..high.len())
            .map(|j| E::new(((offset >> log) >> j & 1) as u64, 0, 0))
            .collect();
        let weight = eq_eval(&bits, high);
        covered += weight;
        total += weight * value;
    }
    total + ONE + covered
}

/// Verify a SPARK proof that `value` is the block's matrix form at lincheck's terminal weights.
pub(super) fn verify(
    key: &Key,
    k: usize,
    claims: &FlockClaims,
    value: E,
    log_inv_rate: usize,
    transcript: &mut Transcript,
) -> Result<(), VerifierError> {
    let l = key.nnz_log;
    let pre = Layout::new(PRE_SLOTS, l.max(k));
    let online = Layout::new(ONLINE_SLOTS, l);
    let (mut pre_claims, mut online_claims) = (Claims::new(&pre), Claims::new(&online));
    let halves = transcript.next_scalars(2)?;
    let online_root = Digest::from_halves(halves[0], halves[1])?;

    let (r_sc, terminal) = sumcheck(transcript, value, 4, &vec![None; l])?;
    let mut tags = [ZERO; 3];
    for (t, tag) in tags.iter_mut().enumerate() {
        *tag = pre_claims.receive(transcript, TAG_A + t, &r_sc)?;
    }
    let mut limbs = [ZERO; ONLINE_SLOTS];
    for (slot, limb) in limbs.iter_mut().enumerate() {
        *limb = online_claims.receive(transcript, slot, &r_sc)?;
    }
    let alpha = claims.alpha;
    let val = tags[0] + alpha * (tags[1] + alpha * tags[2]);
    require(
        terminal == val * from_limbs(&limbs[E_U..E_U + 3]) * from_limbs(&limbs[E_W..E_W + 3]),
        VerifierError::SparkSumcheck,
    )?;

    let fingerprint = Fingerprint {
        gamma: transcript.sample(),
        tau: transcript.sample(),
    };
    let depth = log2_ceil(2 * ((1u64 << l) + (1u64 << k)));
    let (_, point, products) = verify_gkr_grand_products(depth, transcript)?;
    let (z_l, z_k) = (&point[..l], &point[..k]);
    let mut at_l = [ZERO; 4];
    for (value, slot) in at_l.iter_mut().zip([ROW, COL, READ_TS_ROW, READ_TS_COL]) {
        *value = pre_claims.receive(transcript, slot, z_l)?;
    }
    let [row, col, read_ts_row, read_ts_col] = at_l;
    for (slot, limb) in limbs.iter_mut().enumerate() {
        *limb = online_claims.receive(transcript, slot, z_l)?;
    }
    let final_ts_row = pre_claims.receive(transcript, FINAL_TS_ROW, z_k)?;
    let final_ts_col = pre_claims.receive(transcript, FINAL_TS_COL, z_k)?;

    let col_bit = E::from(K(1 << k));
    let address = z_k.iter().enumerate().fold(ZERO, |acc, (j, &z)| acc + z * K(1 << j));
    let (e_u, e_w) = (from_limbs(&limbs[E_U..E_U + 3]), from_limbs(&limbs[E_W..E_W + 3]));
    let (u, w) = (row_weights_mle(claims, z_k), column_weights_mle(claims, z_k));
    let col = col + col_bit;
    let init_writes = [
        fingerprint.eval(row, e_u, read_ts_row * GEN),
        fingerprint.eval(col, e_w, read_ts_col * GEN),
        fingerprint.eval(address, u, ONE),
        fingerprint.eval(address + col_bit, w, ONE),
    ];
    let reads_final = [
        fingerprint.eval(row, e_u, read_ts_row),
        fingerprint.eval(col, e_w, read_ts_col),
        fingerprint.eval(address, u, final_ts_row),
        fingerprint.eval(address + col_bit, w, final_ts_col),
    ];
    require(
        products[0] == tree_mle(&point, l, k, init_writes)
            && products[1] == tree_mle(&point, l, k, reads_final)
            && products[2] == ONE,
        VerifierError::SparkMemoryCheck,
    )?;

    pre_claims.open(transcript, Digest(key.root), log_inv_rate)?;
    online_claims.open(transcript, online_root, log_inv_rate)
}
