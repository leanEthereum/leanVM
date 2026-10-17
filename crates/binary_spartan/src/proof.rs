//! Prove a batch of block instances: commit the packed witness, run flock's zerocheck and lincheck (with the block's
//! general `C_0`), then open the commitment in one stacked WHIR that discharges lincheck's ring-switched slice claim
//! and pins every instance's public words. The lincheck terminal's matrix evaluation is computed by the verifier from
//! the sparse block ([`Mode::Direct`]) or proven with [`crate::spark`] ([`Mode::Spark`]).
//!
//! Transcript order: commitment root, zerocheck, lincheck, the public-pin point, the stacked opening, then SPARK.
//! [`verify`] hands the proof to `verifier::binary_spartan`, which walks it in the same order.

use crate::block::{BlockR1cs, Csr};
use crate::format::WitnessFile;
use crate::spark::{self, SparkProverKey, SparkVerifierKey};
use fiat_shamir::transcript::ProverState;
use flock::lincheck::{QuirkyPoint, build_quirky_eq_table};
use flock::zerocheck::{K_SKIP, PaddingSpec, ZerocheckClaim};
use leanvm_core::pcs::{RingSwitchClaim, RingSwitchOpen, SlotClaim};
use leanvm_core::witness::StackShape;
use pcs::pack::LOG_PACKING;
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, mle_eval};
use verifier::VerifierError;

pub use fiat_shamir::transcript::Proof;
pub use verifier::binary_spartan::LABEL;

/// The witness commitment's (and SPARK's) inverse-rate logarithm.
pub const LOG_INV_RATE: usize = leanvm_core::pcs::TEST_LOG_INV_RATE;

/// The batch dimensions both sides derive from the block and the real instance count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    pub n_instances: usize,
    pub k_log: usize,
    pub n_log: usize,
}

impl Shape {
    pub fn new(block: &BlockR1cs, n_instances: usize) -> Result<Self, VerifierError> {
        let k_log = block.k_log();
        Ok(Self {
            n_instances,
            k_log,
            n_log: verifier::binary_spartan::batch_log(k_log, n_instances)?,
        })
    }

    pub fn m(&self) -> usize {
        self.k_log + self.n_log
    }

    /// log2 of the packed witness length in words.
    fn qflock_vars(&self) -> usize {
        self.m() - LOG_PACKING
    }

    /// The committed stack: the packed witness at offset 0, padded to WHIR's minimum size.
    fn stack(&self) -> StackShape {
        let mu = self.qflock_vars().max(leanvm_core::pcs::MIN_MU);
        let lane = 1usize << (mu - pcs::whir::INITIAL_FOLDING_FACTOR);
        StackShape {
            mu,
            n_lanes: (1usize << self.qflock_vars()).div_ceil(lane),
        }
    }
}

/// Every instance's public region, `public_words()` packed words per instance: bit `j` is signal `j` (the constant
/// one, the public bits, then zero padding).
pub fn publics(block: &BlockR1cs, batch: &WitnessFile) -> Vec<u64> {
    let mut words = vec![0u64; batch.n_instances * block.public_words()];
    parallel::chunks_mut(&mut words, block.public_words(), |i, out| {
        block.layout_public(batch.instance(i), out)
    });
    words
}

/// How the lincheck terminal's matrix evaluation is discharged.
pub enum Mode<'a, K> {
    /// The verifier evaluates `uᵀ(A_0 + αB_0 + α²C_0)w` from the sparse block.
    Direct,
    /// A SPARK proof of that evaluation rides the transcript.
    Spark(&'a K),
}

impl<K> Clone for Mode<'_, K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K> Copy for Mode<'_, K> {}

pub type ProveMode<'a> = Mode<'a, SparkProverKey>;
pub type VerifyMode<'a> = Mode<'a, SparkVerifierKey>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProveError {
    /// The witness's signal count differs from the block's, or the batch shape is unsupported.
    Shape,
    /// The first violated constraint of the first violating real instance.
    Unsatisfied { instance: usize, row: usize },
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl std::error::Error for ProveError {}

/// Seed the transcript with the statement, as `verifier::binary_spartan` does: the label, the block digest, the shape
/// and every real instance's public words, little-endian.
fn seed(block: &BlockR1cs, shape: &Shape, publics: &[u64]) -> ([F64; 4], [F64; 4]) {
    let mut h = primitives::hash::Hasher::new();
    h.update(LABEL).update(&block.digest);
    for x in [shape.n_instances, shape.k_log, shape.n_log] {
        h.update(&(x as u64).to_le_bytes());
    }
    h.update(bytes(publics));
    (
        fiat_shamir::digest_words(&primitives::hash::hash(LABEL)),
        fiat_shamir::digest_words(&h.finalize()),
    )
}

/// The packed tables the reduction consumes, all in flock's layouts.
struct Packed {
    /// `z`, `A·z`, `B·z`, `C·z`: instance-major, 64 bits per word, `2^k_log / 64` words per instance.
    z: Vec<u64>,
    a: Vec<u64>,
    b: Vec<u64>,
    c: Vec<u64>,
    /// lincheck's byte stripes: byte `(i / 8)·2^k_log + col` holds column `col` of instances `8(i / 8)..+8`.
    z_lincheck: Vec<u8>,
}

/// Lay the batch out (extra instances repeat the last real one) and compute `A·z`, `B·z`, `C·z` up to 64 instances
/// at a time on column words, checking `a·b = c` on the way.
fn pack(block: &BlockR1cs, batch: &WitnessFile, shape: &Shape) -> Result<Packed, ProveError> {
    let k = 1usize << shape.k_log;
    let wpb = k / 64;
    let n_total = 1usize << shape.n_log;
    let last = batch.n_instances - 1;

    // Sized to the committed stack, so the commitment reads `z` in place.
    // SAFETY: the padding past the instances is zeroed here and every instance block in the pass below.
    let mut z: Vec<u64> = unsafe { primitives::uninit_vec((n_total * wpb).max(shape.stack().committed_len())) };
    let (instances, padding) = z.split_at_mut(n_total * wpb);
    padding.fill(0);
    parallel::chunks_mut(instances, wpb, |i, out| {
        out.fill(0);
        block.layout_instance(batch.instance(i.min(last)), out)
    });

    // A group is `lanes` instances; column word `col` holds column `col` of the group's instance `l` at bit `l`.
    let lanes = n_total.min(64);
    // SAFETY: group `g` below writes every word of chunk `g` of `a`, `b`, `c` and every byte of its stripes.
    let (mut a, mut b, mut c, mut z_lincheck): (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u8>) = unsafe {
        (
            primitives::uninit_vec(n_total * wpb),
            primitives::uninit_vec(n_total * wpb),
            primitives::uninit_vec(n_total * wpb),
            primitives::uninit_vec(n_total / 8 * k),
        )
    };
    let (a_out, b_out, c_out) = (
        parallel::Chunks::new(&mut a, lanes * wpb),
        parallel::Chunks::new(&mut b, lanes * wpb),
        parallel::Chunks::new(&mut c, lanes * wpb),
    );
    let stripes = parallel::Chunks::new(&mut z_lincheck, lanes / 8 * k);
    let m = &block.matrices;
    let violations = parallel::map_collect(n_total / lanes, |g| {
        // SAFETY: group `g` takes chunk `g` of each output exactly once.
        let (stripes_g, a_g, b_g, c_g) = unsafe { (stripes.get(g), a_out.get(g), b_out.get(g), c_out.get(g)) };
        let z_g = &z[g * lanes * wpb..(g + 1) * lanes * wpb];
        let mut cols = vec![0u64; k];
        for (w, out) in cols.as_chunks_mut::<64>().0.iter_mut().enumerate() {
            *out = std::array::from_fn(|l| if l < lanes { z_g[l * wpb + w] } else { 0 });
            transpose_64x64(out);
        }
        // Stripe `s` of the group holds byte `s` of every column word: bit `r` is instance `8s + r`.
        for (s, stripe) in stripes_g.chunks_exact_mut(k).enumerate() {
            for (byte, col) in stripe.iter_mut().zip(&cols) {
                *byte = (col >> (8 * s)) as u8;
            }
        }
        let mut sides = vec![0u64; 3 * k];
        let (sa, rest) = sides.split_at_mut(k);
        let (sb, sc) = rest.split_at_mut(k);
        let mut violation = None;
        for r in 0..block.n_constraints {
            let sum = |row: &[u32]| row.iter().fold(0u64, |acc, &col| acc ^ cols[col as usize]);
            (sa[r], sb[r], sc[r]) = (sum(m.a.row(r)), sum(m.b.row(r)), sum(m.c.row(r)));
            let bad = (sa[r] & sb[r]) ^ sc[r];
            if bad != 0 && violation.is_none() {
                violation = Some(((lanes * g + bad.trailing_zeros() as usize).min(last), r));
            }
        }
        for (side, out) in [(&mut *sa, a_g), (&mut *sb, b_g), (&mut *sc, c_g)] {
            for (w, rows) in side.as_chunks_mut::<64>().0.iter_mut().enumerate() {
                transpose_64x64(rows);
                for (l, &word) in rows[..lanes].iter().enumerate() {
                    out[l * wpb + w] = word;
                }
            }
        }
        violation
    });
    if let Some(&(instance, row)) = violations.iter().flatten().min() {
        return Err(ProveError::Unsatisfied { instance, row });
    }
    Ok(Packed { z, a, b, c, z_lincheck })
}

/// Transpose a 64x64 bit matrix in place: bit `c` of word `r` trades places with bit `r` of word `c`.
fn transpose_64x64(m: &mut [u64; 64]) {
    let mut j = 32;
    let mut mask = 0x0000_0000_FFFF_FFFFu64;
    while j != 0 {
        let mut r = 0;
        while r < 64 {
            let t = ((m[r] >> j) ^ m[r + j]) & mask;
            m[r] ^= t << j;
            m[r + j] ^= t;
            r = (r + j + 1) & !j;
        }
        j >>= 1;
        mask ^= mask << j;
    }
}

fn bytes(words: &[u64]) -> &[u8] {
    // SAFETY: u64 has no padding and any bit pattern is a valid u8 sequence; the target is little-endian, which is
    // the bit order the packed tables are defined in.
    const _: () = assert!(cfg!(target_endian = "little"));
    unsafe { std::slice::from_raw_parts(words.as_ptr().cast::<u8>(), std::mem::size_of_val(words)) }
}

fn field_words(words: &[u64]) -> &[F64] {
    const _: () = assert!(size_of::<F64>() == size_of::<u64>() && align_of::<F64>() == align_of::<u64>());
    // SAFETY: `F64` is `repr(transparent)` over `u64`, and every `u64` is a valid `F64`.
    unsafe { std::slice::from_raw_parts(words.as_ptr().cast::<F64>(), words.len()) }
}

/// The lincheck input point carried over from the zerocheck claim.
fn x_ab_of(zc: &ZerocheckClaim, k_log: usize) -> QuirkyPoint {
    let inner_rest_len = k_log - K_SKIP;
    QuirkyPoint {
        z_skip: zc.z,
        x_inner_rest: zc.mlv_challenges[..inner_rest_len].to_vec(),
        x_outer: zc.mlv_challenges[inner_rest_len..].to_vec(),
    }
}

/// The public pins: for each public word slot `s`, the MLE over the instance index of word `s` at `point` (one
/// strided claim on the packed witness, stride one instance).
fn public_pins(shape: &Shape, slots: usize, z: &[u64], point: &[F192]) -> Vec<SlotClaim> {
    let wpb = (1usize << shape.k_log) / 64;
    (0..slots)
        .map(|s| {
            let column: Vec<F64> = (0..1usize << shape.n_log).map(|i| F64(z[i * wpb + s])).collect();
            SlotClaim::Strided {
                offset: 0,
                slot: s,
                stride_log: shape.k_log - LOG_PACKING,
                point: point.to_vec(),
                value: mle_eval(&column, point),
            }
        })
        .collect()
}

/// Prove that every instance of `batch` satisfies `block`. Refuses an unsatisfied witness.
pub fn prove(block: &BlockR1cs, batch: &WitnessFile, mode: ProveMode<'_>) -> Result<Proof, ProveError> {
    prove_statement(block, batch, &publics(block, batch), mode)
}

/// [`prove`] with the transcript seeded by `publics` rather than by the batch's own public region.
fn prove_statement(
    block: &BlockR1cs,
    batch: &WitnessFile,
    publics: &[u64],
    mode: ProveMode<'_>,
) -> Result<Proof, ProveError> {
    if batch.n_signals != block.n_signals {
        return Err(ProveError::Shape);
    }
    let shape = Shape::new(block, batch.n_instances).map_err(|_| ProveError::Shape)?;
    let _span = tracing::info_span!("Binary Spartan prove", n_log = shape.n_log).entered();
    let packed = tracing::info_span!("Pack").in_scope(|| pack(block, batch, &shape))?;
    let (iv, statement) = tracing::info_span!("Seed").in_scope(|| seed(block, &shape, publics));
    let mut ps = ProverState::new(iv, statement);

    let stack_shape = shape.stack();
    let stack = field_words(&packed.z);
    let committed =
        tracing::info_span!("Commit").in_scope(|| leanvm_core::pcs::commit(&mut ps, stack, stack_shape, LOG_INV_RATE));

    let m = shape.m();
    let zerocheck = tracing::info_span!("Zerocheck").entered();
    let zc = flock::zerocheck::prove_packed_padded(
        bytes(&packed.a),
        bytes(&packed.b),
        bytes(&packed.c),
        m,
        &PaddingSpec {
            k_log: shape.k_log,
            useful_bits_per_block: block.used_rows(),
        },
        &mut ps,
    );
    drop(zerocheck);
    let x_ab = x_ab_of(&zc, shape.k_log);
    let lincheck = tracing::info_span!("Lincheck").entered();
    let lc = flock::lincheck::prove_padded_capture_s_hat_v(
        &packed.z_lincheck,
        m,
        shape.k_log,
        K_SKIP,
        block.used_columns(),
        &block.matrices,
        &x_ab,
        &mut ps,
    );
    drop(lincheck);

    let opening = tracing::info_span!("Opening").entered();
    let point = ps.sample_vec(shape.n_log);
    let pins = public_pins(&shape, block.public_words(), &packed.z, &point);
    let mut suffix_point = lc.r_inner_rest.clone();
    suffix_point.extend_from_slice(&x_ab.x_outer);
    let ring = RingSwitchOpen {
        offset: 0,
        qflock_vars: shape.qflock_vars(),
        claims: vec![RingSwitchClaim {
            suffix_point,
            s_hat_v: Some(lc.s_hat_v.clone()),
        }],
    };
    leanvm_core::pcs::open(&mut ps, &committed, stack, &pins, &ring);
    drop(opening);

    if let Mode::Spark(pk) = mode {
        let _span = tracing::info_span!("SPARK").entered();
        // Lincheck's terminal weights: rows `λ(z_skip) ⊗ eq(x_inner_rest)`, columns `z_partial ⊗ eq(r_inner_rest)`.
        let rows = build_quirky_eq_table(x_ab.z_skip, &x_ab.x_inner_rest, K_SKIP);
        let cols: Vec<F192> = eq_table(&lc.r_inner_rest)
            .iter()
            .flat_map(|&e| lc.s_hat_v.iter().map(move |&s| e * s))
            .collect();
        spark::prove(pk, lc.alpha, &rows, &cols, &mut ps);
    }
    Ok(ps.into_proof())
}

/// Verify `proof` for `block` and the real instances' `publics` with `verifier::binary_spartan`.
pub fn verify(block: &BlockR1cs, publics: &[u64], proof: &Proof, mode: VerifyMode<'_>) -> Result<(), VerifierError> {
    fn csr(m: &Csr) -> verifier::binary_spartan::Csr<'_> {
        verifier::binary_spartan::Csr {
            row_ptr: &m.row_ptr,
            cols: &m.cols,
        }
    }
    let m = &block.matrices;
    let statement = verifier::binary_spartan::Block {
        k_log: m.k_log,
        n_public: block.n_public,
        a: csr(&m.a),
        b: csr(&m.b),
        c: csr(&m.c),
        digest: block.digest,
    };
    let spark = match mode {
        Mode::Direct => None,
        Mode::Spark(key) => Some(key),
    };
    let proof = leanvm_core::cpu::scalar_proof(proof);
    verifier::binary_spartan::verify(&statement, publics, LOG_INV_RATE, spark, &proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::format::{Constraint, R1csFile};

    #[test]
    fn transpose_64x64_matches_naive() {
        let mut rng = primitives::test_rng::Rng::new(7);
        let m: [u64; 64] = std::array::from_fn(|_| rng.next_u64());
        let mut t = m;
        transpose_64x64(&mut t);
        for (r, &row) in m.iter().enumerate() {
            for (c, &col) in t.iter().enumerate() {
                assert_eq!((row >> c) & 1, (col >> r) & 1, "bit ({r}, {c})");
            }
        }
    }

    /// A prover that seeds the transcript with the honest public bits but commits a witness whose public region
    /// differs is caught by the public pins alone. The public bits are unconstrained here, so the tampered batch
    /// still satisfies the block.
    #[test]
    fn public_pins_bind_the_committed_witness() {
        let n_public = 70;
        let (p, q, r) = (n_public as u32 + 1, n_public as u32 + 2, n_public as u32 + 3);
        let file = R1csFile {
            n_signals: n_public + 4,
            n_public,
            constraints: vec![
                Constraint {
                    a: vec![p],
                    b: vec![q],
                    c: vec![r],
                },
                Constraint {
                    a: vec![0],
                    b: vec![p],
                    c: vec![p],
                },
            ],
        };
        let block = BlockR1cs::new(&file).expect("valid block");
        let width = file.n_signals.div_ceil(8);
        let mut data = vec![0u8; 3 * width];
        for (i, row) in data.chunks_exact_mut(width).enumerate() {
            row[0] = 1 | (i as u8) << 3;
            for s in [p, q, r] {
                row[s as usize / 8] |= 1 << (s % 8);
            }
        }
        let honest = WitnessFile {
            n_signals: file.n_signals,
            n_instances: 3,
            data,
        };
        let publics = publics(&block, &honest);
        let proof = prove(&block, &honest, Mode::Direct).expect("satisfied");
        assert_eq!(verify(&block, &publics, &proof, Mode::Direct), Ok(()));

        // Public bit 5 of the first instance, then public bit 70 (second word) of the last.
        for (instance, signal) in [(0, 5), (2, 70)] {
            let mut tampered = honest.clone();
            tampered.data[instance * width + signal / 8] ^= 1 << (signal % 8);
            let forged = prove_statement(&block, &tampered, &publics, Mode::Direct).expect("still satisfied");
            assert_eq!(
                verify(&block, &publics, &forged, Mode::Direct),
                Err(VerifierError::WhirTerminal)
            );
        }
    }
}
