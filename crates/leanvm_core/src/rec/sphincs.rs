//! leanSPHINCS signatures verified on the recursion machine: `n` signatures in one recursion proof.
//!
//! The circuit is `verification/circuits/LeanVMCircuits/Sphincs/Circuit.lean`'s, which its header describes: the
//! builder calls below are that program's, in its order, and `CheckXmss` checks that the circuit built here is the one
//! the Lean program builds. Like the Lean program it reuses the leanXMSS circuit's gadgets for statement words, the
//! digit product and digit indicators.
//!
//! Per signature the statement is four `E` words, in the order the guest commits them: the key's root `[r0, r1, 0]`,
//! its public parameter `[p0, p1, 0]`, and the message's words `[m0, m1, 0]` and `[m2, m3, 0]`. The signature is the
//! prover's, and the top layer's root it reaches is held to the statement's.

use super::circuit::{Builder, Circuit, Dw, Ew, Finished, Kw, Limbs, PARAM_IV, Unsatisfied};
use super::fixed::FixedColumns;
use super::tree::{CircuitStats, Leaf, LeafCircuit, LeafStatement, Leaves};
use super::xmss::{STEPS, V, digit_product, indicators, statement_words};
use crate::cpu::{DecodeError, VerifyError};
use crate::envelope::Envelope;
use crate::pcs::Rate;
use fiat_shamir::transcript::ProofTranscript;
use primitives::field::{F64, F192};
use primitives::hash::Hasher;
use thiserror::Error;
use tracing::info_span;

/// The domain of every proof's transcript.
const DOMAIN: &[u8] = b"leanvm-sphincs-rec-1";

/// Hypertree layers, numbered from the top.
const D: usize = 3;
/// Each layer's tree height.
const HEIGHTS: [usize; D] = [12, 7, 7];
/// The height of everything below each layer's top.
const SUFFIX: [usize; D + 1] = [26, 14, 7, 0];
/// The index's bits: the total height.
const H: usize = 26;
/// Log2 of the leaves of one few-time tree.
const A: usize = 10;
/// Indices the message digest picks, one per few-time tree.
const K: usize = 15;
/// Few-time trees in a signature: the last index is held to zero, so its tree is dropped.
const FTS_TREES: usize = K - 1;
/// The encoding's bytes: tweak, parameter, message and the counter's low half.
const ENCODING_BYTES: u64 = 52;

/// `X^191` in `K` as a word: the product the encoding's digit bits must reach, the digits summing to 191.
const TARGET: u64 = 0x8000_0000_0000_0ed6;

/// What one signature is checked against: the signer's public key and the message.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SphincsClaim {
    /// The public key's root: the root of the top layer's tree.
    pub root: [u64; 2],
    /// The public key's parameter, under which every hash of the key is taken.
    pub public_param: [u64; 2],
    /// The message.
    pub message: [u64; 4],
}

/// One few-time tree's part of a leanSPHINCS signature: the opened secret and its path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SphincsFtsOpening {
    /// The secret of the leaf the message digest picks.
    pub secret: [u64; 2],
    /// The sibling at each level, leaf first.
    pub path: [[u64; 2]; A],
}

/// One hypertree layer's part of a leanSPHINCS signature, for a tree of height `HEIGHT`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SphincsLayer<const HEIGHT: usize> {
    /// The encoding counter, a 32-bit value in a word of its own.
    pub counter: u64,
    /// The one-time signature: chain `i` opened at the encoding's digit `i`.
    pub ots: [[u64; 2]; V],
    /// The sibling at each level of the layer's tree, leaf first.
    pub path: [[u64; 2]; HEIGHT],
}

/// A leanSPHINCS signature, as words, in the specification's order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SphincsSignature {
    /// What the message digest is taken under.
    pub randomizer: [u64; 2],
    /// The few-time signature, one opening per tree.
    pub fts: [SphincsFtsOpening; FTS_TREES],
    /// The top layer, of height 12.
    pub layer0: SphincsLayer<{ HEIGHTS[0] }>,
    /// The middle layer, of height 7.
    pub layer1: SphincsLayer<{ HEIGHTS[1] }>,
    /// The bottom layer, of height 7, which signs the few-time key.
    pub layer2: SphincsLayer<{ HEIGHTS[2] }>,
}

impl<const HEIGHT: usize> SphincsLayer<HEIGHT> {
    /// The layer of zeros.
    const ZERO: Self = Self {
        counter: 0,
        ots: [[0; 2]; V],
        path: [[0; 2]; HEIGHT],
    };

    /// Its counter, one-time signature and path.
    const fn parts(&self) -> (u64, &[[u64; 2]; V], &[[u64; 2]]) {
        (self.counter, &self.ots, &self.path)
    }
}

impl SphincsSignature {
    /// The opening of zeros.
    const ZERO_OPENING: SphincsFtsOpening = SphincsFtsOpening {
        secret: [0; 2],
        path: [[0; 2]; A],
    };

    /// The signature of zeros, which a circuit built from its size alone reads.
    const ZERO: Self = Self {
        randomizer: [0; 2],
        fts: [Self::ZERO_OPENING; FTS_TREES],
        layer0: SphincsLayer::ZERO,
        layer1: SphincsLayer::ZERO,
        layer2: SphincsLayer::ZERO,
    };

    /// Layer `lay`'s counter, one-time signature and path.
    const fn layer(&self, lay: usize) -> (u64, &[[u64; 2]; V], &[[u64; 2]]) {
        // The layers have different heights, hence different types.
        match lay {
            0 => self.layer0.parts(),
            1 => self.layer1.parts(),
            _ => self.layer2.parts(),
        }
    }
}

/// The circuit verifying `n` leanSPHINCS signatures at one rate: the key of both its prover and its verifier.
///
/// It is built from `n` and the rate alone.
pub struct SphincsBatch {
    /// The signatures a proof verifies.
    n: usize,
    /// Every proof's rate.
    rate: Rate,
    /// The circuit.
    circuit: Circuit,
    /// Its fixed columns.
    columns: FixedColumns,
    /// The transcript's seed.
    iv: [F64; 4],
}

/// A proof that a batch of leanSPHINCS signatures verifies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SphincsProof {
    /// The recursion proof.
    proof: ProofTranscript,
    /// The rate it is proven at.
    rate: Rate,
}

/// Why a batch cannot be built or proven, or a proof is refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum SphincsError {
    /// The circuit fits no commitment.
    #[error("the circuit verifying {n} signatures fits no commitment")]
    TooLarge {
        /// The signatures it verifies.
        n: usize,
    },
    /// Claims or signatures of another number than the batch's.
    #[error("a batch of {expected} signatures is given {got} {what}")]
    Count {
        /// The batch's size.
        expected: usize,
        /// How many are given.
        got: usize,
        /// What is given.
        what: &'static str,
    },
    /// A signature fails a check of the circuit, its root among them.
    #[error("the signature does not verify: {0}")]
    Unsatisfied(Unsatisfied),
    /// A proof at another rate than the batch's.
    #[error(
        "a proof at log-inv-rate {}, and the batch's is {}",
        .got.log_inv_rate(),
        .expected.log_inv_rate()
    )]
    Rate {
        /// The batch's.
        expected: Rate,
        /// The proof's.
        got: Rate,
    },
    /// The recursion proof does not verify.
    #[error(transparent)]
    Proof(#[from] VerifyError),
}

impl SphincsProof {
    /// The header of a proof's bytes: the magic `LVMS`, then the protocol's version.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMS", 1);

    /// The proof's bytes.
    ///
    /// ```text
    /// | header | log_inv_rate: u8 | recursion proof |
    /// ```
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut body = vec![self.rate.log_inv_rate()];
        body.extend(self.proof.to_bytes());
        Self::ENVELOPE.seal(&body)
    }

    /// The proof these bytes encode.
    ///
    /// # Errors
    ///
    /// - Bytes that are no such proof.
    /// - A proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let body = Self::ENVELOPE.open(bytes)?;
        let (&rate, proof) = body.split_first().ok_or(DecodeError::Malformed)?;
        Ok(Self {
            proof: ProofTranscript::from_bytes(proof).ok_or(DecodeError::Malformed)?,
            rate: Rate::new(rate).map_err(|_| DecodeError::Malformed)?,
        })
    }
}

impl SphincsBatch {
    /// The circuit verifying `n` signatures, its proofs at `rate`.
    ///
    /// # Errors
    ///
    /// A circuit that fits no commitment.
    pub fn new(n: usize, rate: Rate) -> Result<Self, SphincsError> {
        let circuit = build(&vec![SphincsClaim::default(); n], &vec![SphincsSignature::ZERO; n]).circuit;
        circuit.committed_words().map_err(|_| SphincsError::TooLarge { n })?;
        let columns = FixedColumns::of(&circuit, &circuit.heights());
        let mut h = Hasher::new();
        h.update(DOMAIN);
        h.update(&(n as u64).to_le_bytes());
        h.update(&[rate.log_inv_rate()]);
        let iv = fiat_shamir::digest_words(&h.finalize());
        Ok(Self {
            n,
            rate,
            circuit,
            columns,
            iv,
        })
    }

    /// The signatures a proof verifies.
    #[must_use]
    pub const fn n(&self) -> usize {
        self.n
    }

    /// What the circuit costs: its rows and heights per table, and the words a proof commits.
    #[must_use]
    pub fn stats(&self) -> CircuitStats {
        CircuitStats::of(&self.circuit)
    }

    /// The leaves of an aggregation tree that are proofs of this batch.
    #[must_use]
    pub const fn leaves(&self) -> Leaves<'_> {
        Leaves::Circuit(self.leaf_circuit())
    }

    /// A leaf of an aggregation tree: a proof of this batch, and the claims it proves, in order.
    ///
    /// # Errors
    ///
    /// Claims of another number than the batch's.
    pub fn leaf<'a>(&self, claims: &[SphincsClaim], proof: &'a SphincsProof) -> Result<Leaf<'a>, SphincsError> {
        self.count(claims.len(), "claims")?;
        Ok(Leaf::circuit(
            &self.leaf_circuit(),
            statement(claims),
            &proof.proof,
            proof.rate,
        ))
    }

    /// What a leaf of these claims states, which an aggregation tree's verifier is given.
    ///
    /// # Errors
    ///
    /// Claims of another number than the batch's.
    pub fn statement(&self, claims: &[SphincsClaim]) -> Result<LeafStatement, SphincsError> {
        self.count(claims.len(), "claims")?;
        Ok(LeafStatement::circuit(&self.leaf_circuit(), statement(claims)))
    }

    const fn leaf_circuit(&self) -> LeafCircuit<'_> {
        LeafCircuit::new(&self.circuit, &self.columns, self.iv, self.rate)
    }

    /// Prove that each signature verifies under its claim, in order.
    ///
    /// # Errors
    ///
    /// - Claims or signatures of another number than the batch's.
    /// - A signature that does not verify.
    pub fn prove(
        &self,
        claims: &[SphincsClaim],
        signatures: &[SphincsSignature],
    ) -> Result<SphincsProof, SphincsError> {
        self.count(claims.len(), "claims")?;
        self.count(signatures.len(), "signatures")?;
        let Finished {
            circuit,
            assignment,
            failures,
        } = info_span!("Build circuit").in_scope(|| build(claims, signatures));
        if let Some(first) = failures.into_iter().next() {
            return Err(SphincsError::Unsatisfied(first));
        }
        debug_assert!(circuit == self.circuit, "the rows never depend on the values");
        debug_assert!(
            assignment.statement() == statement(claims),
            "the statement is the claims'"
        );
        let proof = (self.circuit)
            .prove_with(&assignment, self.iv, self.rate, Some(&self.columns))
            .map_err(|_| SphincsError::TooLarge { n: self.n })?;
        Ok(SphincsProof { proof, rate: self.rate })
    }

    /// Verify a proof that each signature verifies under its claim, in order.
    ///
    /// # Errors
    ///
    /// - Claims of another number than the batch's.
    /// - A proof at another rate, or one that does not verify.
    pub fn verify(&self, claims: &[SphincsClaim], proof: &SphincsProof) -> Result<(), SphincsError> {
        self.count(claims.len(), "claims")?;
        if proof.rate != self.rate {
            return Err(SphincsError::Rate {
                expected: self.rate,
                got: proof.rate,
            });
        }
        (self.circuit)
            .verify_to_raw_with(&statement(claims), self.iv, self.rate, &proof.proof, &self.columns)
            .map_err(VerifyError::from)?;
        Ok(())
    }

    /// The circuit as `CheckXmss` reads it: the builder calls that make it, one per line, then `circuit` and the
    /// circuit's dump, then `next` and the bus's `next` key of every slot of the circuit's rows, per table, row-major.
    ///
    /// # Panics
    ///
    /// Panics if building the circuit again gives another circuit.
    #[cfg(feature = "circuit-trace")]
    #[must_use]
    pub fn circuit_dump(&self) -> String {
        let n = self.n;
        let (finished, calls) =
            super::circuit::traced(|| build(&vec![SphincsClaim::default(); n], &vec![SphincsSignature::ZERO; n]));
        assert_eq!(finished.circuit, self.circuit, "a circuit is built the same every time");
        calls + "circuit\n" + &self.circuit.dump() + &self.columns.dump_next(&self.circuit)
    }

    const fn count(&self, got: usize, what: &'static str) -> Result<(), SphincsError> {
        if got == self.n {
            Ok(())
        } else {
            Err(SphincsError::Count {
                expected: self.n,
                got,
                what,
            })
        }
    }
}

/// The statement of a batch: each claim's four words.
fn statement(claims: &[SphincsClaim]) -> Vec<Limbs> {
    (claims.iter())
        .flat_map(|c| {
            let ([r0, r1], [p0, p1], [m0, m1, m2, m3]) = (c.root, c.public_param, c.message);
            [[r0, r1, 0, 0], [p0, p1, 0, 0], [m0, m1, 0, 0], [m2, m3, 0, 0]]
        })
        .collect()
}

/// The circuit verifying the signatures, with their values: `Circuit.circuit n`.
fn build(claims: &[SphincsClaim], signatures: &[SphincsSignature]) -> Finished {
    let mut b = Builder::new();
    for (i, (claim, sig)) in claims.iter().zip(signatures).enumerate() {
        b.scope(format!("signature {i}"), |b| signature(b, claim, sig));
    }
    b.finish()
}

/// A tweak's first word: the domain separator 1 in byte 0, the type in byte 1, the layer or tree in byte 2, the
/// position `p` in bytes 4 to 7.
const fn tweak0(ty: u64, lay: usize, p: usize) -> u64 {
    1 | ty << 8 | (lay as u64) << 16 | (p as u64) << 32
}

/// A statement word exposed, its two words.
fn statement_digest(b: &mut Builder, [w0, w1]: [u64; 2]) -> [Kw; 2] {
    let ks = statement_words(b, F192::new(w0, w1, 0), 1);
    [ks[0], ks[1]]
}

/// A tweak's second word `tau | j << 32` from the bits of `tau` and `j`, low first; the constant zero when both have
/// none.
fn index_word(b: &mut Builder, tau: &[Kw], j: &[Kw]) -> Kw {
    let z = b.k_const(0);
    if tau.is_empty() && j.is_empty() {
        return z;
    }
    let mut all = tau.to_vec();
    all.resize(32, z);
    all.extend(j);
    b.pack(&all)
}

/// The digest wire of the hash of `tw0 || tw1 || p || payload`, `tw0` a constant.
fn th(b: &mut Builder, tw0: u64, tw1: Kw, pp: &[Kw; 2], payload: &[Kw]) -> Dw {
    let t = b.k_const(tw0);
    let words: Vec<Kw> = [t, tw1].iter().chain(pp).chain(payload).copied().collect();
    b.chain(&words)
}

/// One tree level: the parent of `node` and the sibling, `bit` naming the side of `node`.
fn level(b: &mut Builder, tw0: u64, tw1: Kw, bit: Kw, node: Dw, pp: &[Kw; 2], [s0, s1]: [u64; 2]) -> Dw {
    let (cur, _) = b.d_to_e_and_k(node);
    let sib = b.free_e(F192::new(s0, s1, 0));
    let diff = b.add(cur, sib);
    let left = b.mul_k_add(diff, bit, cur);
    let right = b.add(left, diff);
    let [l0, l1, _] = b.e_to_k(left);
    let [r0, r1, _] = b.e_to_k(right);
    th(b, tw0, tw1, pp, &[l0, l1, r0, r1])
}

/// A tree of type `ty` and layer or tree `lay`, `tau` its tree's bits: the root `leaf` climbs to by `path`, the leaf
/// index's bits `j` low first; `top` is the tweak's second word at the top, `tau` alone.
fn fold(
    b: &mut Builder,
    (ty, lay): (u64, usize),
    (tau, top): (&[Kw], Kw),
    j: &[Kw],
    pp: &[Kw; 2],
    leaf: Dw,
    path: &[[u64; 2]],
) -> Dw {
    let mut node = leaf;
    for (l, (&bit, &sibling)) in j.iter().zip(path).enumerate() {
        let tw1 = if l + 1 < j.len() {
            index_word(b, tau, &j[l + 1..])
        } else {
            top
        };
        node = level(b, tweak0(ty, lay, l + 1), tw1, bit, node, pp, sibling);
    }
    node
}

/// Chain `i` of layer `lay` from its element `tip` under the digit's indicators `ind`, the key's tweak word `tw1`:
/// its end's two words.
fn chain_end(b: &mut Builder, (lay, i): (usize, usize), tw1: Kw, tip: Ew, pp: &[Kw; 2], ind: &[Ew]) -> [Kw; 2] {
    let [t0, t1, _] = b.e_to_k(tip);
    let d = th(b, tweak0(1, lay, 8 * i), tw1, pp, &[t0, t1]);
    let (mut cur, _) = b.d_to_e_and_k(d);
    for (s, &selected) in ind[..STEPS].iter().enumerate().skip(1) {
        let diff = b.add(tip, cur);
        let m = b.mul_add(selected, diff, cur);
        let [v0, v1, _] = b.e_to_k(m);
        let d = th(b, tweak0(1, lay, 8 * i + s), tw1, pp, &[v0, v1]);
        cur = b.d_to_e_and_k(d).0;
    }
    let diff = b.add(tip, cur);
    let end = b.mul_add(ind[STEPS], diff, cur);
    let [n0, n1, _] = b.e_to_k(end);
    [n0, n1]
}

/// The few-time key the openings reach, the index's bits `idx`, the leaf indices' bits `us`, and `top` the tweak word
/// of the index alone.
fn fts(b: &mut Builder, idx: &[Kw], us: &[&[Kw]], top: Kw, pp: &[Kw; 2], openings: &[SphincsFtsOpening]) -> Dw {
    let mut roots = Vec::with_capacity(2 * FTS_TREES);
    for (kappa, opening) in openings.iter().enumerate() {
        let u = us[kappa];
        let [s0, s1] = opening.secret;
        let secret = b.free_e(F192::new(s0, s1, 0));
        let [s0, s1, _] = b.e_to_k(secret);
        let tw1 = index_word(b, idx, u);
        let leaf = th(b, tweak0(9, kappa, 0), tw1, pp, &[s0, s1]);
        let root = fold(b, (10, kappa), (idx, top), u, pp, leaf, &opening.path);
        let rs = b.d_to_k(root);
        roots.extend([rs[0], rs[1]]);
    }
    th(b, tweak0(11, 0, 0), top, pp, &roots)
}

/// Layer `lay`'s root, from the message `msg` it signs and the index's bits `idx`.
fn layer(
    b: &mut Builder,
    lay: usize,
    idx: &[Kw],
    pp: &[Kw; 2],
    msg: Dw,
    (counter, ots, path): (u64, &[[u64; 2]; V], &[[u64; 2]]),
) -> Dw {
    let tau = &idx[SUFFIX[lay]..];
    let e = &idx[SUFFIX[lay + 1]..][..HEIGHTS[lay]];
    let z = b.k_const(0);
    let key = index_word(b, tau, e);
    let top = index_word(b, tau, &[]);

    // The encoding.
    let ms = b.d_to_k(msg);
    let ctr = b.free_k(counter);
    let cb = b.split(ctr);
    b.scope("counter", |b| {
        for &k in &cb[32..] {
            b.eq_k_const(k, 0);
        }
    });
    let tw0 = b.k_const(tweak0(4, lay, 0));
    let h = b.d_const(PARAM_IV);
    let d = b.leaf_block(h, [tw0, key, pp[0], pp[1], ms[0], ms[1], ctr, z], ENCODING_BYTES, true);
    let ks = b.d_to_k(d);
    let lo = b.split(ks[0]);
    let hi = b.split(ks[1]);
    let digit_bits: Vec<Kw> = lo[..63].iter().chain(&hi[..63]).copied().collect();
    b.scope("encoding", |b| {
        b.eq_k_const(lo[63], 0);
        b.eq_k_const(hi[63], 0);
        let prod = digit_product(b, &digit_bits);
        b.eq_e_const(prod, F192::new(TARGET, 0, 0));
    });

    // The chains.
    let mut ends = Vec::with_capacity(2 * V);
    for (i, &[t0, t1]) in ots.iter().enumerate() {
        let tip = b.free_e(F192::new(t0, t1, 0));
        let ind = indicators(b, [digit_bits[3 * i], digit_bits[3 * i + 1], digit_bits[3 * i + 2]]);
        ends.extend(chain_end(b, (lay, i), key, tip, pp, &ind));
    }

    // The leaf and the path.
    let leaf = th(b, tweak0(2, lay, 0), key, pp, &ends);
    fold(b, (3, lay), (tau, top), e, pp, leaf, path)
}

/// One signature's verification.
fn signature(b: &mut Builder, claim: &SphincsClaim, sig: &SphincsSignature) {
    let [m0, m1, m2, m3] = claim.message;
    let root = statement_digest(b, claim.root);
    let pp = statement_digest(b, claim.public_param);
    let mlo = statement_digest(b, [m0, m1]);
    let mhi = statement_digest(b, [m2, m3]);
    let z = b.k_const(0);

    // The message digest.
    let [r0, r1] = sig.randomizer;
    let rho = b.free_e(F192::new(r0, r1, 0));
    let [r0, r1, _] = b.e_to_k(rho);
    let payload: Vec<Kw> = [r0, r1].into_iter().chain(root).chain(mlo).chain(mhi).collect();
    let d = th(b, tweak0(12, 0, 0), z, &pp, &payload);
    let ks = b.d_to_k(d);
    let mut bits = Vec::with_capacity(3 * 64);
    for &k in &ks[..3] {
        bits.extend(b.split(k));
    }
    let idx = &bits[..H];
    let us: Vec<&[Kw]> = (0..K).map(|kappa| &bits[H + A * kappa..][..A]).collect();
    b.scope("message digest", |b| {
        for &k in us[K - 1] {
            b.eq_k_const(k, 0);
        }
    });

    // The few-time key, then the layers.
    let top = index_word(b, idx, &[]);
    let mut msg = b.scope("few-time key", |b| fts(b, idx, &us, top, &pp, &sig.fts));
    for lay in (0..D).rev() {
        msg = b.scope(format!("layer {lay}"), |b| layer(b, lay, idx, &pp, msg, sig.layer(lay)));
    }
    let rs = b.d_to_k(msg);
    b.scope("root", |b| {
        b.eq_k(rs[0], root[0]);
        b.eq_k(rs[1], root[1]);
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use leansphincs_host::{LayerSignature, MESSAGE};

    /// A change to a claim.
    type Change = fn(&mut SphincsClaim);
    /// A change to a claim and its signature.
    type Tamper = fn(&mut SphincsClaim, &mut SphincsSignature);

    /// A guest layer as the circuit's.
    fn layer<const HEIGHT: usize>(l: &LayerSignature<HEIGHT>) -> SphincsLayer<HEIGHT> {
        SphincsLayer {
            counter: l.counter,
            ots: l.ots,
            path: l.path,
        }
    }

    /// `n` honest signers' claims and signatures.
    fn signed(n: usize) -> (Vec<SphincsClaim>, Vec<SphincsSignature>) {
        (leansphincs_host::signers(n).into_iter())
            .map(|(pk, s)| {
                let claim = SphincsClaim {
                    root: pk.root,
                    public_param: pk.public_param,
                    message: MESSAGE,
                };
                let signature = SphincsSignature {
                    randomizer: s.randomizer,
                    fts: s.fts.map(|o| SphincsFtsOpening {
                        secret: o.secret,
                        path: o.path,
                    }),
                    layer0: layer(&s.layer0),
                    layer1: layer(&s.layer1),
                    layer2: layer(&s.layer2),
                };
                (claim, signature)
            })
            .unzip()
    }

    #[test]
    fn an_honest_batch_verifies_under_its_statement_only() {
        let (claims, signatures) = signed(2);
        let batch = SphincsBatch::new(2, Rate::MIN).expect("two signatures fit");
        let proof = batch.prove(&claims, &signatures).expect("honest signatures");
        let decoded = SphincsProof::from_bytes(&proof.to_bytes()).expect("its own bytes");
        assert_eq!(decoded, proof);
        // The verifier's key is built from the size and the rate alone.
        let key = SphincsBatch::new(2, Rate::MIN).expect("two signatures fit");
        assert_eq!(key.verify(&claims, &decoded), Ok(()));

        // Mutation: one word of each part of the second claim.
        //
        //     the statement seeds the transcript and the public rows read it
        //     → the proof of the honest claims is refused
        let changes: [(&str, Change); 4] = [
            ("the root", |c| c.root[0] ^= 1),
            ("the parameter", |c| c.public_param[1] ^= 1),
            ("the message's first half", |c| c.message[0] ^= 1),
            ("the message's second half", |c| c.message[3] ^= 1),
        ];
        for (what, change) in changes {
            let mut forged = claims.clone();
            change(&mut forged[1]);
            assert!(
                matches!(key.verify(&forged, &proof), Err(SphincsError::Proof(_))),
                "{what}"
            );
        }
    }

    #[test]
    fn a_tampered_signature_has_no_proof() {
        let (claims, signatures) = signed(2);
        let batch = SphincsBatch::new(2, Rate::MIN).expect("two signatures fit");

        // Mutation: any part of the signature, or the claim's root or message.
        //
        //     the randomizer or the message changes the message digest
        //     → a nonzero last index, or another few-time key
        //     a few-time secret or sibling changes the few-time key
        //     → an encoding the bottom layer's rows refuse
        //     a counter changes, or passes 32 bits
        //     → an encoding the rows refuse, or bits the rows hold zero
        //     a chain element or a layer's sibling changes the layer's root
        //     → an encoding the layer above refuses, or another root than the key's
        let tampered: [(&str, Tamper); 13] = [
            ("the randomizer", |_, s| s.randomizer[0] ^= 1),
            ("a few-time secret", |_, s| s.fts[0].secret[0] ^= 1),
            ("a few-time sibling", |_, s| s.fts[13].path[9][1] ^= 1 << 63),
            ("the top counter", |_, s| s.layer0.counter ^= 1),
            ("the bottom counter", |_, s| s.layer2.counter ^= 1),
            ("a counter past 32 bits", |_, s| s.layer1.counter |= 1 << 32),
            ("a top chain element", |_, s| s.layer0.ots[20][1] ^= 1),
            ("a bottom chain element", |_, s| s.layer2.ots[41][0] ^= 1),
            ("a top sibling", |_, s| s.layer0.path[11][0] ^= 1),
            ("a middle sibling", |_, s| s.layer1.path[0][1] ^= 1),
            ("the root", |c, _| c.root[1] ^= 1),
            ("the message's first half", |c, _| c.message[1] ^= 1),
            ("the message's second half", |c, _| c.message[2] ^= 1),
        ];
        for (what, tamper) in tampered {
            let (mut c, mut s) = (claims.clone(), signatures.clone());
            tamper(&mut c[1], &mut s[1]);
            let refused = batch.prove(&c, &s).err();
            assert!(
                matches!(refused, Some(SphincsError::Unsatisfied(_))),
                "{what}: {refused:?}"
            );
        }
    }
}
