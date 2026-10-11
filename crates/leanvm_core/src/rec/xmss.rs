//! leanXMSS signatures verified on the recursion machine: `n` signatures in one recursion proof.
//!
//! The circuit is `verification/circuits/LeanVMCircuits/Xmss/Circuit.lean`'s, which its header describes: the builder
//! calls below are that program's, in its order, and `CheckXmss` checks that the circuit built here is the one the Lean
//! program builds.
//!
//! Per signature the statement is five `E` words, in this order: the public parameter `[p0, p1, 0]`, the message's
//! words `[m0, m1, 0]` and `[m2, m3, 0]`, the epoch `[e, 0, 0]`, then the Merkle root `[r0, r1, 0]` the signature
//! reaches. The signature is the prover's.

use super::circuit::{Builder, Circuit, Dw, Ew, Finished, Kw, Limbs, Unsatisfied};
use super::fixed::FixedColumns;
use super::tree::CircuitStats;
use crate::cpu::{DecodeError, VerifyError};
use crate::envelope::Envelope;
use crate::pcs::Rate;
use fiat_shamir::transcript::ProofTranscript;
use primitives::field::{F64, F192};
use primitives::hash::Hasher;
use thiserror::Error;
use tracing::info_span;

/// The domain of every proof's transcript.
const DOMAIN: &[u8] = b"leanvm-xmss-rec-1";

/// Hash chains, one per encoding digit.
const V: usize = 42;
/// Steps of a chain: its values are `0..=7`.
const STEPS: usize = 7;
/// The Merkle tree's height.
const LOG_LIFETIME: usize = 32;
/// Statement words per signature.
const WORDS: usize = 5;

/// `X^195` in `K` as a word: the product the encoding's digit bits must reach, the digits summing to 195.
const TARGET: u64 = 0xedb8;

/// What one signature is checked against: the signer's public key, the epoch and the message.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct XmssClaim {
    /// The public key's parameter, under which every hash of the key is taken.
    pub public_param: [u64; 2],
    /// The public key's Merkle root.
    pub merkle_root: [u64; 2],
    /// The epoch: the leaf of the tree the signature uses.
    pub epoch: u32,
    /// The message.
    pub message: [u64; 4],
}

/// A leanXMSS signature, as words.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XmssSignature {
    /// Chain `i` opened at the message's digit `i`.
    pub chain_tips: [[u64; 2]; V],
    /// What the message is encoded under.
    pub randomness: [u64; 3],
    /// The sibling at each level, leaf first.
    pub merkle_proof: [[u64; 2]; LOG_LIFETIME],
}

impl XmssSignature {
    /// The signature of zeros, which a circuit built from its size alone reads.
    const ZERO: Self = Self {
        chain_tips: [[0; 2]; V],
        randomness: [0; 3],
        merkle_proof: [[0; 2]; LOG_LIFETIME],
    };
}

/// The circuit verifying `n` leanXMSS signatures at one rate: the key of both its prover and its verifier.
///
/// It is built from `n` and the rate alone.
pub struct XmssBatch {
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

/// A proof that a batch of signatures verifies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XmssProof {
    /// The recursion proof.
    proof: ProofTranscript,
    /// The rate it is proven at.
    rate: Rate,
}

/// Why a batch cannot be built or proven, or a proof is refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum XmssError {
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
    /// A signature fails a check of the circuit.
    #[error("the signature does not verify: {0}")]
    Unsatisfied(Unsatisfied),
    /// A signature reaches another root than its key's.
    #[error("signature {index} reaches another root than its key's")]
    Root {
        /// The signature's index in the batch.
        index: usize,
    },
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

impl XmssProof {
    /// The header of a proof's bytes: the magic `LVMX`, then the protocol's version.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMX", 1);

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

impl XmssBatch {
    /// The circuit verifying `n` signatures, its proofs at `rate`.
    ///
    /// # Errors
    ///
    /// A circuit that fits no commitment.
    pub fn new(n: usize, rate: Rate) -> Result<Self, XmssError> {
        let circuit = build(&vec![XmssClaim::default(); n], &vec![XmssSignature::ZERO; n]).circuit;
        circuit.committed_words().map_err(|_| XmssError::TooLarge { n })?;
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

    /// Prove that each signature verifies under its claim, in order.
    ///
    /// # Errors
    ///
    /// - Claims or signatures of another number than the batch's.
    /// - A signature that does not verify.
    pub fn prove(&self, claims: &[XmssClaim], signatures: &[XmssSignature]) -> Result<XmssProof, XmssError> {
        self.count(claims.len(), "claims")?;
        self.count(signatures.len(), "signatures")?;
        let Finished {
            circuit,
            assignment,
            failures,
        } = info_span!("Build circuit").in_scope(|| build(claims, signatures));
        if let Some(first) = failures.into_iter().next() {
            return Err(XmssError::Unsatisfied(first));
        }
        let statement = statement(claims);
        if let Some(i) = (0..self.n).find(|&i| assignment.statement()[WORDS * i + 4] != statement[WORDS * i + 4]) {
            return Err(XmssError::Root { index: i });
        }
        debug_assert!(circuit == self.circuit, "the rows never depend on the values");
        let proof = (self.circuit)
            .prove_with(&assignment, self.iv, self.rate, Some(&self.columns))
            .map_err(|_| XmssError::TooLarge { n: self.n })?;
        Ok(XmssProof { proof, rate: self.rate })
    }

    /// Verify a proof that each signature verifies under its claim, in order.
    ///
    /// # Errors
    ///
    /// - Claims of another number than the batch's.
    /// - A proof at another rate, or one that does not verify.
    pub fn verify(&self, claims: &[XmssClaim], proof: &XmssProof) -> Result<(), XmssError> {
        self.count(claims.len(), "claims")?;
        if proof.rate != self.rate {
            return Err(XmssError::Rate {
                expected: self.rate,
                got: proof.rate,
            });
        }
        (self.circuit)
            .verify_to_raw_with(&statement(claims), self.iv, self.rate, &proof.proof, &self.columns)
            .map_err(VerifyError::from)?;
        Ok(())
    }

    /// The circuit as `CheckXmss` reads it: the builder calls that make it, one per line, then `circuit` and the circuit's
    /// dump, then `next` and the bus's `next` key of every slot of the circuit's rows, per table, row-major.
    ///
    /// # Panics
    ///
    /// Panics if building the circuit again gives another circuit.
    #[cfg(feature = "circuit-trace")]
    #[must_use]
    pub fn circuit_dump(&self) -> String {
        let n = self.n;
        let (finished, calls) =
            super::circuit::traced(|| build(&vec![XmssClaim::default(); n], &vec![XmssSignature::ZERO; n]));
        assert_eq!(finished.circuit, self.circuit, "a circuit is built the same every time");
        calls + "circuit\n" + &self.circuit.dump() + &self.columns.dump_next(&self.circuit)
    }

    const fn count(&self, got: usize, what: &'static str) -> Result<(), XmssError> {
        if got == self.n {
            Ok(())
        } else {
            Err(XmssError::Count {
                expected: self.n,
                got,
                what,
            })
        }
    }
}

/// The statement of a batch: each claim's five words.
fn statement(claims: &[XmssClaim]) -> Vec<Limbs> {
    (claims.iter())
        .flat_map(|c| {
            let ([p0, p1], [m0, m1, m2, m3], [r0, r1]) = (c.public_param, c.message, c.merkle_root);
            [
                [p0, p1, 0, 0],
                [m0, m1, 0, 0],
                [m2, m3, 0, 0],
                [u64::from(c.epoch), 0, 0, 0],
                [r0, r1, 0, 0],
            ]
        })
        .collect()
}

/// The circuit verifying the signatures, with their values: `Circuit.circuit n`.
fn build(claims: &[XmssClaim], signatures: &[XmssSignature]) -> Finished {
    let mut b = Builder::new();
    for (i, (claim, sig)) in claims.iter().zip(signatures).enumerate() {
        b.scope(format!("signature {i}"), |b| signature(b, claim, sig));
    }
    b.finish()
}

/// A tweak's first word: the domain separator zero, the tweak's type in byte 1, its position in bytes 4 to 7.
const fn tweak0(ty: u64, pos: usize) -> u64 {
    ty << 8 | (pos as u64) << 32
}

/// A statement word exposed, its words; `zeros` of its words past the first `3 - zeros` are held to zero.
fn statement_words(b: &mut Builder, value: F192, zeros: usize) -> Vec<Kw> {
    let w = b.free_e(value);
    b.expose_e(w);
    let ks = b.e_to_k(w);
    for &k in &ks[3 - zeros..] {
        b.eq_k_const(k, 0);
    }
    ks[..3 - zeros].to_vec()
}

/// The index word `e >> shift` in bytes 12 to 15 of a tweak, from the epoch's bits.
fn index_word(b: &mut Builder, bits: &[Kw; 64], shift: usize) -> Kw {
    let z = b.k_const(0);
    let mut all = vec![z; 32];
    all.extend(&bits[shift..32]);
    b.pack(&all)
}

/// The digest wire of the hash of `tweak0 || index || p || payload`.
fn tweak_hash(b: &mut Builder, ty: u64, pos: usize, idx: Kw, pp: &[Kw], payload: &[Kw]) -> Dw {
    let tw = b.k_const(tweak0(ty, pos));
    let words: Vec<Kw> = [tw, idx].iter().chain(pp).chain(payload).copied().collect();
    b.chain(&words)
}

/// The digit bits' product: for each bit `b` of weight `2^k`, times `X^(2^k)` when `b` is one.
fn digit_product(b: &mut Builder, bits: &[Kw]) -> Ew {
    let mut acc = b.one();
    let z = b.zero();
    for i in 0..V {
        for k in 0..3 {
            // `X^(2^k) + 1` as a word, `X` being the word 2.
            let t = b.mul_const_add(acc, F192::new((1 << (1 << k)) + 1, 0, 0), z);
            acc = b.mul_k_add(t, bits[3 * i + k], acc);
        }
    }
    acc
}

/// The indicators of the eight values of a digit's bits, low first: indicator `v` is one exactly when the digit is `v`.
fn indicators(b: &mut Builder, digit: [Kw; 3]) -> Vec<Ew> {
    let o = b.one();
    let z = b.zero();
    let mut level = vec![o];
    for a in digit {
        let len = level.len();
        let mut next = Vec::with_capacity(2 * len);
        for v in 0..2 * len {
            let p = level[v % len];
            // The new bit is bit `log2 len` of `v`: a factor `1 + a` where it is zero, `a` where it is one.
            next.push(if v < len {
                b.mul_k_add(p, a, p)
            } else {
                b.mul_k_add(p, a, z)
            });
        }
        level = next;
    }
    level
}

/// Chain `i` from its element `tip` under the digit's indicators `ind`: its end's two words.
fn chain_end(b: &mut Builder, i: usize, idx: Kw, tip: Ew, pp: &[Kw], ind: &[Ew]) -> [Kw; 2] {
    let [t0, t1, _] = b.e_to_k(tip);
    let d = tweak_hash(b, 1, 8 * i, idx, pp, &[t0, t1]);
    let (mut cur, _) = b.d_to_e_and_k(d);
    for (s, &selected) in ind[..STEPS].iter().enumerate().skip(1) {
        let diff = b.add(tip, cur);
        let m = b.mul_add(selected, diff, cur);
        let [v0, v1, _] = b.e_to_k(m);
        let d = tweak_hash(b, 1, 8 * i + s, idx, pp, &[v0, v1]);
        cur = b.d_to_e_and_k(d).0;
    }
    let diff = b.add(tip, cur);
    let end = b.mul_add(ind[STEPS], diff, cur);
    let [n0, n1, _] = b.e_to_k(end);
    [n0, n1]
}

/// Level `l` of the Merkle path: the parent of `node` and the sibling, the epoch's bit `bit` naming the side of `node`.
fn level(b: &mut Builder, l: usize, idx: Kw, bit: Kw, node: Dw, pp: &[Kw], [s0, s1]: [u64; 2]) -> Dw {
    let (cur, _) = b.d_to_e_and_k(node);
    let sib = b.free_e(F192::new(s0, s1, 0));
    let diff = b.add(cur, sib);
    let left = b.mul_k_add(diff, bit, cur);
    let right = b.add(left, diff);
    let [l0, l1, _] = b.e_to_k(left);
    let [r0, r1, _] = b.e_to_k(right);
    tweak_hash(b, 3, l + 1, idx, pp, &[l0, l1, r0, r1])
}

/// One signature's verification.
fn signature(b: &mut Builder, claim: &XmssClaim, sig: &XmssSignature) {
    let ([p0, p1], [m0, m1, m2, m3]) = (claim.public_param, claim.message);
    let pp = statement_words(b, F192::new(p0, p1, 0), 1);
    let mlo = statement_words(b, F192::new(m0, m1, 0), 1);
    let mhi = statement_words(b, F192::new(m2, m3, 0), 1);
    let ep = statement_words(b, F192::new(claim.epoch.into(), 0, 0), 2);
    let z = b.k_const(0);
    let bits = b.split(ep[0]);
    for &k in &bits[32..] {
        b.eq_k_const(k, 0);
    }
    let idx = index_word(b, &bits, 0);

    // The encoding.
    let [r0, r1, r2] = sig.randomness;
    let rho = b.free_e(F192::new(r0, r1, r2));
    let [r0, r1, r2] = b.e_to_k(rho);
    let payload: Vec<Kw> = mlo.iter().chain(&mhi).copied().chain([r0, r1, r2, z]).collect();
    let d = tweak_hash(b, 4, 0, idx, &pp, &payload);
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
    for (i, &[t0, t1]) in sig.chain_tips.iter().enumerate() {
        let tip = b.free_e(F192::new(t0, t1, 0));
        let ind = indicators(b, [digit_bits[3 * i], digit_bits[3 * i + 1], digit_bits[3 * i + 2]]);
        ends.extend(chain_end(b, i, idx, tip, &pp, &ind));
    }

    // The leaf and the path.
    let mut node = tweak_hash(b, 2, 0, idx, &pp, &ends);
    for (l, &sibling) in sig.merkle_proof.iter().enumerate() {
        let ix = index_word(b, &bits, l + 1);
        node = level(b, l, ix, bits[l], node, &pp, sibling);
    }
    let rs = b.d_to_k(node);
    let root = b.k_to_e([rs[0], rs[1], z]);
    b.expose_e(root);
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanxmss_host::{LEAF_INDEX, MESSAGE};

    /// A change to a claim.
    type Change = fn(&mut XmssClaim);
    /// A change to a claim and its signature.
    type Tamper = fn(&mut XmssClaim, &mut XmssSignature);

    /// `n` honest signers' claims and signatures.
    fn signed(n: usize) -> (Vec<XmssClaim>, Vec<XmssSignature>) {
        (leanxmss_host::signers(n).into_iter())
            .map(|(pk, s)| {
                let claim = XmssClaim {
                    public_param: pk.public_param,
                    merkle_root: pk.merkle_root,
                    epoch: LEAF_INDEX,
                    message: MESSAGE,
                };
                let signature = XmssSignature {
                    chain_tips: s.chain_tips,
                    randomness: s.randomness,
                    merkle_proof: s.merkle_proof,
                };
                (claim, signature)
            })
            .unzip()
    }

    #[test]
    fn an_honest_batch_verifies_under_its_statement_only() {
        let (claims, signatures) = signed(2);
        let batch = XmssBatch::new(2, Rate::MIN).expect("two signatures fit");
        let proof = batch.prove(&claims, &signatures).expect("honest signatures");
        let decoded = XmssProof::from_bytes(&proof.to_bytes()).expect("its own bytes");
        assert_eq!(decoded, proof);
        // The verifier's key is built from the size and the rate alone.
        let key = XmssBatch::new(2, Rate::MIN).expect("two signatures fit");
        assert_eq!(key.verify(&claims, &decoded), Ok(()));

        // Mutation: one word of each part of the second claim.
        //
        //     the statement seeds the transcript and the public rows read it
        //     → the proof of the honest claims is refused
        let changes: [(&str, Change); 4] = [
            ("the parameter", |c| c.public_param[1] ^= 1),
            ("the message", |c| c.message[3] ^= 1),
            ("the epoch", |c| c.epoch ^= 1),
            ("the root", |c| c.merkle_root[0] ^= 1),
        ];
        for (what, change) in changes {
            let mut forged = claims.clone();
            change(&mut forged[1]);
            assert!(
                matches!(key.verify(&forged, &proof), Err(XmssError::Proof(_))),
                "{what}"
            );
        }
    }

    #[test]
    fn a_tampered_signature_has_no_proof() {
        let (claims, signatures) = signed(2);
        let batch = XmssBatch::new(2, Rate::MIN).expect("two signatures fit");

        // Mutation: a chain element, a sibling, the randomness, or the claim's message, epoch or root.
        //
        //     a chain element or a sibling changes the leaf or the fold
        //     → another root than the key's
        //     the randomness, the message or the epoch changes the encoding's digest
        //     → an invalid encoding the rows refuse, or another root
        let tampered: [(&str, Tamper); 7] = [
            ("a chain element", |_, s| s.chain_tips[41][1] ^= 1 << 63),
            ("a chain element's first word", |_, s| s.chain_tips[0][0] ^= 1),
            ("a sibling", |_, s| s.merkle_proof[31][0] ^= 1),
            ("the randomness", |_, s| s.randomness[0] ^= 1),
            ("the message", |c, _| c.message[0] ^= 1),
            ("the epoch", |c, _| c.epoch ^= 1),
            ("the root", |c, _| c.merkle_root[1] ^= 1),
        ];
        for (what, tamper) in tampered {
            let (mut c, mut s) = (claims.clone(), signatures.clone());
            tamper(&mut c[1], &mut s[1]);
            let refused = batch.prove(&c, &s).err();
            assert!(
                matches!(refused, Some(XmssError::Unsatisfied(_) | XmssError::Root { index: 1 })),
                "{what}: {refused:?}"
            );
        }
    }
}
