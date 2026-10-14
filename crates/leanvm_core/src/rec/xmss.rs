//! leanXMSS signatures verified on the recursion machine: `n` signatures in one recursion proof.
//!
//! The circuit is `verification/circuits/LeanVMCircuits/Xmss/Circuit.lean`'s, which its header describes: the builder
//! calls below are that program's, in its order, and `CheckXmss` checks that the circuit built here is the one the Lean
//! program builds.
//!
//! Per signature the statement is five `E` words, in this order: the public parameter `[p0, p1, 0]`, the message's
//! words `[m0, m1, 0]` and `[m2, m3, 0]`, the epoch `[e, 0, 0]`, then the Merkle root `[r0, r1, 0]` the signature
//! reaches. The signature is the prover's.

use super::circuit::{Builder, Dw, Ew, Finished, Kw, Limbs, Replay, Unsatisfied, chain};
use super::proof::CircuitKey;
use super::tree::{CircuitStats, ClaimLayout, ClaimSet, ClaimWord, Leaf, LeafCircuit, LeafStatement, Leaves};
use crate::commitment::Rate;
use crate::cpu::{DecodeError, VerifyError};
use crate::envelope::Envelope;
use fiat_shamir::arith::Arith;
use fiat_shamir::{ProofTranscript, SessionId};
use primitives::field::F192;
use thiserror::Error;
use tracing::info_span;

/// The domain of every proof's transcript.
const DOMAIN: &[u8] = b"leanvm-xmss-rec-1";

/// Hash chains, one per encoding digit.
pub(super) const V: usize = 42;
/// Steps of a chain: its values are `0..=7`.
pub(super) const STEPS: usize = 7;
/// The Merkle tree's height.
const LOG_LIFETIME: usize = 32;
/// Statement words per signature.
const WORDS: usize = 5;

/// `X^195` in `K` as a word: the product the encoding's digit bits must reach, the digits summing to 195.
const TARGET: u64 = 0xedb8;

/// The chain steps a signature's digits need: `V · STEPS` less their sum, 195.
const CHAIN_STEPS: usize = V * STEPS - 195;

/// The bit a signature's index starts at in its chains' bus keys, above the tweak word's position.
const TAG_SHIFT: usize = 41;

/// leanXMSS's scheme word, the first of a claim's label, as the guest's signer sets write it.
const SCHEME: u64 = 1;

/// How the statement states claims, one a signature, as the guest's signer sets write them: the label is the scheme,
/// the epoch and the message's words, the member the key's root then its public parameter.
const CLAIMS: ClaimLayout = ClaimLayout {
    words: WORDS,
    label: [
        ClaimWord::Const(SCHEME),
        ClaimWord::At { at: 3, word: 0 },
        ClaimWord::At { at: 1, word: 0 },
        ClaimWord::At { at: 1, word: 1 },
        ClaimWord::At { at: 2, word: 0 },
        ClaimWord::At { at: 2, word: 1 },
    ],
    member: [
        ClaimWord::At { at: 4, word: 0 },
        ClaimWord::At { at: 4, word: 1 },
        ClaimWord::At { at: 0, word: 0 },
        ClaimWord::At { at: 0, word: 1 },
    ],
};

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
    /// The circuit and its fixed columns.
    key: CircuitKey,
    /// What a prover replays of the circuit's build, one part per signature, for its values.
    replay: Replay,
    /// The transcript's session, which names the circuit and its size.
    session: SessionId,
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
    /// Claims of more than one epoch or message, which make no claim set of one group.
    #[error("the claims are not of one epoch and message")]
    Label,
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
        if n > 1 << (63 - TAG_SHIFT) {
            return Err(XmssError::TooLarge { n });
        }
        let (finished, replay) = build(&vec![XmssClaim::default(); n], &vec![XmssSignature::ZERO; n]);
        let key = CircuitKey::new(finished.circuit).map_err(|_| XmssError::TooLarge { n })?;
        let mut tag = DOMAIN.to_vec();
        tag.extend_from_slice(&(n as u64).to_le_bytes());
        tag.push(rate.log_inv_rate());
        let session = SessionId::new(&tag);
        Ok(Self {
            n,
            rate,
            key,
            replay,
            session,
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
        CircuitStats::of(self.key.circuit())
    }

    /// The leaf family of an aggregation tree over proofs of this batch, which takes no other leaves.
    #[must_use]
    pub const fn leaves(&self) -> Leaves<'_> {
        Leaves::Circuit(self.leaf_circuit())
    }

    /// A leaf of an aggregation tree: a proof of this batch, and the claims it proves, in order.
    ///
    /// # Errors
    ///
    /// Claims of another number than the batch's.
    pub fn leaf<'a>(&self, claims: &[XmssClaim], proof: &'a XmssProof) -> Result<Leaf<'a>, XmssError> {
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
    pub fn statement(&self, claims: &[XmssClaim]) -> Result<LeafStatement, XmssError> {
        self.count(claims.len(), "claims")?;
        Ok(LeafStatement::circuit(&self.leaf_circuit(), statement(claims)))
    }

    /// The claim set a leaf of these claims publishes in a claim-set tree: one group, of the epoch and message they
    /// share, a member a key, in the claims' order, as the guest's signer sets write it.
    ///
    /// # Errors
    ///
    /// - Claims of another number than the batch's.
    /// - Claims of more than one epoch or message.
    pub fn claim_set(&self, claims: &[XmssClaim]) -> Result<ClaimSet, XmssError> {
        self.count(claims.len(), "claims")?;
        CLAIMS.set(&statement(claims)).ok_or(XmssError::Label)
    }

    const fn leaf_circuit(&self) -> LeafCircuit<'_> {
        LeafCircuit::new(&self.key, self.session, self.rate, &CLAIMS)
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
        let (assignment, failures) =
            info_span!("Build circuit").in_scope(|| self.replay.values(part(claims, signatures)));
        if let Some(first) = failures.into_iter().next() {
            return Err(XmssError::Unsatisfied(first));
        }
        let statement = statement(claims);
        if let Some(i) = (0..self.n).find(|&i| assignment.statement()[WORDS * i + 4] != statement[WORDS * i + 4]) {
            return Err(XmssError::Root { index: i });
        }
        debug_assert!(
            build(claims, signatures).0.circuit == *self.key.circuit(),
            "the rows never depend on the values"
        );
        let proof = self.key.prove(&assignment, &self.session, self.rate);
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
        (self.key)
            .verify(&statement(claims), &self.session, self.rate, &proof.proof)
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
        let ((finished, _), calls) =
            super::circuit::traced(|| build(&vec![XmssClaim::default(); n], &vec![XmssSignature::ZERO; n]));
        let circuit = self.key.circuit();
        assert_eq!(&finished.circuit, circuit, "a circuit is built the same every time");
        calls + "circuit\n" + &circuit.dump() + &self.key.fixed().dump_next(circuit)
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

/// The circuit verifying the signatures, with their values, and its replay: `Circuit.circuit n`.
fn build(claims: &[XmssClaim], signatures: &[XmssSignature]) -> (Finished, Replay) {
    Builder::parts(claims.len(), part(claims, signatures))
}

/// The circuit's part verifying signature `i`.
fn part<'a>(claims: &'a [XmssClaim], signatures: &'a [XmssSignature]) -> impl Fn(&mut Builder, usize) + Sync + 'a {
    move |b, i| {
        b.scope(format!("signature {i}"), |b| {
            signature(b, i, &claims[i], &signatures[i]);
        });
    }
}

/// A tweak's first word: the domain separator zero, the tweak's type in byte 1, its position in bytes 4 to 7.
const fn tweak0(ty: u64, pos: usize) -> u64 {
    ty << 8 | (pos as u64) << 32
}

/// A statement word exposed, its words; `zeros` of its words past the first `3 - zeros` are held to zero.
pub(super) fn statement_words(b: &mut Builder, value: F192, zeros: usize) -> Vec<Kw> {
    let w = b.free_e(value);
    b.expose(w);
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
pub(super) fn digit_product(b: &mut Builder, bits: &[Kw]) -> Ew {
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

/// Chains on the dynamic bus, `Circuit.chains`: an activity wire held to one, the tweak words' base `base` (below
/// `2^32`) and the tag `tag << TAG_SHIFT` as constants, a link row per chain from its tip at its digit to its end,
/// then `n_steps` steps the digits need, chain by chain, each pulling its input at its chain's position and pushing
/// its output at the next. Returns the ends' wires.
#[expect(
    clippy::too_many_arguments,
    reason = "the arguments of `Circuit.chains` and the chains' tips"
)]
pub(super) fn chains(
    b: &mut Builder,
    base: u64,
    tag: u64,
    n_steps: usize,
    idx: Kw,
    pp: [Kw; 2],
    digit_bits: &[Kw],
    tips: &[[u64; 2]],
) -> Vec<Kw> {
    let one = b.free_k(1);
    b.eq_k_const(one, 1);
    let base_w = b.k_const(base);
    let tag_word = tag << TAG_SHIFT;
    let tag_w = b.k_const(tag_word);
    let (idx_word, p) = (b.k(idx), pp.map(|w| b.k(w)));
    let mut steps = Vec::with_capacity(n_steps);
    let mut ends = Vec::with_capacity(2 * tips.len());
    for (i, &tip) in tips.iter().enumerate() {
        let digit: u64 = (0..3).map(|k| b.k(digit_bits[3 * i + k]) << k).sum();
        let mut v = tip;
        for s in usize::try_from(digit).expect("a digit is three bits")..STEPS {
            let tweak = base | ((8 * i + s) as u64) << 32;
            steps.push((tweak, v));
            let d = chain(&[tweak, idx_word, p[0], p[1], v[0], v[1]]);
            v = [d[0], d[1]];
        }
        let w = b.k_const(base | ((8 * i) as u64) << 32 | tag_word);
        let d = [digit_bits[3 * i], digit_bits[3 * i + 1], digit_bits[3 * i + 2]];
        ends.extend(b.link(w, d, one, tip, v));
    }
    // Digits off the target sum need another number of steps; the encoding's check already fails on them.
    steps.resize(n_steps, (0, [0, 0]));
    for &(tweak, v) in &steps {
        b.chain_step(idx, pp, base_w, tag_w, one, tweak, v);
    }
    ends
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
fn signature(b: &mut Builder, j: usize, claim: &XmssClaim, sig: &XmssSignature) {
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
    let ends = chains(
        b,
        tweak0(1, 0),
        j as u64,
        CHAIN_STEPS,
        idx,
        [pp[0], pp[1]],
        &digit_bits,
        &sig.chain_tips,
    );

    // The leaf and the path.
    let mut node = tweak_hash(b, 2, 0, idx, &pp, &ends);
    for (l, &sibling) in sig.merkle_proof.iter().enumerate() {
        let ix = index_word(b, &bits, l + 1);
        node = level(b, l, ix, bits[l], node, &pp, sibling);
    }
    let rs = b.d_to_k(node);
    let root = b.k_to_e([rs[0], rs[1], z]);
    b.expose(root);
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
    fn a_proof_replays_the_build() {
        let (claims, signatures) = signed(2);
        let batch = XmssBatch::new(2, Rate::MIN).expect("two signatures fit");

        // Mutation: the randomness of the second signature.
        //
        //     its digits change, and the steps they need
        //     → the build's failures, the encoding's and the dynamic tuples'
        let mut tampered = signatures.clone();
        tampered[1].randomness[0] ^= 1;
        for (sigs, honest) in [(&signatures, true), (&tampered, false)] {
            let built = build(&claims, sigs).0;
            let failures = batch.replay.assert_replays(part(&claims, sigs), &built);
            assert_eq!(failures.is_empty(), honest);
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
