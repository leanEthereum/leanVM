//! The verifier of a leanVM proof as rows of the recursion machine (Annex E).
//!
//! - The bus, its GKR and the table sumcheck are the native verifier's own code, run over wires.
//! - The flock reductions and the opening are the native verifier's code too, over the rows' transcript and Merkle openings.
//!
//! No row depends on a value: a circuit built from a proof equals the one built from its shape.

use super::circuit::{Builder, Dw, Ew, Kw};
use super::transcript::Transcript;
use crate::bus::{PublicColumn, PublicColumns};
use fiat_shamir::arith::{Arith, PublicMle, Stage, Verifier};
use fiat_shamir::{TranscriptContext, TranscriptError};
use pcs::verifier::OpeningVerifier;
use pcs::whir::Stratum;
use primitives::field::F192;
use recursion::FixedHints;
use std::fmt::Debug;

mod recursion;
mod riscv;

pub(crate) use recursion::{FixedHint, RecShape};
pub use riscv::ProofShape;

/// The verifier's arithmetic and transcript as rows: a circuit being built, and a transcript replayed in it.
///
/// A read never fails and an equality never refuses: both become rows, which the outer proof checks.
///
/// A public column is evaluated in rows, unless it is a fixed column of the recursion proof being verified: its evaluation is then a hint.
pub(crate) struct Rows<'a, 's> {
    b: &'a mut Builder,
    t: &'a mut Transcript<'s>,
    fixed: Option<&'a mut FixedHints<'s>>,
}

impl<'a, 's> Rows<'a, 's> {
    /// Rows appended to `b`, reading through `t`.
    pub(crate) const fn new(b: &'a mut Builder, t: &'a mut Transcript<'s>) -> Self {
        Self { b, t, fixed: None }
    }

    /// Rows appended to `b`, reading through `t`, that take every evaluation of a fixed column as a hint.
    pub(crate) const fn hinting(b: &'a mut Builder, t: &'a mut Transcript<'s>, fixed: &'a mut FixedHints<'s>) -> Self {
        Self {
            b,
            t,
            fixed: Some(fixed),
        }
    }
}

impl Rows<'_, '_> {
    /// Each query's row, its opening the next phase's, hashed up its own low levels to its stratum's node, every node
    /// then tied to the root.
    ///
    /// A query of stratum `(s, j)` is hashed up its `depth - s` low levels to node `j` of the top subtree's level `s`.
    /// The batch's largest group reaches every node of the subtree's bottom level, which is hashed once up to the root.
    /// Every other query's node is the subtree's.
    /// So each leaf sits `depth` levels below the root, as the shape fixes.
    fn authenticate(&mut self, root: Dw, queries: &[Vec<Kw>], row_words: usize, leaf_words: usize) -> Vec<Vec<Kw>> {
        self.t.next_openings();
        let depth = queries[0].len();
        let strata = Stratum::batch(queries.len(), depth);
        let top = strata[0].bits;
        let mut nodes: Vec<Vec<Option<Dw>>> = (0..=top).map(|s| vec![None; 1 << s]).collect();
        let tie = |b: &mut Builder, slot: &mut Option<Dw>, node: Dw| match *slot {
            Some(known) => b.eq(known, node),
            None => *slot = Some(node),
        };
        let rows = (queries.iter().zip(&strata))
            .map(|(bits, s)| {
                let row = self.t.open_row(self.b, &bits[..depth - s.bits], row_words, leaf_words);
                tie(self.b, &mut nodes[s.bits][s.index], row.node);
                row.words
            })
            .collect();
        for s in (1..=top).rev() {
            for j in 0..1 << (s - 1) {
                let [left, right] =
                    [2 * j, 2 * j + 1].map(|i| nodes[s][i].expect("the largest group covers its level"));
                let node = self.b.parent(left, right);
                tie(self.b, &mut nodes[s - 1][j], node);
            }
        }
        tie(self.b, &mut nodes[0][0], root);
        rows
    }
}

impl PublicMle for Builder {}

impl Arith for Rows<'_, '_> {
    type E = Ew;

    fn constant(&mut self, c: F192) -> Ew {
        self.b.e_const(c)
    }

    fn mul_add(&mut self, a: Ew, b: Ew, d: Ew) -> Ew {
        self.b.mul_add(a, b, d)
    }

    fn add(&mut self, a: Ew, d: Ew) -> Ew {
        self.b.add(a, d)
    }

    fn mul_const_add(&mut self, a: Ew, c: F192, d: Ew) -> Ew {
        self.b.mul_const_add(a, c, d)
    }

    fn inv(&mut self, a: Ew) -> Ew {
        self.b.inv(a)
    }

    fn frobenius2(&mut self, a: Ew) -> Ew {
        self.b.frobenius2(a)
    }

    fn zero(&mut self) -> Ew {
        self.b.zero()
    }

    fn one(&mut self) -> Ew {
        self.b.one()
    }

    fn mul(&mut self, a: Ew, b: Ew) -> Ew {
        self.b.mul(a, b)
    }
}

impl PublicMle for Rows<'_, '_> {}

impl PublicColumns for Rows<'_, '_> {
    fn column_mle(&mut self, column: &PublicColumn, point: &[Ew]) -> Ew {
        match (self.fixed.as_deref_mut(), column.fixed) {
            (Some(hints), Some(fixed)) => hints.evaluate(self.b, fixed, point),
            _ => self.b.public_mle(&column.values, point),
        }
    }
}

impl Verifier for Rows<'_, '_> {
    fn prover_message(&mut self) -> Result<Ew, TranscriptError> {
        Ok(self.t.prover_message(self.b))
    }

    fn verifier_message(&mut self) -> Ew {
        self.t.verifier_message(self.b)
    }

    fn check_pow(&mut self, bits: u32) -> Result<(), TranscriptError> {
        self.t.check_pow(self.b, bits);
        Ok(())
    }

    fn ensure_eq<Er>(&mut self, a: Ew, b: Ew, _: impl FnOnce() -> Er) -> Result<(), Er> {
        self.b.eq(a, b);
        Ok(())
    }

    fn check_eof(&mut self) -> Result<(), TranscriptError> {
        // A recorded failure, not a constraint: in rows the proof is only the witness, so nothing is left to read.
        // It catches an honest prover's mismatch with the native verifier, and protects nothing else.
        if !self.t.finished() {
            self.begin_scope(Stage::Transcript);
            self.b.fail("the proof has data the verifier never reads");
            self.end_scope();
        }
        Ok(())
    }

    fn begin_scope(&mut self, stage: Stage) {
        let name = match stage {
            Stage::Announcement => "announcement",
            Stage::BusAndTables => "bus and tables",
            Stage::Flock => "flock",
            Stage::Lincheck => "lincheck",
            Stage::Opening => "opening",
            Stage::Rows => "rows",
            Stage::Target => "target",
            Stage::Terminal => "terminal",
            Stage::Transcript => "transcript",
            Stage::Whir => "whir",
            Stage::Zerocheck => "zerocheck",
        };
        self.b.enter(name);
    }

    fn end_scope(&mut self) {
        self.b.leave();
    }
}

impl OpeningVerifier for Rows<'_, '_> {
    type Root = Dw;
    type K = Kw;
    /// A query's index bits, lowest first.
    type Query = Vec<Kw>;

    fn context(&mut self) -> TranscriptContext<Kw, Dw> {
        self.t.context()
    }

    fn zero_k(&mut self) -> Kw {
        self.b.k_const(0)
    }

    fn ensure_root_eq(&mut self, actual: Dw, expected: Dw) -> Result<(), pcs::whir::WhirError> {
        for (actual, expected) in self.b.d_to_k(actual).into_iter().zip(self.b.d_to_k(expected)) {
            self.b.eq(actual, expected);
        }
        Ok(())
    }

    fn next_root(&mut self) -> Result<Dw, TranscriptError> {
        Ok(self.t.prover_root(self.b))
    }

    /// Each challenge's 192 bits `c0 | c1 << 64 | c2 << 128`, split, then cut into queries.
    fn sample_queries(&mut self, depth: usize, count: usize) -> Vec<Vec<Kw>> {
        let per = 192 / depth;
        let mut out = Vec::with_capacity(count);
        while out.len() < count {
            let v = self.verifier_message();
            let n = per.min(count - out.len());
            let limbs = self.b.e_to_k(v);
            let mut bits = Vec::with_capacity(192);
            for &limb in &limbs[..(n * depth).div_ceil(64)] {
                bits.extend(self.b.split(limb));
            }
            out.extend((0..n).map(|j| bits[j * depth..(j + 1) * depth].to_vec()));
        }
        // Each query's top bits are its stratum's, constants of the shape.
        for (bits, s) in out.iter_mut().zip(Stratum::batch(count, depth)) {
            let low = depth - s.bits;
            for (i, bit) in bits[low..].iter_mut().enumerate() {
                *bit = self.b.k_const((s.index >> i) as u64 & 1);
            }
        }
        out
    }

    fn open_rows(
        &mut self,
        root: &Dw,
        _depth: usize,
        queries: &[Vec<Kw>],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<Kw>>, TranscriptError> {
        Ok(self.authenticate(*root, queries, row_words, leaf_words))
    }

    fn mul_k_add(&mut self, a: Ew, k: Kw, d: Ew) -> Ew {
        self.b.mul_k_add(a, k, d)
    }

    fn e_of_limbs(&mut self, limbs: [Kw; 3]) -> Ew {
        self.b.k_to_e(limbs)
    }

    fn query_point(&mut self, bits: &Vec<Kw>) -> Ew {
        let q = self.b.pack(bits);
        self.b.k_to_e1(q)
    }
}

/// The value of a read the rows never refuse.
pub(crate) fn infallible<T, Er: Debug>(read: Result<T, Er>) -> T {
    read.unwrap_or_else(|e| unreachable!("rows record a failure rather than refuse: {e:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::ConstraintError;
    use crate::tables::{CircuitId, Fill, TableId};

    use crate::commitment::{Commitment, Committed, Rate, RingSwitch, SliceClaim, StackClaim};
    use crate::rec::RecError;
    use crate::rec::circuit::{Assignment, Builder, Circuit, Ew, Finished, Kw, Unsatisfied};
    use crate::rec::hash;
    use crate::rec::proof::CircuitKey;
    use crate::rec::transcript::{ProofSource, Transcript};

    use crate::stacking::StackShape;
    use fiat_shamir::{Encoding, FromNarg, ProofTranscript, ProverState, SessionId, VerifierState};
    use flock::BatchRows;
    use flock::FlockError;
    use flock::reduction::{self, Block, Instance, ReductionReplay, Shape};
    use flock::test_util::Witness;
    use flock::zerocheck::K_SKIP;
    use pcs::merkle::{Hash, Openings, hash_leaf, hash_pair};
    use pcs::verifier::Recording;
    use pcs::whir::{Stratum, WhirError};
    use primitives::field::{F64, F192};
    use primitives::multilinear::inner_product_base;
    use primitives::test_util::Rng;

    // Message `i` of a proof whose first `i + 1` messages are field elements.
    pub(super) fn scalar(proof: &ProofTranscript, i: usize) -> F192 {
        F192::from_narg(&mut &proof.narg[24 * i..]).expect("a message")
    }

    // Replace message `i` of a proof whose first `i + 1` messages are field elements.
    pub(super) fn set_scalar(proof: &mut ProofTranscript, i: usize, x: F192) {
        proof.narg[24 * i..24 * i + 24].copy_from_slice(&x.encode());
    }

    // The level-0 batch: the largest group's first query feeds the shared subtree's bottom level, and the first query of
    // the next group reaches a node inside it. A wrong sibling right under either node breaks the tie to the subtree.
    #[test]
    fn a_wrong_sibling_under_the_shared_subtree_is_refused() {
        // Fixture: a tree of 2^6 one-block leaves, and 21 queries in their strata.
        let (depth, count) = (6, 21);
        let leaves: Vec<Hash> = (0..1u64 << depth)
            .map(|i| hash_leaf(&(0..8).flat_map(|j| (8 * i + j).to_le_bytes()).collect::<Vec<u8>>()))
            .collect();
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let level = levels.last().unwrap();
            levels.push(level.chunks(2).map(|pair| hash_pair(&pair[0], &pair[1])).collect());
        }
        let root = levels.last().unwrap()[0];
        let strata = Stratum::batch(count, depth);
        let mut rng = Rng::new(9);
        let queries: Vec<usize> = (strata.iter())
            .map(|s| {
                let low = depth - s.bits;
                (rng.next_u64() as usize & ((1 << low) - 1)) | s.index << low
            })
            .collect();

        // Each query's honest full path, and the rows hashing them.
        let path = |q: usize| -> Vec<Hash> { (0..depth).map(|l| levels[l][(q >> l) ^ 1]).collect() };
        let failures = |forge: Option<usize>| {
            let mut b = Builder::new();
            let instance = [b.k_const(0)];
            let mut openings = Openings {
                leaf_words: 8,
                height: depth,
                images: Vec::new(),
                paths: Vec::new(),
            };
            for (i, &q) in queries.iter().enumerate() {
                let mut path = path(q);
                if forge == Some(i) {
                    path[depth - strata[i].bits - 1][0] ^= 1;
                }
                openings.images.extend((0..8).map(|j| F64(8 * q as u64 + j)));
                openings.paths.extend(path);
            }
            let proof = ProofTranscript::default();
            let phases = [openings];
            let mut t = Transcript::new(
                &mut b,
                &SessionId::new(LABEL),
                &instance,
                ProofSource::Proof(&proof, &phases),
            );
            let bits: Vec<Vec<Kw>> = (queries.iter())
                .map(|&q| (0..depth).map(|l| b.k_const((q >> l) as u64 & 1)).collect())
                .collect();
            let root = b.d_const(primitives::hash::digest_words(&root));
            Rows::new(&mut b, &mut t).authenticate(root, &bits, 8, 8);
            b.finish().failures
        };
        assert!(failures(None).is_empty(), "the honest paths tie to the root");

        // The largest group's first query, and the first query of a group with fixed bits inside the subtree.
        let inner = strata.iter().position(|s| s.bits < strata[0].bits && s.bits > 0);
        let inner = inner.expect("the batch has a second group with fixed bits");
        for q in [0, inner] {
            assert!(!failures(Some(q)).is_empty(), "query {q}");
        }
    }

    // The direction bit of a Merkle node is the hash row's mux selector: a non-Boolean one is refused by the outer verifier.
    #[test]
    fn a_non_boolean_merkle_selector_is_refused() {
        let mut b = Builder::new();
        let acc = b.free_d([1, 2, 3, 4]);
        let bit = b.free_k(1);
        let parent = b.node(acc, bit, [5, 6, 7, 8]);
        b.expose(parent);
        let Finished {
            circuit,
            assignment: mut a,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let session = SessionId::new(b"selector-test");
        let statement = a.statement().to_vec();
        let key = CircuitKey::new(circuit).expect("the circuit fits");
        let prove = |a: &Assignment| key.prove(a, &session, Rate::MIN);
        let verify = |proof: &ProofTranscript| key.verify(&statement, &session, Rate::MIN, proof).map(drop);
        assert_eq!(verify(&prove(&a)), Ok(()));
        a.values[bit.0 as usize][0] = 2;
        assert_eq!(
            verify(&prove(&a)),
            Err(RecError::Constraint(ConstraintError::FinalMismatch))
        );
    }

    pub(super) const LABEL: &[u8] = b"rec-verifier-test";

    // A rows transcript from the test label over `source`, and what `f` builds on it.
    fn replay<T>(source: ProofSource<'_>, f: impl FnOnce(&mut Rows<'_, '_>) -> T) -> (Builder, T, bool) {
        let mut b = Builder::new();
        let instance = [b.k_const(0)];
        let mut t = Transcript::new(&mut b, &SessionId::new(LABEL), &instance, source);
        let out = f(&mut Rows::new(&mut b, &mut t));
        let finished = t.finished();
        (b, out, finished)
    }

    // Packed witness `f`'s batch over `rows`, as the prover holds it.
    struct Batch {
        block: Block<'static>,
        n_blocks_log: usize,
        witness: Witness,
    }

    fn batch<const N: usize>(f: CircuitId, rows: &[[u64; N]]) -> Batch {
        let (circuit, spec) = (f.circuit(), f.table().spec());
        let n_blocks_log = spec.n_blocks_log(rows.len());
        let witness = match spec.circuit.as_ref().map(|c| c.fill) {
            Some(Fill::Instance(instance)) => Witness::by_instance(
                circuit,
                BatchRows::new(rows, &[0; N], n_blocks_log),
                |row, z, az, bz| instance(row, z, az, bz),
            ),
            _ => Witness::by_walk(circuit, BatchRows::new(rows, &[0; N], n_blocks_log), |row, words| {
                words.copy_from_slice(row);
            }),
        };
        Batch {
            block: circuit.block(),
            n_blocks_log,
            witness,
        }
    }

    // The reduction's matrix claims settle, its rows read the whole proof and are the shape's, and a tampered scalar fails both verifiers at one stage.
    fn check_reductions(batches: &[Batch]) {
        let proof = {
            let instances: Vec<Instance<'_>> = (batches.iter())
                .map(|batch| batch.witness.instance(batch.block, batch.n_blocks_log))
                .collect();
            let mut ps = ProverState::new(&SessionId::new(LABEL), &0u64);
            reduction::prove(&instances, &mut ps);
            ps.into_proof()
        };
        let circuits: Vec<(Shape, usize)> = (batches.iter())
            .map(|batch| (batch.block.shape(), batch.n_blocks_log))
            .collect();
        let native = |proof: &ProofTranscript| {
            let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, proof);
            reduction::verify(&circuits, &mut vs)
        };
        let rows = |source: ProofSource<'_>| replay(source, |r| infallible(reduction::verify(&circuits, r)));

        let replays = native(&proof).expect("an honest batch");
        for (batch, replay) in batches.iter().zip(&replays) {
            assert_eq!(
                replay.matrices.form.evaluate(batch.block.circuit),
                replay.matrices.value
            );
        }
        let (b, _, finished) = rows(ProofSource::Proof(&proof, &[]));
        assert!(finished, "the rows read the whole proof");
        let Finished { circuit, failures, .. } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        assert!(
            circuit == rows(ProofSource::Shape).0.finish().circuit,
            "the shape builds another circuit"
        );

        // The first scalar of the zerocheck's first round, the last circuit's `c` claim, the last lincheck round's top
        // coefficient, the first circuit's first slice and its form's value.
        let n = batches.len();
        let tail = n * (F64::DEGREE + 1);
        let n_rounds = (circuits.iter())
            .map(|(shape, _)| shape.k_log - K_SKIP)
            .max()
            .unwrap_or(0);
        let lincheck_start = proof.narg.len() / 24 - tail - 2 * n_rounds;
        let len = proof.narg.len() / 24;
        let tampers = [
            (0, "zerocheck"),
            (lincheck_start - 1, "zerocheck"),
            (len - tail - 1, "lincheck"),
            (len - tail, "lincheck"),
            (len - tail + F64::DEGREE, "lincheck"),
        ];
        for (index, stage) in tampers {
            let mut forged = proof.clone();
            forged.narg[24 * index] ^= 1;
            let refused = match native(&forged) {
                Err(FlockError::Zerocheck(_)) => "zerocheck",
                Err(FlockError::Lincheck(_)) => "lincheck",
                Ok(_) => "",
            };
            assert_eq!(refused, stage, "the native verifier refuses scalar {index}");
            let failures = rows(ProofSource::Proof(&forged, &[])).0.finish().failures;
            assert!(
                failures.first().is_some_and(|f| f.scope()[0] == stage),
                "scalar {index}: {failures:?}"
            );
        }

        // A value moved between two circuits' forms keeps the batch's identity: the reduction accepts, and the claims do not settle.
        if n > 1 {
            let lifts: Vec<F192> = {
                // A circuit's lincheck rounds bind its inner coordinates top first: its round challenges are its
                // column point reversed, a prefix of the longest circuit's.
                let rounds = |replay: &ReductionReplay| replay.matrices.form.r_inner_rest.len();
                let longest = replays.iter().max_by_key(|r| rounds(r)).expect("a batch");
                let r_rounds: Vec<F192> = longest.matrices.form.r_inner_rest.iter().rev().copied().collect();
                let alpha_4 = replays[0].matrices.form.alpha.square().square();
                let weights = alpha_4.powers(n);
                (replays.iter().zip(weights))
                    .map(|(replay, w)| r_rounds[rounds(replay)..].iter().fold(w, |acc, &r| acc * r))
                    .collect()
            };
            let delta = F192::new(7, 0, 0);
            let mut forged = proof;
            let (a, b) = (len - tail + F64::DEGREE, len - tail + 2 * F64::DEGREE + 1);
            let (moved_a, moved_b) = (
                scalar(&forged, a) + delta * lifts[1],
                scalar(&forged, b) + delta * lifts[0],
            );
            set_scalar(&mut forged, a, moved_a);
            set_scalar(&mut forged, b, moved_b);
            let moved = native(&forged).expect("the batch's identity holds");
            for (f, replay) in moved.iter().enumerate() {
                let matrices = &replay.matrices;
                let settles = matrices.form.evaluate(batches[f].block.circuit) == matrices.value;
                assert_eq!(settles, f > 1, "circuit {f}'s moved claim");
            }
        }
    }

    fn hash_batch(seed: u64) -> Batch {
        let mut rng = Rng::new(seed);
        let rows: Vec<[u64; 14]> = (0..5).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
        batch(hash::CIRCUIT, &rows)
    }

    fn ld_batch(seed: u64, n: usize) -> Batch {
        let mut rng = Rng::new(seed);
        let rows: Vec<[u64; 2]> = (0..n).map(|_| [rng.next_u64(), rng.next_u64()]).collect();
        batch(CircuitId::class(TableId::LD).unwrap(), &rows)
    }

    #[test]
    fn the_hash_reduction_holds_in_both_verifiers() {
        check_reductions(&[hash_batch(0xA7)]);
    }

    // Two block sizes, and two batches of one circuit at different heights, so the claims sit at prefixes of one another.
    #[test]
    fn a_mixed_batch_holds_in_both_verifiers() {
        check_reductions(&[ld_batch(0x5EED, 20), hash_batch(0xA7), ld_batch(0xB0B, 300)]);
    }

    // Fewer lanes than a leaf holds, and not whole blocks of them, so the level-0 image has a zero prefix.
    const N_LANES: usize = 37;

    // The 64 bit slices of the packed words `q` at `point`.
    fn slices(q: &[F64], point: &[F192]) -> Vec<F192> {
        let eq = primitives::multilinear::eq_table(point);
        (0..F64::DEGREE)
            .map(|i| (q.iter().zip(&eq)).fold(F192::ZERO, |acc, (w, &e)| if w.0 >> i & 1 == 1 { acc + e } else { acc }))
            .collect()
    }

    // The regions with every claim's elements as free wires holding their values.
    fn ring_wires(r: &mut Rows<'_, '_>, rings: &[RingSwitch]) -> Vec<RingSwitch<Ew>> {
        (rings.iter())
            .map(|ring| RingSwitch {
                offset: ring.offset,
                qflock_vars: ring.qflock_vars,
                claims: (ring.claims.iter())
                    .map(|claim| SliceClaim {
                        suffix_point: claim.suffix_point.iter().map(|&v| r.b.free_e(v)).collect(),
                        s_hat_v: claim.s_hat_v.iter().map(|&v| r.b.free_e(v)).collect(),
                    })
                    .collect(),
            })
            .collect()
    }

    // Point and strided claims and two ring-switched regions on a stack of `N_LANES` lanes, their values read from `q`.
    fn opening_claims(mu: usize, q: &[F64], rng: &mut Rng) -> (Vec<StackClaim>, Vec<RingSwitch>) {
        let lane = 1usize << (mu - crate::commitment::LOG_BATCH);
        let eq = primitives::multilinear::eq_table;
        let mut slots = Vec::new();
        for (offset, vars) in [(0, mu - 6), (2 * lane, mu - 5), (8, 3), (5, 0)] {
            let low_point = rng.ext_vec(vars);
            let value = inner_product_base(&q[offset..offset + (1 << vars)], &eq(&low_point));
            slots.push(StackClaim::Point {
                offset,
                low_point,
                value,
            });
        }
        for (offset, slot, stride_log) in [(4 * lane, 5, 3), (6 * lane, 0, 0)] {
            let point = rng.ext_vec(mu - 6 - stride_log);
            let value = (eq(&point).iter().enumerate()).fold(F192::ZERO, |acc, (j, e)| {
                acc + e.mul_base(q[offset + slot + (j << stride_log)])
            });
            slots.push(StackClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                value,
            });
        }
        let rings = [(4 * lane, mu - 4, 2), (16 * lane, mu - 5, 1)]
            .into_iter()
            .map(|(offset, qflock_vars, n_claims)| RingSwitch {
                offset,
                qflock_vars,
                claims: (0..n_claims)
                    .map(|_| {
                        let suffix_point = rng.ext_vec(qflock_vars);
                        let s_hat_v = slices(&q[offset..offset + (1 << qflock_vars)], &suffix_point);
                        SliceClaim { suffix_point, s_hat_v }
                    })
                    .collect(),
            })
            .collect();
        (slots, rings)
    }

    // The opening's rows over `source`, its claims free wires holding the given values.
    fn opening_rows(
        shape: StackShape,
        rate: Rate,
        slots: &[StackClaim],
        rings: &[RingSwitch],
        source: ProofSource<'_>,
    ) -> (Circuit, Vec<Unsatisfied>, bool) {
        let (b, (), finished) = replay(source, |r| {
            let commitment = infallible(Commitment::read(r, shape, rate));
            let wire = |r: &mut Rows<'_, '_>, v: &F192| r.b.free_e(*v);
            let slot_wires: Vec<StackClaim<Ew>> = (slots.iter())
                .map(|claim| match claim {
                    StackClaim::Point {
                        offset,
                        low_point,
                        value,
                    } => StackClaim::Point {
                        offset: *offset,
                        low_point: low_point.iter().map(|v| wire(r, v)).collect(),
                        value: wire(r, value),
                    },
                    StackClaim::Strided {
                        offset,
                        slot,
                        stride_log,
                        point,
                        value,
                    } => StackClaim::Strided {
                        offset: *offset,
                        slot: *slot,
                        stride_log: *stride_log,
                        point: point.iter().map(|v| wire(r, v)).collect(),
                        value: wire(r, value),
                    },
                })
                .collect();
            let ring_wires = ring_wires(r, rings);
            infallible(commitment.verify(r, &slot_wires, &ring_wires));
        });
        let done = b.finish();
        (done.circuit, done.failures, finished)
    }

    const FRESH_OPENING_LABEL: &[u8] = b"rec-verifier-fresh-opening";

    // Keep the original wires in one builder while the opening uses a separate transcript.
    fn fresh_opening_rows(
        original_label: &[u8],
        shape: StackShape,
        rate: Rate,
        rings: &[RingSwitch],
        header: ProofSource<'_>,
        opening: ProofSource<'_>,
    ) -> (Circuit, Vec<Unsatisfied>, bool) {
        let mut b = Builder::new();
        let instance = [b.k_const(0)];
        let mut original = Transcript::new(&mut b, &SessionId::new(original_label), &instance, header);
        let commitment = {
            let mut r = Rows::new(&mut b, &mut original);
            infallible(Commitment::read(&mut r, shape, rate))
        };
        let header_finished = original.finished();
        let mut fresh = Transcript::new(&mut b, &SessionId::new(FRESH_OPENING_LABEL), &instance, opening);
        {
            let mut r = Rows::new(&mut b, &mut fresh);
            let rings = ring_wires(&mut r, rings);
            infallible(commitment.verify(&mut r, &[], &rings));
        }
        let finished = header_finished && fresh.finished();
        let done = b.finish();
        (done.circuit, done.failures, finished)
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the test's statement is fixed before the transcript: public"
    )]
    fn a_fresh_opening_keeps_the_original_record_in_both_verifiers() {
        use pcs::stack::{CommittedStack, StackCommitment, Statement};

        const OTHER_ORIGINAL_LABEL: &[u8] = b"rec-verifier-other-original";
        let shape = StackShape {
            mu: crate::commitment::MIN_MU,
            n_lanes: N_LANES,
            hiding: false,
        };
        let rate = Rate::MIN;
        let config =
            pcs::whir::Config::for_rate(shape.mu, usize::from(rate.log_inv_rate())).expect("supported profile");
        let mut rng = Rng::new(0x7265_636f_7264);
        let q: Vec<F64> = (0..shape.committed_len()).map(|_| F64(rng.next_u64())).collect();
        let vars = shape.mu - crate::commitment::LOG_BATCH;
        let point = rng.ext_vec(vars);
        let rings = [RingSwitch {
            offset: 0,
            qflock_vars: vars,
            claims: vec![SliceClaim {
                s_hat_v: slices(&q[..1 << vars], &point),
                suffix_point: point,
            }],
        }];
        let mut original = ProverState::new(&SessionId::new(LABEL), &0u64);
        let committed = CommittedStack::new(&mut original, &q, shape.mu, config.clone());
        let header = original.into_proof();
        let mut other = ProverState::new(&SessionId::new(OTHER_ORIGINAL_LABEL), &0u64);
        let foreign = CommittedStack::new(&mut other, &q, shape.mu, config.clone());
        assert_eq!(committed.root(), foreign.root());
        let other_header = other.into_proof();

        let read_header = |label: &[u8], header: &ProofTranscript| {
            let mut vs = VerifierState::new(&SessionId::new(label), &0u64, header);
            let record = StackCommitment::receive(&mut vs, shape.mu, shape.n_lanes, config.clone()).expect("a record");
            vs.check_eof().expect("only the original commitment");
            record
        };
        let record = read_header(LABEL, &header);
        let foreign_record = read_header(OTHER_ORIGINAL_LABEL, &other_header);
        let mut fresh = ProverState::new(&SessionId::new(FRESH_OPENING_LABEL), &0u64);
        committed.open(
            &mut fresh,
            &q,
            Statement {
                points: &[],
                rings: &rings,
            },
        );
        let opening = fresh.into_proof();
        let mut vs = Recording::new(VerifierState::new(
            &SessionId::new(FRESH_OPENING_LABEL),
            &0u64,
            &opening,
        ));
        record
            .verify(
                &mut vs,
                Statement {
                    points: &[],
                    rings: &rings,
                },
            )
            .expect("the original record works in a separate session");
        vs.transcript().check_eof().expect("only the fresh opening");
        let openings = vs.into_openings();
        let (circuit, failures, finished) = fresh_opening_rows(
            LABEL,
            shape,
            rate,
            &rings,
            ProofSource::Proof(&header, &[]),
            ProofSource::Proof(&opening, &openings),
        );
        assert!(failures.is_empty(), "honest fresh-session rows: {failures:?}");
        assert!(finished, "both transcripts must be consumed independently");
        assert!(
            circuit == fresh_opening_rows(LABEL, shape, rate, &rings, ProofSource::Shape, ProofSource::Shape).0,
            "the fresh-session shape must build the same constraints",
        );

        let mut vs = VerifierState::new(&SessionId::new(FRESH_OPENING_LABEL), &0u64, &opening);
        assert_eq!(
            foreign_record.verify(
                &mut vs,
                Statement {
                    points: &[],
                    rings: &rings,
                },
            ),
            Err(WhirError::CommitmentMismatch),
        );
        let (_, failures, finished) = fresh_opening_rows(
            OTHER_ORIGINAL_LABEL,
            shape,
            rate,
            &rings,
            ProofSource::Proof(&other_header, &[]),
            ProofSource::Proof(&opening, &openings),
        );
        assert!(finished, "row constraints must retain the complete fresh transcript");
        assert!(
            !failures.is_empty(),
            "the same Merkle root must not substitute another original context"
        );

        // Both record digests are raw 32-byte messages, and every one of their four limbs is constrained.
        for start in [3 * 24, 3 * 24 + 32] {
            for limb in 0..4 {
                let mut forged = opening.clone();
                forged.narg[start + 8 * limb] ^= 1;
                let mut vs = VerifierState::new(&SessionId::new(FRESH_OPENING_LABEL), &0u64, &forged);
                assert_eq!(
                    record.verify(
                        &mut vs,
                        Statement {
                            points: &[],
                            rings: &rings
                        }
                    ),
                    Err(WhirError::CommitmentMismatch),
                );
                let (_, failures, finished) = fresh_opening_rows(
                    LABEL,
                    shape,
                    rate,
                    &rings,
                    ProofSource::Proof(&header, &[]),
                    ProofSource::Proof(&forged, &openings),
                );
                assert!(finished, "the forged record still has the complete transport");
                assert!(
                    !failures.is_empty(),
                    "digest at byte {start}, limb {limb} passes the rows"
                );
            }
        }
    }

    // Commit and open, then verify natively and in rows: an honest opening holds in both, and a tampered claim fails both at the terminal check.
    fn check_opening(mu: usize, log_inv_rate: u8, seed: u64) {
        let what = format!("mu {mu}, log_inv_rate {log_inv_rate}");
        let rate = Rate::new(log_inv_rate).expect("a supported rate");
        let mut rng = Rng::new(seed);
        let shape = StackShape {
            mu,
            n_lanes: N_LANES,
            hiding: false,
        };
        let q: Vec<F64> = (0..shape.committed_len()).map(|_| F64(rng.next_u64())).collect();
        let (slots, rings) = opening_claims(mu, &q, &mut rng);

        let mut ps = ProverState::new(&SessionId::new(LABEL), &0u64);
        let committed = Committed::new(&mut ps, &q, shape, rate).expect("a supported witness");
        committed
            .open(&mut ps, &q, &slots, &rings)
            .expect("the committed witness");
        let proof = ps.into_proof();
        let native = |slots: &[StackClaim], rings: &[RingSwitch], proof: &ProofTranscript| {
            let mut v = Recording::new(VerifierState::new(&SessionId::new(LABEL), &0u64, proof));
            let commitment = Commitment::read(&mut v, shape, rate).expect("a root");
            commitment.verify(&mut v, slots, rings)?;
            v.transcript()
                .check_eof()
                .expect("the native verifier reads the whole proof");
            Ok::<_, WhirError>(v.into_openings())
        };
        let openings = native(&slots, &rings, &proof).expect("the native verifier accepts");

        let rows = |slots: &[StackClaim], rings: &[RingSwitch], source: ProofSource<'_>| {
            opening_rows(shape, rate, slots, rings, source)
        };
        let (circuit, failures, finished) = rows(&slots, &rings, ProofSource::Proof(&proof, &openings));
        assert!(failures.is_empty(), "{what}: {failures:?}");
        assert!(finished, "{what}: the rows left part of the proof unread");
        assert!(
            circuit == rows(&slots, &rings, ProofSource::Shape).0,
            "{what}: the shape builds another circuit"
        );

        let terminal = |failures: &[Unsatisfied]| failures.iter().any(|f| f.scope().iter().any(|s| s == "terminal"));
        let refused = |slots: &[StackClaim], rings: &[RingSwitch]| {
            native(slots, rings, &proof).err() == Some(WhirError::TerminalMismatch)
                && terminal(&rows(slots, rings, ProofSource::Proof(&proof, &openings)).1)
        };
        for i in 0..slots.len() {
            let mut forged = slots.clone();
            match &mut forged[i] {
                StackClaim::Point { value, .. } | StackClaim::Strided { value, .. } => *value += F192::ONE,
            }
            assert!(
                refused(&forged, &rings),
                "{what}: a wrong value of point claim {i} passes"
            );
        }
        for ring in 0..rings.len() {
            for claim in 0..rings[ring].claims.len() {
                let mut forged = rings.clone();
                forged[ring].claims[claim].s_hat_v[7] += F192::ONE;
                assert!(
                    refused(&slots, &forged),
                    "{what}: a wrong slice of ring {ring} claim {claim} passes"
                );
            }
        }
        let mut forged = proof.clone();
        let mid = forged.narg.len() / 2;
        forged.narg[mid] ^= 1;
        assert!(
            !rows(&slots, &rings, ProofSource::Proof(&forged, &openings))
                .1
                .is_empty(),
            "{what}: a forged scalar passes"
        );
    }

    #[test]
    fn the_smallest_opening_holds_in_both_verifiers() {
        check_opening(crate::commitment::MIN_MU, 1, 1);
        check_opening(crate::commitment::MIN_MU, 2, 2);
    }

    #[test]
    fn a_larger_opening_holds_in_both_verifiers() {
        check_opening(20, 1, 3);
        check_opening(20, 2, 4);
    }
}
