//! Proving and verifying a run of the recursion machine: the pipeline of a leanVM proof, on the circuit's tables.
//!
//! - The stack commits the hash table's packed witness, then every present owned table's committed columns.
//! - The bus balances the slots' copy cycles.
//! - One batch proves every present table's summand at the bus's point, and flock proves every hash row.
//! - One opening settles the column claims and the packed witness's ring-switched claim.
//!
//! A table with no rows, other than the hash and public tables, is absent (`RecLayout`): neither side reads it.

use super::RecError;
use super::bus::{BusBlocks, TableResidual, TableSummand};
use super::circuit::{Assignment, Circuit, Limbs};
use super::fixed::FixedColumns;
use super::hash::{self, HashBatch};
use super::layout::RecLayout;
use super::table::Table;
use crate::bus::PublicColumns;
use crate::commitment::{Commitment, Committed, Rate, StackClaim};
use crate::constraints::{Columns, ConstraintError};
use crate::{constraints, stacking};
use fiat_shamir::arith::Verifier;
use fiat_shamir::{LengthPrefixed, ProofTranscript, ProverState, SessionId, VerifierState};
use flock::FlockError;
use flock::lincheck::MatrixClaim;
use flock::reduction;
use pcs::merkle::Openings;
use pcs::verifier::{OpeningVerifier, Recording};
use primitives::field::{F64, F192};
use std::mem::MaybeUninit;
use tracing::info_span;

/// The prover's stack and the hash table's ports by global column.
struct RecWitness {
    q: Vec<F64>,
    ports: Vec<(usize, Vec<F64>)>,
}

/// What proving or verifying runs of one circuit takes: the circuit, its layout and its fixed columns.
///
/// Building it checks that the circuit fits one commitment.
#[derive(Clone, Debug)]
pub(crate) struct CircuitKey {
    /// The circuit.
    circuit: Circuit,
    /// Its heights and every column's place in the stack.
    layout: RecLayout,
    /// The columns of its bus its wiring alone fixes.
    fixed: FixedColumns,
}

/// The bus and the constraint batch over the owned tables, which leave the column claims the opening settles.
pub(crate) struct TableArgument<'a> {
    layout: &'a RecLayout,
    blocks: BusBlocks,
}

impl RecWitness {
    /// The witness, and the hash table's batch, which the reduction consumes.
    fn build(layout: &RecLayout, a: &Assignment) -> (Self, HashBatch) {
        let mut q = Box::new_uninit_slice(layout.shape.committed_len());
        // SAFETY: the owned tables and hash batch fill every committed window before it is read.
        // The pad tail is zeroed.
        let mut windows = stacking::split_stack(unsafe { primitives::write_only(&mut q) }, &layout.placements);
        for &table in &layout.present {
            table.fill(a, &mut windows[RecLayout::columns(table)]);
        }

        let tau = layout.tau(Table::Hash);
        // A port is not in the stack: its values are a buffer of their own, written by the batch.
        let mut ports: Vec<Box<[MaybeUninit<F64>]>> =
            (0..hash::N_PORTS).map(|_| Box::new_uninit_slice(1 << tau)).collect();
        let batch = HashBatch::new(&a.hash, tau, windows[RecLayout::HASH_WITNESS], &mut ports);
        drop(windows);
        // SAFETY: the windows tile the stack up to its zeroed tail, and each was filled above.
        let q = unsafe { q.assume_init() }.into_vec();

        let ports_at = RecLayout::columns(Table::Hash).start;
        let ports = (ports.into_iter().enumerate())
            // SAFETY: the batch wrote every row of every port.
            .map(|(port, values)| (ports_at + port, unsafe { values.assume_init() }.into_vec()))
            .collect();
        (Self { q, ports }, batch)
    }

    /// One view per global column: a committed column's window, a port's own buffer.
    fn columns<'a>(&'a self, layout: &RecLayout) -> Vec<&'a [F64]> {
        let mut cols: Vec<&[F64]> = (layout.placements.iter())
            .map(|p| {
                p.window()
                    .map_or(&[][..], |w| &self.q[w.offset..w.offset + (1 << w.n_vars)])
            })
            .collect();
        for (i, buf) in &self.ports {
            cols[*i] = buf;
        }
        cols
    }
}

impl<'a> TableArgument<'a> {
    /// The argument over the given bus blocks.
    pub(crate) const fn new(layout: &'a RecLayout, blocks: BusBlocks) -> Self {
        Self { layout, blocks }
    }

    /// The argument of a circuit's fixed columns and its statement, the public rows reading the statement.
    fn of(fixed: &FixedColumns, statement: &[Limbs], layout: &'a RecLayout) -> Self {
        let public = fixed.public_values(statement);
        Self::new(layout, BusBlocks::new(fixed, public, layout))
    }

    /// Prove the bus, then every present owned table's summand at the bus's point.
    fn prove(&self, w: &RecWitness, ps: &mut ProverState) -> Vec<StackClaim> {
        let cols = w.columns(self.layout);
        let bus = info_span!("Prove bus").in_scope(|| self.blocks.prove(&cols, ps));
        let tables = info_span!("Prove constraints").in_scope(|| {
            let xi = ps.verifier_message();
            let present = &self.layout.present;
            let sums: Vec<F192> = (0..present.len())
                .map(|t| bus.sigmas[0][t] + xi * bus.sigmas[1][t])
                .collect();
            let table_cols = (present.iter())
                .map(|&t| Columns::K(cols[RecLayout::columns(t)].to_vec()))
                .collect();
            let airs = self.layout.airs(TableSummand::batch(present, &bus.forms, xi));
            constraints::prove(&airs, table_cols, &bus.point, &sums, ps)
        });
        self.layout.opening_claims(bus.claims, &tables)
    }

    /// Verify the bus, then the table sumcheck against what the bus says the tables owe.
    ///
    /// # Errors
    ///
    /// Returns the bus's or the table sumcheck's refusal.
    pub(crate) fn verify<V: Verifier + PublicColumns>(&self, v: &mut V) -> Result<Vec<StackClaim<V::E>>, RecError> {
        let bus = self.blocks.verify(v)?;
        let xi = v.verifier_message();
        let target = v.mul_add(xi, bus.totals[1], bus.totals[0]);
        let airs = self
            .layout
            .airs(TableResidual::batch(v, &self.layout.present, &bus.forms, xi));
        let tables = constraints::verify(v, &airs, &bus.point, target)?;
        let zero = v.zero();
        v.ensure_eq(tables.residual, zero, || {
            RecError::Constraint(ConstraintError::FinalMismatch)
        })?;
        Ok(self.layout.opening_claims(bus.claims, &tables.claims))
    }

    /// The verifier's core: the commitment, the hash rows' reduction, the bus and the tables, and the opening, then nothing left to read.
    ///
    /// It returns the hash rows' claim on their matrices, which whoever holds the circuit settles.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    pub(crate) fn verify_core<V: OpeningVerifier + PublicColumns>(
        &self,
        v: &mut V,
        rate: Rate,
    ) -> Result<MatrixClaim<V::E>, RecError> {
        let commitment = Commitment::read(v, self.layout.shape, rate)?;
        let batch = (hash::CIRCUIT.shape(), self.layout.tau(Table::Hash));
        let [replay] = <[_; 1]>::try_from(v.scope("flock", |v| reduction::verify(&[batch], v))?)
            .unwrap_or_else(|_| unreachable!("a batch of one circuit"));
        let slots = v.scope("bus and tables", |v| self.verify(v))?;
        let ring = self.layout.hash_window().ring(replay.claim);
        v.scope("opening", |v| commitment.verify(v, &slots, &[ring]))?;
        v.check_eof()?;
        Ok(replay.matrices)
    }
}

impl Circuit {
    /// The words a proof of the circuit commits: its committed columns at its heights.
    ///
    /// # Errors
    ///
    /// Returns an error if a table has more rows than its keys name, or the witness exceeds one commitment.
    pub fn committed_words(&self) -> Result<usize, RecError> {
        Ok(stacking::committed_len(&RecLayout::new(self)?.placements))
    }
}

impl CircuitKey {
    /// The key of a circuit: its layout at its heights, and its fixed columns.
    ///
    /// # Errors
    ///
    /// Returns an error if a table has more rows than its keys name, or the witness exceeds one commitment.
    pub(crate) fn new(circuit: Circuit) -> Result<Self, RecError> {
        let layout = RecLayout::new(&circuit)?;
        let fixed = FixedColumns::new(&circuit);
        Ok(Self { circuit, layout, fixed })
    }

    /// The circuit.
    pub(crate) const fn circuit(&self) -> &Circuit {
        &self.circuit
    }

    /// The circuit's fixed columns at its heights.
    pub(crate) const fn fixed(&self) -> &FixedColumns {
        &self.fixed
    }

    /// Prove that an assignment is a run of the circuit, at the given commitment rate.
    ///
    /// The transcript starts from a digest naming the circuit and absorbs the statement before any challenge.
    ///
    /// # Panics
    ///
    /// Panics if the assignment is not one of the circuit, or its bus does not balance.
    #[tracing::instrument(name = "Prove recursion", skip_all)]
    pub(crate) fn prove(&self, a: &Assignment, session: &SessionId, rate: Rate) -> ProofTranscript {
        let (circuit, layout) = (&self.circuit, &self.layout);
        assert_eq!(a.statement.len(), circuit.statement_len, "the assignment's statement");
        assert!(
            Table::ALL
                .iter()
                .all(|&t| a.wires.of(t).len() == circuit.classes.of(t).len()),
            "the assignment's rows are the circuit's"
        );
        let mut ps = ProverState::new(session, &LengthPrefixed(a.statement.as_flattened()));

        let (w, batch) = info_span!("Build witness").in_scope(|| RecWitness::build(layout, a));
        let committed = info_span!("Commit")
            .in_scope(|| Committed::new(&mut ps, &w.q, layout.shape, rate).expect("the witness matches its layout"));
        // The hash rows' reduction reads only the commitment, so it runs first and frees their batch before the bus.
        let ring = info_span!("Flock reduction").in_scope(|| batch.prove(layout, &w.q, &mut ps));
        let slots = TableArgument::of(&self.fixed, &a.statement, layout).prove(&w, &mut ps);

        let RecWitness { q, ports } = w;
        drop(ports);
        info_span!("PCS open").in_scope(|| {
            committed
                .open(&mut ps, &q, &slots, &[ring])
                .expect("opening uses the committed witness");
        });
        ps.into_proof()
    }

    /// Verify a proof of the circuit, returning every opening it authenticated.
    ///
    /// A recursive verifier of the proof hashes those openings rather than decoding the hints again.
    ///
    /// # Errors
    ///
    /// Returns the first check that refuses the proof.
    pub(crate) fn verify(
        &self,
        statement: &[Limbs],
        session: &SessionId,
        rate: Rate,
        proof: &ProofTranscript,
    ) -> Result<Vec<Openings>, RecError> {
        let instance = LengthPrefixed(statement.as_flattened());
        self.verify_after(statement, VerifierState::new(session, &instance, proof), rate)
    }

    /// Verify a proof over a transcript that has absorbed its instance.
    fn verify_after(
        &self,
        statement: &[Limbs],
        transcript: VerifierState<'_>,
        rate: Rate,
    ) -> Result<Vec<Openings>, RecError> {
        if statement.len() != self.circuit.statement_len {
            return Err(RecError::StatementLength {
                expected: self.circuit.statement_len,
                got: statement.len(),
            });
        }
        let mut v = Recording::new(transcript);
        let matrices = TableArgument::of(&self.fixed, statement, &self.layout).verify_core(&mut v, rate)?;
        matrices.check(hash::CIRCUIT.circuit()).map_err(FlockError::Lincheck)?;
        Ok(v.into_openings())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::{self, Rate};
    use crate::constraints::ConstraintError;
    use crate::rec::circuit::chains::{Planned, plan, step, tweak};
    use crate::rec::circuit::{Builder, Dw, Ew, Finished, Kw, PARAM_IV};
    use crate::rec::fixed::FixedColumn;
    use fiat_shamir::arith::Arith;
    use std::panic::AssertUnwindSafe;

    fn session() -> SessionId {
        SessionId::new(b"rec-proof-test")
    }

    fn key(circuit: &Circuit) -> CircuitKey {
        CircuitKey::new(circuit.clone()).expect("the circuit fits one commitment")
    }

    fn prove_run(circuit: &Circuit, a: &Assignment) -> ProofTranscript {
        key(circuit).prove(a, &session(), Rate::MIN)
    }

    fn verify_run(circuit: &Circuit, statement: &[Limbs], proof: &ProofTranscript) -> Result<(), RecError> {
        key(circuit).verify(statement, &session(), Rate::MIN, proof).map(drop)
    }

    // Verify a proof whose transcript absorbed `absorbed` as its instance, in place of the statement.
    fn verify_absorbing(
        circuit: &Circuit,
        statement: &[Limbs],
        absorbed: &[Limbs],
        proof: &ProofTranscript,
    ) -> Result<(), RecError> {
        let instance = LengthPrefixed(absorbed.as_flattened());
        let transcript = VerifierState::new(&session(), &instance, proof);
        key(circuit).verify_after(statement, transcript, Rate::MIN).map(drop)
    }

    // Wires of the every-kind circuit a test forges.
    struct Wires {
        // An `EMUL` output another row reads.
        product: Ew,
        // Bits 39 and 40 of a split word, 0 and 1, which nothing else reads.
        lone_bits: [Kw; 2],
    }

    // A circuit using every table and every slot kind.
    fn every_kind() -> (Circuit, Assignment, Wires) {
        kinds(true)
    }

    // The same circuit without its chain, so with no step or link rows.
    fn every_kind_but_chains() -> (Circuit, Assignment, Wires) {
        kinds(false)
    }

    fn kinds(chains: bool) -> (Circuit, Assignment, Wires) {
        let mut b = Builder::new();
        let x = b.free_e(F192::new(3, 5, 7));
        let one = b.one();
        let zero = b.zero();
        let y = b.e_const(F192::new(11, 13, 17));
        let product = b.mul_add(x, y, one);
        let scaled = b.mul_const(product, F192::from(F64(9)));
        let k = b.free_k(0xdead_beef);
        let r = b.mul_k_add(scaled, k, x);
        // A free wire in one slot only.
        let hint = b.free_e(F192::new(1, 2, 3));
        b.mul_add(hint, y, zero);

        // Two one-block hashes, then a Merkle path with a right and a left turn.
        let start = b.d_const([9, 8, 7, 6]);
        let observe = b.k_const(1);
        let (acc, _) = b.compress(start, r, observe);
        let squeeze = b.k_const(2);
        let (acc, challenge) = b.compress(acc, zero, squeeze);
        let w = b.free_k(0b1101_0110 | 1 << 40);
        let bits = b.split(w);
        let low = b.pack(&bits[..8]);
        b.eq_k_const(low, 0b1101_0110);
        let right = b.node(acc, bits[1], [1, 2, 3, 4]);
        let root = b.node(right, bits[0], [5, 6, 7, 8]);

        // A leaf's two blocks.
        let h = b.d_const(PARAM_IV);
        let m: [Kw; 8] = std::array::from_fn(|i| b.free_k(77 * i as u64 + 1));
        let first = b.leaf_block(h, m, 64, false);
        let words = b.d_to_k(root);
        let zero_k = b.k_const(0);
        let m2 = [words[0], words[1], words[2], words[3], zero_k, zero_k, zero_k, zero_k];
        let leaf = b.leaf_block(first, m2, 128, true);

        // Every cast, and equalities across tables.
        let limbs = b.e_to_k(challenge);
        let back = b.k_to_e(limbs);
        b.eq(back, challenge);
        let embedded = b.k_to_e1(k);
        let seven = b.e_const(F192::new(0, 7, 0));
        let zero = b.zero();
        let kk = b.mul_k_add(seven, k, zero);
        let kk_again = b.mul(seven, embedded);
        b.eq(kk, kk_again);
        let digest = b.k_to_d(words);
        b.eq(digest, root);
        let lo = b.k_to_e([words[0], words[1], zero_k]);
        let hi = b.k_to_e([words[2], words[3], zero_k]);
        let halves: Dw = b.halves_to_d(lo, hi);
        b.eq(halves, root);

        b.expose(r);
        b.expose(leaf);
        b.expose(low);
        if chains {
            b.emit_chains(&plan(&[5]));
        }
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let wires = Wires {
            product,
            lone_bits: [bits[39], bits[40]],
        };
        (circuit, a, wires)
    }

    #[test]
    fn every_table_and_slot_kind_proves_and_verifies() {
        let (circuit, a, _) = every_kind();
        let counts = circuit.row_counts();
        assert!(counts.values().all(|&n| n > 0), "{counts:?}");
        let proof = prove_run(&circuit, &a);
        assert_eq!(verify_run(&circuit, &a.statement, &proof), Ok(()));
    }

    #[test]
    fn a_changed_statement_word_is_refused() {
        let (circuit, a, _) = every_kind();
        let proof = prove_run(&circuit, &a);
        for (i, limb) in [(0, 1), (1, 3), (2, 0)] {
            let mut statement = a.statement.clone();
            statement[i][limb] ^= 1;
            // As the instance, the word changes every challenge, and the first stage, flock, refuses it.
            let refused = verify_run(&circuit, &statement, &proof);
            assert!(
                matches!(refused, Err(RecError::Flock(_))),
                "word {i} limb {limb}: {refused:?}"
            );
            // Under the honest instance, what the bus says the public rows owe refuses it.
            let refused = verify_absorbing(&circuit, &statement, &a.statement, &proof);
            assert!(
                matches!(refused, Err(RecError::Bus(_) | RecError::Constraint(_))),
                "word {i} limb {limb}: {refused:?}"
            );
        }
    }

    // The bus binds a statement word through `sum_j w_j·delta_j` at one point, `w_j` in `E` and `delta_j` in `K`.
    // Four limbs leave a kernel, so only the transcript's seed can refuse a word moved along it.
    #[test]
    fn a_statement_moved_along_the_bus_kernel_is_refused() {
        let mut b = Builder::new();
        let w: [Kw; 4] = std::array::from_fn(|i| b.free_k(10 + i as u64));
        let d = b.k_to_d(w);
        b.expose(d);
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let proof = prove_run(&circuit, &a);

        // Replay the honest verifier up to the bus, past the hash rows' reduction, to read the fingerprint weights of the limbs.
        let layout = RecLayout::new(&circuit).unwrap();
        let mut vs = VerifierState::new(&session(), &LengthPrefixed(a.statement.as_flattened()), &proof);
        Commitment::read(&mut vs, layout.shape, Rate::MIN).unwrap();
        reduction::verify(&[(hash::CIRCUIT.shape(), layout.tau(Table::Hash))], &mut vs).unwrap();
        let fixed = FixedColumns::new(&circuit);
        let blocks = BusBlocks::new(&fixed, fixed.public_values(&a.statement), &layout);
        let bus = blocks.verify(&mut vs).unwrap();
        let wt: Vec<F192> = (1..5).map(|j| bus.weights[j]).collect();

        // Solve `sum_j wt_j·delta_j = 0` over `K` with `delta_3 = 1`: three `K`-linear equations, by elimination.
        let limb = |x: F192, r: usize| F64([x.c0, x.c1, x.c2][r]);
        let mut m: Vec<[F64; 4]> = (0..3).map(|r| std::array::from_fn(|j| limb(wt[j], r))).collect();
        for c in 0..3 {
            let p = (c..3).find(|&r| !m[r][c].is_zero()).expect("a pivot");
            m.swap(c, p);
            let inv = m[c][c].inv();
            m[c] = m[c].map(|v| v * inv);
            for r in (0..3).filter(|&r| r != c) {
                let f = m[r][c];
                m[r] = std::array::from_fn(|k| m[r][k] + m[c][k] * f);
            }
        }
        let delta = [m[0][3], m[1][3], m[2][3], F64(1)];
        assert!(
            (0..4)
                .fold(F192::ZERO, |acc, j| acc + wt[j].mul_base(delta[j]))
                .is_zero()
        );
        let mut forged = a.statement.clone();
        for (l, dl) in forged[0].iter_mut().zip(delta) {
            *l ^= dl.0;
        }

        // Under the honest instance the bus accepts the forged words; with them as the instance, the proof is refused
        // at its first stage.
        assert!(verify_absorbing(&circuit, &forged, &a.statement, &proof).is_ok());
        assert!(matches!(verify_run(&circuit, &forged, &proof), Err(RecError::Flock(_))));
    }

    // A wire in one slot balances whatever it holds, so what refuses a non-Boolean bit is its table's identities.
    // The word is `sum_i x^i·b_i` in `K`: `b_39 = x` and `b_40 = 0` keep the word, so only `b_39^2 = b_39` fails.
    #[test]
    fn a_non_boolean_bit_is_refused() {
        let (circuit, mut a, wires) = every_kind();
        let [b39, b40] = wires.lone_bits.map(|w| w.0 as usize);
        assert_eq!((a.values[b39][0], a.values[b40][0]), (0, 1));
        a.values[b39][0] = 2;
        a.values[b40][0] = 0;
        let proof = prove_run(&circuit, &a);
        assert_eq!(
            verify_run(&circuit, &a.statement, &proof),
            Err(RecError::Constraint(ConstraintError::FinalMismatch))
        );
    }

    // An `EMUL` output another row reads differently leaves its copy cycle unbalanced, which no prover states.
    #[test]
    fn a_forged_product_unbalances_the_bus() {
        let (circuit, mut a, wires) = every_kind();
        a.values[wires.product.0 as usize][0] ^= 1;
        let refused = std::panic::catch_unwind(AssertUnwindSafe(|| prove_run(&circuit, &a)))
            .expect_err("an unbalanced bus was proven");
        let message = refused.downcast_ref::<String>().map_or("", String::as_str);
        assert!(message.contains("the bus needs the two products to agree"), "{message}");
    }

    // The verifier's circuit holds two wires equal that the honest run does not: the copy cycles refuse it.
    #[test]
    fn an_equality_the_run_breaks_is_refused_by_the_verifier() {
        let mut b = Builder::new();
        let x = b.free_e(F192::new(3, 5, 7));
        let y = b.free_e(F192::new(4, 5, 7));
        let c = b.e_const(F192::new(2, 0, 1));
        let p = b.mul(x, c);
        let q = b.mul(y, c);
        b.expose(p);
        b.expose(q);
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let proof = prove_run(&circuit, &a);
        assert_eq!(verify_run(&circuit, &a.statement, &proof), Ok(()));

        let mut merged = circuit;
        let emul = merged.classes.of(Table::Emul);
        let (cx, cy) = (emul[0], emul[4]);
        assert_ne!(cx, cy);
        merged.classes = merged.classes.map(|c| if c == cx { cy } else { c });
        assert_eq!(
            verify_run(&merged, &a.statement, &proof),
            Err(RecError::Constraint(ConstraintError::FinalMismatch))
        );
    }

    // Every table a few rows short of or past a power of two: the padding rows carry nothing.
    #[test]
    fn padding_rows_are_inert() {
        let mut b = Builder::new();
        let mut e = b.free_e(F192::new(2, 3, 4));
        let mut acc = b.d_const([1, 2, 3, 4]);
        let ds = b.k_const(1);
        for i in 0..3u64 {
            let c = b.e_const(F192::new(i + 5, 1, 0));
            e = b.mul_add(e, c, e);
            e = b.mul_const(e, F192::from(F64(i + 3)));
            let w = b.free_k(i * 0x1234_5678);
            b.split(w);
            b.d_to_k(acc);
        }
        for i in 0..61u64 {
            acc = if i % 2 == 0 {
                b.compress(acc, e, ds).0
            } else {
                let m: [Kw; 8] = std::array::from_fn(|j| b.free_k(i * 8 + j as u64));
                b.leaf_block(acc, m, 64 * (i + 1), i % 4 == 3)
            };
        }
        b.emit_chains(&plan(&[4, 7, 5]));
        b.expose(acc);
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let counts = circuit.row_counts();
        assert_eq!(counts[Table::Hash], 66);
        assert!(counts.values().all(|&n| n > 1 && !n.is_power_of_two()), "{counts:?}");
        let proof = prove_run(&circuit, &a);
        assert_eq!(verify_run(&circuit, &a.statement, &proof), Ok(()));
    }

    fn chains(rows: &[Planned]) -> Finished {
        let mut b = Builder::new();
        b.emit_chains(rows);
        b.finish()
    }

    // Chains of every digit's kind, one of no step and one of seven, prove and verify.
    #[test]
    fn chains_on_the_dynamic_bus_prove_and_verify() {
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = chains(&plan(&[0, 3, 7, 6]));
        assert!(failures.is_empty(), "{failures:?}");
        let counts = circuit.row_counts();
        assert_eq!((counts[Table::Step], counts[Table::Link]), (12, 4));
        let proof = prove_run(&circuit, &a);
        assert_eq!(verify_run(&circuit, &a.statement, &proof), Ok(()));
    }

    // Rows whose dynamic tuples do not balance: the builder reports it, and the prover cannot prove the bus.
    fn assert_refused(rows: &[Planned], what: &str) {
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = chains(rows);
        assert!(
            failures.iter().any(|f| f.check() == "the dynamic tuples balance"),
            "{what}: {failures:?}"
        );
        let refused = std::panic::catch_unwind(AssertUnwindSafe(|| prove_run(&circuit, &a)))
            .expect_err(&format!("{what} was proven"));
        let message = refused.downcast_ref::<String>().map_or("", String::as_str);
        assert!(
            message.contains("the bus needs the two products to agree"),
            "{what}: {message}"
        );
    }

    // Row `i`'s input, a step's.
    fn input(rows: &mut [Planned], i: usize) -> &mut [u64; 2] {
        match &mut rows[i] {
            Planned::Step { v, .. } => v,
            Planned::Link { .. } => unreachable!("row {i} is a step"),
        }
    }

    #[test]
    fn tampered_chains_are_refused() {
        // Chain 0 steps from position 2 (rows 0 to 4, link 5), chain 1 from position 5 (rows 6 and 7, link 8).
        let honest = plan(&[2, 5]);

        // The tuples are a multiset: the rows' order is free.
        let mut rows = honest.clone();
        rows.swap(2, 7);
        assert!(chains(&rows).failures.is_empty());

        let mut rows = honest.clone();
        input(&mut rows, 2)[1] ^= 1;
        assert_refused(&rows, "a step with a wrong input");

        let mut rows = honest.clone();
        let (v1, v2) = (*input(&mut rows, 1), *input(&mut rows, 2));
        *input(&mut rows, 1) = v2;
        *input(&mut rows, 2) = v1;
        assert_refused(&rows, "two steps' inputs swapped");

        let mut rows = honest.clone();
        rows.remove(3);
        assert_refused(&rows, "a missing step");

        let mut rows = honest.clone();
        let Planned::Link { end, .. } = &mut rows[8] else {
            unreachable!("row 8 is chain 1's link")
        };
        end[0] ^= 1;
        assert_refused(&rows, "a link's end not the chain's");

        // Eight steps of chain 50, past the 42 a signature has, from position 0 round to position 0: the last
        // pushes at the first's key, and only an output equal to the first input would close the cycle.
        let mut rows = honest;
        let mut v = [5, 6];
        for s in 0..8 {
            rows.push(Planned::Step { tweak: tweak(50, s), v });
            v = step(tweak(50, s), v);
        }
        assert_refused(&rows, "a cycle of steps past the chains");
    }

    // A circuit whose last step is a padding row, the witness filling it with that step: an honest prover cannot
    // balance the bus, the padding row's tuples being inactive, and a proof that sets the row active is refused.
    #[test]
    fn a_padding_row_carrying_a_tuple_is_refused() {
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = chains(&plan(&[3]));
        assert!(failures.is_empty(), "{failures:?}");
        assert_eq!(circuit.row_counts()[Table::Step], 4);
        let mut short = circuit.clone();
        short.classes.pop_row(Table::Step);
        let taus = circuit.heights();
        assert_eq!(short.heights(), taus);
        // The honest circuit's key, its fixed columns the short circuit's.
        let forged = |fixed: FixedColumns| CircuitKey { fixed, ..key(&circuit) };
        let fixed = FixedColumns::new(&short);
        let refused = std::panic::catch_unwind(AssertUnwindSafe(|| {
            forged(fixed.clone()).prove(&a, &session(), Rate::MIN)
        }))
        .expect_err("an inactive tuple balanced an active one");
        let message = refused.downcast_ref::<String>().map_or("", String::as_str);
        assert!(message.contains("the bus needs the two products to agree"), "{message}");

        let mut active = fixed;
        active.set(FixedColumn::Active(Table::Step), 3, F64::ONE);
        let proof = forged(active).prove(&a, &session(), Rate::MIN);
        assert!(verify_run(&short, &a.statement, &proof).is_err());
    }

    #[test]
    fn a_circuit_past_one_commitment_is_an_error() {
        let (mut circuit, ..) = every_kind();
        circuit.floor[Table::Emul] = Some(commitment::MAX_MU);
        let too_long = |e: &RecError| matches!(e, RecError::TooLong { mu } if *mu > commitment::MAX_MU);
        assert!(CircuitKey::new(circuit.clone()).is_err_and(|e| too_long(&e)));

        circuit.floor[Table::Emul] = None;
        circuit.floor[Table::Pub] = Some(RecLayout::MAX_TAU + 1);
        let too_many = Err(RecError::TooManyRows {
            table: Table::Pub,
            tau: RecLayout::MAX_TAU + 1,
        });
        assert_eq!(CircuitKey::new(circuit).map(drop), too_many);
    }

    // A table with no rows is absent: nothing of it is committed and the verifier reads nothing of it. The heights fix
    // which tables a proof has, so a proof with the table is refused where the verifier expects none, and the other way.
    #[test]
    fn the_heights_fix_the_absent_tables() {
        let (circuit, a, _) = every_kind_but_chains();
        let counts = circuit.row_counts();
        assert_eq!((counts[Table::Step], counts[Table::Link]), (0, 0));
        let layout = RecLayout::new(&circuit).unwrap();
        assert!(!layout.present.contains(&Table::Step) && !layout.present.contains(&Table::Link));
        let proof = prove_run(&circuit, &a);
        assert_eq!(verify_run(&circuit, &a.statement, &proof), Ok(()));

        let mut padded = circuit.clone();
        padded.floor[Table::Step] = Some(0);
        padded.floor[Table::Link] = Some(0);
        assert!(padded.committed_words().unwrap() > circuit.committed_words().unwrap());
        let padded_proof = prove_run(&padded, &a);
        assert_eq!(verify_run(&padded, &a.statement, &padded_proof), Ok(()));
        assert!(verify_run(&circuit, &a.statement, &padded_proof).is_err());
        assert!(verify_run(&padded, &a.statement, &proof).is_err());
    }
}
