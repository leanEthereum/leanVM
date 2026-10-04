//! Proving and verifying a run of the recursion machine: the pipeline of a leanVM proof, on the circuit's tables.
//!
//! - The stack commits the hash table's packed witness, then every owned table's committed columns.
//! - The bus balances the slots' copy cycles.
//! - One batch proves every table's summand at the bus's point, and flock proves every hash row.
//! - One opening settles the column claims and the packed witness's ring-switched claim.

use super::RecError;
use super::bus::{BusBlocks, TableResidual, TableSummand};
use super::circuit::{Assignment, Circuit, Compression, Limbs, chain};
use super::fixed::FixedColumns;
use super::layout::RecLayout;
use super::table::{HashFlock, Table};
use crate::arith::Verifier;
use crate::constraints::{Columns, ConstraintError};
use crate::pcs::{Rate, RingSwitchOpen, StackClaim};
use crate::{constraints, pcs, witness};
use fiat_shamir::transcript::{Challenger, Proof, ProverState, RawProof, VerifierState};
use flock::reduction::SliceClaim;
use primitives::field::{F64, F192};
use zk_alloc::ArenaVec;

/// The transcript's public input for a statement: the hash of its words' limbs, in order.
pub fn statement_seed(statement: &[Limbs]) -> [F64; 4] {
    let limbs: Vec<u64> = statement.iter().flatten().copied().collect();
    chain(&limbs).map(F64)
}

/// The hash table's flock batch, one instance per row.
struct HashBatch {
    tau: usize,
    z: ArenaVec<u64>,
    a: ArenaVec<u64>,
    b: ArenaVec<u64>,
    z_lincheck: ArenaVec<u8>,
}

/// The prover's stack, the hash table's ports by global column, and the hash table's batch.
struct RecWitness {
    q: ArenaVec<F64>,
    ports: Vec<(usize, ArenaVec<F64>)>,
    batch: HashBatch,
}

/// The bus and the constraint batch over the owned tables, which leave the column claims the opening settles.
pub(crate) struct TableArgument<'a> {
    layout: &'a RecLayout,
    blocks: BusBlocks,
}

impl HashBatch {
    /// Every hash row's packed witness, at the hash table's height.
    fn build(hash: &[Compression], tau: usize) -> Self {
        let (z, a, b, z_lincheck) =
            HashFlock::circuit().generate_witness_with(hash, &Compression::PADDING, tau, |row, z, az, bz| {
                crate::rv::circuits::blake2s_witness(row.inputs(), z, az, bz);
            });
        Self {
            tau,
            z,
            a,
            b,
            z_lincheck,
        }
    }

    /// Prove every hash row: zerocheck, then lincheck, to one ring-switched claim on the packed witness.
    fn prove(self, layout: &RecLayout, ps: &mut ProverState) -> RingSwitchOpen {
        let block = HashFlock::circuit().block();
        let window = layout.hash_window();
        let stage = block.prove_zerocheck(self.tau, &self.z, &self.a, &self.b, ps);
        let reduced = block.prove_lincheck(self.tau, stage, &self.z_lincheck, ps);
        flock::reduction::ring_switch_open(window.n_vars, window.offset, &reduced)
    }

    /// The verifier's replay of the hash rows' reduction, to the claim on the packed witness.
    ///
    /// The rows' matrices are settled here, against the circuit.
    fn verify(layout: &RecLayout, vs: &mut VerifierState) -> Result<SliceClaim, RecError> {
        let replay = HashFlock::circuit().block().verify(layout.tau(Table::Hash), vs)?;
        Ok(replay.claim)
    }
}

impl RecWitness {
    fn build(layout: &RecLayout, a: &Assignment) -> Self {
        // SAFETY: `split_stack` zeroes the pad tail; every committed window is written below: each owned table's
        // committed columns by its fill, and the packed witness from its batch.
        let mut q = unsafe { witness::alloc_stack(layout.shape) };
        let ports_at = RecLayout::columns(Table::Hash).start;
        // SAFETY: each port's buffer is written in full from the batch below.
        let mut ports: Vec<(usize, ArenaVec<F64>)> = (0..HashFlock::N_PORTS)
            .map(|c| {
                (ports_at + c, unsafe {
                    ArenaVec::uninitialized(1 << layout.tau(Table::Hash))
                })
            })
            .collect();
        let mut windows = witness::split_stack(&mut q, &layout.placements);
        for (i, buf) in &mut ports {
            windows[*i] = buf;
        }
        for table in Table::OWNED {
            table.fill(a, &mut windows[RecLayout::columns(table)]);
        }

        let batch = HashBatch::build(&a.hash, layout.tau(Table::Hash));
        parallel::chunks_mut_zip(windows[RecLayout::HASH_WITNESS], &batch.z, 1 << 16, |_, dst, src| {
            for (d, &s) in dst.iter_mut().zip(src) {
                *d = F64(s);
            }
        });
        let stride_log = HashFlock::stride_log();
        for port in 0..HashFlock::N_PORTS {
            for (j, cell) in windows[ports_at + port].iter_mut().enumerate() {
                *cell = F64(batch.z[(j << stride_log) + port]);
            }
        }
        drop(windows);
        Self { q, ports, batch }
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

    /// The argument of a circuit and its statement, the public rows reading the statement.
    fn of(circuit: &Circuit, statement: &[Limbs], layout: &'a RecLayout) -> Self {
        let fixed = FixedColumns::of(circuit, &layout.taus);
        let public = fixed.public_values(statement);
        Self::new(layout, BusBlocks::new(&fixed, public, layout))
    }

    /// Prove the bus, then every owned table's summand at the bus's point.
    fn prove(&self, w: &RecWitness, ps: &mut ProverState) -> Vec<StackClaim> {
        let cols = w.columns(self.layout);
        let bus = crate::stage!("Prove bus", || self.blocks.prove(&cols, ps));
        let tables = crate::stage!("Prove constraints", || {
            let xi = ps.sample();
            let sums: Vec<F192> = (0..Table::OWNED.len())
                .map(|t| bus.sigmas[0][t] + xi * bus.sigmas[1][t])
                .collect();
            let table_cols = (Table::OWNED.into_iter())
                .map(|t| Columns::K(cols[RecLayout::columns(t)].to_vec()))
                .collect();
            let airs = self.layout.airs(TableSummand::batch(&bus.forms, xi));
            constraints::prove(&airs, table_cols, &bus.point, &sums, ps)
        });
        self.layout.opening_claims(bus.claims, &tables)
    }

    /// Verify the bus, then the table sumcheck against what the bus says the tables owe.
    ///
    /// # Errors
    ///
    /// Returns the bus's or the table sumcheck's refusal.
    pub(crate) fn verify<V: Verifier>(&self, v: &mut V) -> Result<Vec<StackClaim<V::E>>, RecError> {
        let bus = self.blocks.verify(v)?;
        let xi = v.sample();
        let target = v.mul_add(xi, bus.totals[1], bus.totals[0]);
        let airs = self.layout.airs(TableResidual::batch(v, &bus.forms, xi));
        let tables = constraints::verify(v, &airs, &bus.point, target)?;
        let zero = v.zero();
        v.ensure_eq(tables.residual, zero, || {
            RecError::Constraint(ConstraintError::FinalMismatch)
        })?;
        Ok(self.layout.opening_claims(bus.claims, &tables.claims))
    }
}

impl Circuit {
    /// The words a proof of the circuit commits: its committed columns at its heights.
    ///
    /// # Errors
    ///
    /// Returns an error if a table has more rows than its keys name, or the witness exceeds one commitment.
    pub fn committed_words(&self) -> Result<usize, RecError> {
        Ok(witness::committed_len(&RecLayout::new(self)?.placements))
    }

    /// Prove that an assignment is a run of the circuit, at the given commitment rate.
    ///
    /// The transcript starts from a digest naming the circuit and absorbs the statement before any challenge.
    ///
    /// # Errors
    ///
    /// Returns an error if a table has more rows than its keys name, or the witness exceeds one commitment.
    ///
    /// # Panics
    ///
    /// Panics if the assignment is not one of the circuit, or its bus does not balance.
    #[tracing::instrument(name = "Prove recursion", skip_all)]
    pub fn prove(&self, a: &Assignment, iv: [F64; 4], rate: Rate) -> Result<Proof, RecError> {
        assert_eq!(a.statement.len(), self.statement_len, "the assignment's statement");
        assert!(
            Table::ALL
                .iter()
                .all(|&t| a.wires.of(t).len() == self.classes.of(t).len()),
            "the assignment's rows are the circuit's"
        );
        let layout = RecLayout::new(self)?;
        let _phase = zk_alloc::enter_phase();
        let log_inv_rate = rate.log_inv_rate().into();
        let mut ps = ProverState::new(iv, statement_seed(&a.statement));

        let w = crate::stage!("Build witness", || RecWitness::build(&layout, a));
        let committed = crate::stage!("Commit", || pcs::commit(&mut ps, &w.q, layout.shape, log_inv_rate));
        let slots = TableArgument::of(self, &a.statement, &layout).prove(&w, &mut ps);

        let RecWitness { q, ports, batch } = w;
        drop(ports);
        let ring = crate::stage!("Flock reduction", || batch.prove(&layout, &mut ps));
        crate::stage!("PCS open", || pcs::open(&mut ps, &committed, &q, &slots, &[ring]));
        Ok(ps.into_proof())
    }

    /// Verify a proof that the circuit has a run exposing the statement, at the given commitment rate.
    ///
    /// # Errors
    ///
    /// Returns the first check that refuses the proof.
    pub fn verify(&self, statement: &[Limbs], iv: [F64; 4], rate: Rate, proof: &Proof) -> Result<(), RecError> {
        self.verify_to_raw(statement, iv, rate, proof).map(|_| ())
    }

    /// Verify a proof, returning it as its verifier read it, every Merkle path written out.
    ///
    /// That is what a recursive verifier replays.
    ///
    /// # Errors
    ///
    /// Returns the first check that refuses the proof.
    pub fn verify_to_raw(
        &self,
        statement: &[Limbs],
        iv: [F64; 4],
        rate: Rate,
        proof: &Proof,
    ) -> Result<RawProof, RecError> {
        self.verify_seeded(statement, iv, statement_seed(statement), rate, proof)
    }

    /// Verify a proof whose transcript absorbed the given public input in place of the statement.
    fn verify_seeded(
        &self,
        statement: &[Limbs],
        iv: [F64; 4],
        public_input: [F64; 4],
        rate: Rate,
        proof: &Proof,
    ) -> Result<RawProof, RecError> {
        if statement.len() != self.statement_len {
            return Err(RecError::StatementLength {
                expected: self.statement_len,
                got: statement.len(),
            });
        }
        let layout = RecLayout::new(self)?;
        let mut vs = VerifierState::new(iv, proof, public_input);
        let root = pcs::read_commitment(&mut vs)?;
        let slots = TableArgument::of(self, statement, &layout).verify(&mut vs)?;
        let hash_claim = HashBatch::verify(&layout, &mut vs)?;
        let window = layout.hash_window();
        let ring = flock::reduction::ring_switch_verify(window.n_vars, window.offset, &hash_claim);
        pcs::verify(
            &mut vs,
            &slots,
            &[ring],
            layout.shape,
            rate.log_inv_rate().into(),
            &root,
        )?;
        vs.finish()?;
        Ok(vs.into_raw_proof())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::ConstraintError;
    use crate::leaf::BusError;
    use crate::pcs::Rate;
    use crate::rec::circuit::{Builder, Dw, Ew, Finished, Kw, PARAM_IV};
    use fiat_shamir::{DS_OBSERVE, DS_SQUEEZE};
    use std::panic::AssertUnwindSafe;

    const IV: [F64; 4] = [F64(1), F64(2), F64(3), F64(4)];

    fn prove_run(circuit: &Circuit, a: &Assignment) -> Proof {
        circuit
            .prove(a, IV, Rate::MIN)
            .expect("the circuit fits one commitment")
    }

    fn verify_run(circuit: &Circuit, statement: &[Limbs], proof: &Proof) -> Result<(), RecError> {
        circuit.verify(statement, IV, Rate::MIN, proof)
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

        // Two transcript steps, then a Merkle path with a right and a left turn.
        let start = b.d_const([9, 8, 7, 6]);
        let observe = b.k_const(DS_OBSERVE.0);
        let (acc, _) = b.compress(start, r, observe);
        let squeeze = b.k_const(DS_SQUEEZE.0);
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
        b.eq_e(back, challenge);
        let embedded = b.k_to_e1(k);
        let seven = b.e_const(F192::new(0, 7, 0));
        let kk = b.mul_k(seven, k);
        let kk_again = b.mul(seven, embedded);
        b.eq_e(kk, kk_again);
        let digest = b.k_to_d(words);
        b.eq_d(digest, root);
        let lo = b.k_to_e([words[0], words[1], zero_k]);
        let hi = b.k_to_e([words[2], words[3], zero_k]);
        let halves: Dw = b.halves_to_d(lo, hi);
        b.eq_d(halves, root);

        b.expose_e(r);
        b.expose_d(leaf);
        b.expose_k(low);
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
        assert!(counts.iter().all(|&n| n > 0), "{counts:?}");
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
            let refused = verify_run(&circuit, &statement, &proof);
            assert!(
                matches!(refused, Err(RecError::Bus(_))),
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
        b.expose_d(d);
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let proof = prove_run(&circuit, &a);
        let seed = statement_seed(&a.statement);

        // Replay the honest verifier up to the bus to read the fingerprint weights of the limbs.
        let layout = RecLayout::new(&circuit).unwrap();
        let mut vs = VerifierState::new(IV, &proof, seed);
        pcs::read_commitment(&mut vs).unwrap();
        let fixed = FixedColumns::of(&circuit, &layout.taus);
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
        let mut forged = a.statement;
        for (l, dl) in forged[0].iter_mut().zip(delta) {
            *l ^= dl.0;
        }

        // Under the honest seed the bus accepts the forged words; seeded with them, the proof is refused.
        assert!(circuit.verify_seeded(&forged, IV, seed, Rate::MIN, &proof).is_ok());
        assert!(matches!(
            verify_run(&circuit, &forged, &proof),
            Err(RecError::Bus(BusError::Gkr(_)))
        ));
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
        b.expose_e(p);
        b.expose_e(q);
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
        let ds = b.k_const(DS_OBSERVE.0);
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
        b.expose_d(acc);
        let Finished {
            circuit,
            assignment: a,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let counts = circuit.row_counts();
        assert_eq!(counts[Table::Hash as usize], 61);
        assert!(counts.iter().all(|&n| n > 1 && !n.is_power_of_two()), "{counts:?}");
        let proof = prove_run(&circuit, &a);
        assert_eq!(verify_run(&circuit, &a.statement, &proof), Ok(()));
    }

    #[test]
    fn a_circuit_past_one_commitment_is_an_error() {
        let (mut circuit, a, _) = every_kind();
        let proof = prove_run(&circuit, &a);
        circuit.floor[Table::Emul as usize] = pcs::MAX_MU;
        let too_long = |e: &RecError| matches!(e, RecError::TooLong { mu } if *mu > pcs::MAX_MU);
        assert!(circuit.prove(&a, IV, Rate::MIN).is_err_and(|e| too_long(&e)));
        assert!(verify_run(&circuit, &a.statement, &proof).is_err_and(|e| too_long(&e)));

        circuit.floor[Table::Emul as usize] = 0;
        circuit.floor[Table::Pub as usize] = RecLayout::MAX_TAU + 1;
        let too_many = Err(RecError::TooManyRows {
            table: Table::Pub,
            tau: RecLayout::MAX_TAU + 1,
        });
        assert_eq!(circuit.prove(&a, IV, Rate::MIN).map(|_| ()), too_many);
        assert_eq!(verify_run(&circuit, &a.statement, &proof), too_many);
    }
}
