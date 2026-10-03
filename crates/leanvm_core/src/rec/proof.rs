//! Proving and verifying a run of the recursion machine: the same pipeline as `cpu::Program`, on the circuit's
//! tables.
//!
//! The stack commits the `Hash` table's packed witness, then every owned table's committed columns. The bus
//! balances the slots' copy cycles, one batch proves every table's summand at the bus's point, flock proves
//! every hash row, and one opening settles the column claims and the packed witness's ring-switched claim.

use super::circuit::{Assignment, Circuit, Limbs, N_TABLES, Table};
use super::machine::{self, N_OWNED};
use crate::constraints::{self, Air, Claims, Columns};
use crate::leaf::{self, ColumnClaim};
use crate::pcs;
use crate::witness::{self, Placement, Source, StackShape, Window};
use fiat_shamir::transcript::{Challenger, Proof, ProverState, RawProof, VerifierState};
use primitives::field::{F64, F192};
use zk_alloc::ArenaVec;

/// The global column of the `Hash` table's packed witness, the one committed column before the owned tables'.
pub const Q_COLUMN: usize = 0;

/// Each owned table's first global column and its number of columns, in table order after the packed witness.
pub const fn spans() -> [(usize, usize); N_OWNED] {
    let mut spans = [(0, 0); N_OWNED];
    let mut next = Q_COLUMN + 1;
    let mut t = 0;
    while t < N_OWNED {
        spans[t] = (next, machine::n_cols(Table::ALL[t]));
        next += spans[t].1;
        t += 1;
    }
    spans
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RecError {
    #[error("the statement has {got} words, and the circuit exposes {expected}")]
    StatementLength { expected: usize, got: usize },
    #[error("log_inv_rate {0} is not a supported rate")]
    Rate(usize),
    #[error("the witness has 2^{mu} words, outside 2^{min}..=2^{max}", min = pcs::MIN_MU, max = pcs::MAX_MU)]
    WitnessSize { mu: usize },
    #[error(transparent)]
    Transcript(#[from] fiat_shamir::transcript::Error),
    #[error(transparent)]
    Bus(#[from] leaf::Error),
    #[error(transparent)]
    Constraint(#[from] constraints::Error),
    #[error(transparent)]
    Flock(#[from] flock::verifier::VerifyError),
    #[error(transparent)]
    Open(#[from] ::pcs::whir::VerifyError),
}

/// Each table's height as a base-two logarithm: the least power of two holding its rows, at flock's floor for
/// the `Hash` table, and at least the circuit's floor.
pub fn heights(circuit: &Circuit) -> [usize; N_TABLES] {
    let counts = circuit.row_counts();
    std::array::from_fn(|t| machine::log_rows(Table::ALL[t], counts[t]).max(circuit.floor[t]))
}

/// What both sides derive from the circuit alone: each table's height and where every column sits in the
/// stack.
#[derive(Clone, Debug)]
pub struct Layout {
    /// Each table's base-two logarithm of rows, `Pub` included.
    pub taus: [usize; N_TABLES],
    pub placements: Vec<Placement>,
    pub shape: StackShape,
}

impl Layout {
    pub fn new(circuit: &Circuit) -> Self {
        Self::from_taus(heights(circuit))
    }

    /// The layout of a circuit whose tables have these heights.
    pub fn from_taus(taus: [usize; N_TABLES]) -> Self {
        let stride_log = machine::hash_stride_log();
        let mut sources = vec![Source::Committed(taus[Table::Hash as usize] + stride_log)];
        for (t, &(base, n)) in spans().iter().enumerate() {
            debug_assert_eq!(sources.len(), base);
            let table = Table::ALL[t];
            sources.extend((0..n).map(|c| {
                if c < machine::n_ports(table) {
                    Source::Port {
                        column: Q_COLUMN,
                        port: c,
                        stride_log,
                    }
                } else {
                    Source::Committed(taus[t])
                }
            }));
        }
        let (placements, shape) = witness::placements_of(&sources);
        Self {
            taus,
            placements,
            shape,
        }
    }

    pub fn window(&self, col: usize) -> Window {
        self.placements[col].window().expect("a committed column")
    }

    /// The constraint batch's airs, one per owned table.
    pub(crate) fn airs(&self, forms: &[Vec<leaf::BusForm>; 2], xi: F192) -> Vec<Air<machine::Summand>> {
        machine::summands(forms, xi)
            .into_iter()
            .enumerate()
            .map(|(t, summand)| Air {
                tau: self.taus[t],
                n_cols: machine::n_cols(Table::ALL[t]),
                n_public: 0,
                summand,
            })
            .collect()
    }

    /// Every column claim the opening discharges, the bus's then each owned table's at its batch point, located
    /// in the stack: a port's as a strided evaluation of its packed witness.
    fn opening_claims(&self, bus: Vec<ColumnClaim>, tables: &[Claims]) -> Vec<pcs::SlotClaim> {
        let mut claims = bus;
        for (&(base, _), table) in spans().iter().zip(tables) {
            claims.extend(table.evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
                col: base + c,
                point: table.chi.clone(),
                value,
            }));
        }
        claims
            .into_iter()
            .map(|c| match self.placements[c.col] {
                Placement::Committed(window) => pcs::SlotClaim::Point {
                    offset: window.offset,
                    low_point: c.point,
                    value: c.value,
                },
                Placement::Port {
                    offset,
                    port,
                    stride_log,
                } => pcs::SlotClaim::Strided {
                    offset,
                    slot: port,
                    stride_log,
                    point: c.point,
                    value: c.value,
                },
            })
            .collect()
    }
}

/// How many words a proof of `circuit` commits, before the stack's zero pad.
pub fn committed_words(circuit: &Circuit) -> usize {
    witness::committed_len(&Layout::new(circuit).placements)
}

/// The `Hash` table's flock batch, one instance per row.
struct HashBatch {
    tau: usize,
    z: ArenaVec<u64>,
    a: ArenaVec<u64>,
    b: ArenaVec<u64>,
    z_lincheck: ArenaVec<u8>,
}

/// The prover's stack, its ports' values by global column, and the `Hash` table's batch.
struct Witness {
    q: ArenaVec<F64>,
    virt: Vec<(usize, ArenaVec<F64>)>,
    batch: HashBatch,
}

impl Witness {
    fn build(layout: &Layout, a: &Assignment) -> Self {
        // SAFETY: `split_stack` zeroes the pad tail; every committed window is written below: each owned table's
        // committed columns by `fill_table`, the packed witness from its batch, and each port's buffer in full.
        let mut q = unsafe { witness::alloc_stack(layout.shape) };
        let mut virt: Vec<(usize, ArenaVec<F64>)> = Vec::new();
        for (t, &(base, _)) in spans().iter().enumerate() {
            for c in 0..machine::n_ports(Table::ALL[t]) {
                // SAFETY: written in full from the table's batch below.
                virt.push((base + c, unsafe { ArenaVec::uninitialized(1 << layout.taus[t]) }));
            }
        }
        let mut windows = witness::split_stack(&mut q, &layout.placements);
        for (i, buf) in &mut virt {
            windows[*i] = buf;
        }
        for (t, &(base, n)) in spans().iter().enumerate() {
            machine::fill_table(Table::ALL[t], a, &mut windows[base..base + n]);
        }

        let (circuit, stride_log) = (machine::hash_circuit(), machine::hash_stride_log());
        let tau = layout.taus[Table::Hash as usize];
        let (z, za, zb, z_lincheck) = circuit.generate_witness_with(&a.hash, &[0; 14], tau, |row, z, az, bz| {
            crate::rv::circuits::blake2s_witness(row, z, az, bz);
        });
        parallel::chunks_mut_zip(windows[Q_COLUMN], &z, 1 << 16, |_, dst, src| {
            for (d, &s) in dst.iter_mut().zip(src) {
                *d = F64(s);
            }
        });
        let base = spans()[Table::Hash as usize].0;
        for port in 0..machine::N_PORTS {
            for (j, slot) in windows[base + port].iter_mut().enumerate() {
                *slot = F64(z[(j << stride_log) + port]);
            }
        }
        drop(windows);
        let batch = HashBatch {
            tau,
            z,
            a: za,
            b: zb,
            z_lincheck,
        };
        Self { q, virt, batch }
    }

    /// One view per global column: a committed column's window, a port's own buffer.
    fn columns<'a>(&'a self, layout: &Layout) -> Vec<&'a [F64]> {
        let mut cols: Vec<&[F64]> = (layout.placements.iter())
            .map(|p| {
                p.window()
                    .map_or(&[][..], |w| &self.q[w.offset..w.offset + (1 << w.n_vars)])
            })
            .collect();
        for (i, buf) in &self.virt {
            cols[*i] = buf;
        }
        cols
    }
}

/// Prove that `a` is a run of `circuit`, at commitment rate `rate`, the transcript seeded with `iv` and
/// `public_input`.
///
/// # Panics
///
/// Panics if `a` is no run of `circuit` the bus balances, or if the witness exceeds what one commitment holds.
#[tracing::instrument(name = "Prove recursion", skip_all)]
pub fn prove(circuit: &Circuit, a: &Assignment, iv: [F64; 4], public_input: [F64; 4], rate: pcs::Rate) -> Proof {
    let _phase = zk_alloc::enter_phase();
    assert_eq!(a.statement.len(), circuit.statement_len, "the assignment's statement");
    assert!(
        (0..N_TABLES).all(|t| a.rows[t].len() == circuit.rows[t].len()),
        "the assignment's rows are the circuit's"
    );
    let layout = Layout::new(circuit);
    assert!(layout.shape.mu <= pcs::MAX_MU, "the witness exceeds one commitment");
    let log_inv_rate = rate.log_inv_rate().into();
    let mut ps = ProverState::new(iv, public_input);

    let w = crate::stage!("Build witness", || Witness::build(&layout, a));
    let committed = crate::stage!("Commit", || pcs::commit(&mut ps, &w.q, layout.shape, log_inv_rate));

    let (push, pull) = machine::bus_blocks(circuit, &a.statement, &layout.taus, &spans());
    let (bus_claims, table_claims) = {
        let cols = w.columns(&layout);
        let bus = crate::stage!("Prove bus", || leaf::prove_balance(
            &push,
            &pull,
            &[],
            &cols,
            &spans(),
            &mut ps
        ));
        let claims = crate::stage!("Prove constraints", || {
            let xi = ps.sample();
            let sums: Vec<F192> = (0..N_OWNED).map(|t| bus.sigmas[0][t] + xi * bus.sigmas[1][t]).collect();
            let table_cols = spans()
                .iter()
                .map(|&(base, n)| Columns::K(cols[base..base + n].to_vec()))
                .collect();
            constraints::prove(&layout.airs(&bus.forms, xi), table_cols, &bus.point, &sums, &mut ps)
        });
        (bus.claims, claims)
    };
    let slots = layout.opening_claims(bus_claims, &table_claims);

    let Witness { q, virt, batch } = w;
    drop(virt);
    let ring = crate::stage!("Flock reduction", || {
        let block = machine::hash_circuit().block();
        let window = layout.window(Q_COLUMN);
        let stage = block.prove_zerocheck(batch.tau, &batch.z, &batch.a, &batch.b, &mut ps);
        let reduced = block.prove_lincheck(batch.tau, stage, &batch.z_lincheck, &mut ps);
        flock::reduction::ring_switch_open(window.n_vars, window.offset, &reduced)
    });
    crate::stage!("PCS open", || pcs::open(&mut ps, &committed, &q, &slots, &[ring]));
    ps.into_proof()
}

/// Verify a proof that `circuit` has a run exposing `statement`, at rate `2^-log_inv_rate`, the transcript seeded
/// with `iv` and `public_input`.
///
/// # Errors
///
/// Returns the first stage that refuses the proof.
pub fn verify(
    circuit: &Circuit,
    statement: &[Limbs],
    iv: [F64; 4],
    public_input: [F64; 4],
    log_inv_rate: usize,
    proof: &Proof,
) -> Result<(), RecError> {
    verify_to_raw(circuit, statement, iv, public_input, log_inv_rate, proof).map(|_| ())
}

/// [`verify`], returning the proof as its verifier read it, every Merkle path written out: what a recursive
/// verifier replays.
///
/// # Errors
///
/// Returns the first stage that refuses the proof.
pub fn verify_to_raw(
    circuit: &Circuit,
    statement: &[Limbs],
    iv: [F64; 4],
    public_input: [F64; 4],
    log_inv_rate: usize,
    proof: &Proof,
) -> Result<RawProof, RecError> {
    if statement.len() != circuit.statement_len {
        return Err(RecError::StatementLength {
            expected: circuit.statement_len,
            got: statement.len(),
        });
    }
    if u8::try_from(log_inv_rate).map_or(true, |r| pcs::Rate::new(r).is_err()) {
        return Err(RecError::Rate(log_inv_rate));
    }
    let layout = Layout::new(circuit);
    if layout.shape.mu > pcs::MAX_MU {
        return Err(RecError::WitnessSize { mu: layout.shape.mu });
    }
    let mut vs = VerifierState::new(iv, proof, public_input);
    let root = pcs::read_commitment(&mut vs)?;

    let (push, pull) = machine::bus_blocks(circuit, statement, &layout.taus, &spans());
    let bus = leaf::verify_balance(&push, &pull, &[], &spans(), &mut vs)?;
    let xi = vs.sample();
    let target = bus.totals[0] + xi * bus.totals[1];
    let table_claims = constraints::verify(&layout.airs(&bus.forms, xi), &bus.point, target, &mut vs)?.settle()?;
    let slots = layout.opening_claims(bus.claims, &table_claims);

    // The outer verifier is the root, so the `Hash` table's matrices are settled here against the circuit.
    let replay = machine::hash_circuit()
        .block()
        .verify(layout.taus[Table::Hash as usize], &mut vs)?;
    let window = layout.window(Q_COLUMN);
    let ring = flock::reduction::ring_switch_verify(window.n_vars, window.offset, &replay.claim);
    pcs::verify(&mut vs, &slots, &[ring], layout.shape, log_inv_rate, &root)?;
    vs.finish()?;
    Ok(vs.into_raw_proof())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::circuit::{Builder, Dw, Ew, Kw, param_iv, tag};
    use crate::rec::machine::{eval_coord, slot};

    const IV: [F64; 4] = [F64(1), F64(2), F64(3), F64(4)];
    const PUBLIC: [F64; 4] = [F64(5), F64(6), F64(7), F64(8)];

    fn prove_run(circuit: &Circuit, a: &Assignment) -> Proof {
        prove(circuit, a, IV, PUBLIC, pcs::Rate::MIN)
    }

    fn verify_run(circuit: &Circuit, statement: &[Limbs], proof: &Proof) -> Result<(), RecError> {
        verify(
            circuit,
            statement,
            IV,
            PUBLIC,
            pcs::Rate::MIN.log_inv_rate().into(),
            proof,
        )
    }

    /// Wires of [`every_kind`] a test forges.
    struct Wires {
        /// An `EMUL` output another row reads.
        product: Ew,
        /// A bit of a split word nothing else reads.
        lone_bit: Kw,
    }

    /// A circuit using every table and every slot kind.
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
        // A free wire, in one slot only.
        let hint = b.free_e(F192::new(1, 2, 3));
        b.mul_add(hint, one, zero);

        // Two transcript steps, then a Merkle path with a right and a left turn.
        let start = b.d_const([9, 8, 7, 6]);
        let observe = b.k_const(tag::OBSERVE);
        let (acc, _) = b.compress(start, r, observe);
        let squeeze = b.k_const(tag::SQUEEZE);
        let (acc, challenge) = b.compress(acc, zero, squeeze);
        let w = b.free_k(0b1101_0110 | 1 << 40);
        let bits = b.split(w);
        let low = b.pack(&bits[..8]);
        b.eq_k_const(low, 0b1101_0110);
        let right = b.node(acc, bits[1], [1, 2, 3, 4]);
        let root = b.node(right, bits[0], [5, 6, 7, 8]);

        // A leaf's two blocks.
        let h = b.d_const(param_iv());
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
        let kk = b.mul_k(one, k);
        b.eq_e(embedded, kk);
        let digest = b.k_to_d(words);
        b.eq_d(digest, root);
        let lo = b.k_to_e([words[0], words[1], zero_k]);
        let hi = b.k_to_e([words[2], words[3], zero_k]);
        let halves: Dw = b.halves_to_d(lo, hi);
        b.eq_d(halves, root);

        b.expose_e(r);
        b.expose_d(leaf);
        b.expose_k(low);
        let (circuit, a, failures) = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let wires = Wires {
            product,
            lone_bit: bits[40],
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

    /// The `EMUL` and `EXK` outputs are `a·b + d` and `a·k + d` in `E`.
    #[test]
    fn emul_and_exk_outputs_are_e_arithmetic() {
        let words: Vec<u64> = (1..=9u64)
            .map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (i << 61))
            .collect();
        let cols: Vec<F64> = words.iter().map(|&w| F64(w)).collect();
        let e = |c: usize| F192::new(words[c], words[c + 1], words[c + 2]);
        let out = |t: Table| {
            let c = slot(t, 3).map(|c| eval_coord(&c, &cols).0);
            assert_eq!(c[3], 0);
            F192::new(c[0], c[1], c[2])
        };
        assert_eq!(out(Table::Emul), e(0) * e(3) + e(6));
        assert_eq!(out(Table::Exk), e(0).mul_base(F64(words[3])) + e(4));
    }

    #[test]
    fn a_statement_the_prover_did_not_expose_is_rejected() {
        let (circuit, a, _) = every_kind();
        let proof = prove_run(&circuit, &a);
        let mut statement = a.statement;
        statement[0][1] ^= 1;
        assert!(verify_run(&circuit, &statement, &proof).is_err());
    }

    /// A wire in one slot balances whatever it holds, so what refuses a non-Boolean bit is its table's identities.
    #[test]
    fn a_forged_bit_is_rejected() {
        let (circuit, mut a, wires) = every_kind();
        a.values[wires.lone_bit.0 as usize][0] = 2;
        let proof = prove_run(&circuit, &a);
        assert!(matches!(
            verify_run(&circuit, &a.statement, &proof),
            Err(RecError::Constraint(_))
        ));
    }

    /// An `EMUL` output another row reads differently leaves its copy cycle unbalanced, which no prover states.
    #[test]
    fn a_forged_product_unbalances_the_bus() {
        let (circuit, mut a, wires) = every_kind();
        a.values[wires.product.0 as usize][0] ^= 1;
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_run(&circuit, &a)))
            .expect_err("an unbalanced bus was proven");
        let message = refused.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(message.contains("the bus needs the two products to agree"), "{message}");
    }

    /// Every table three rows short of or past a power of two: the padding rows carry nothing.
    #[test]
    fn padding_rows_are_inert() {
        let mut b = Builder::new();
        let mut e = b.free_e(F192::new(2, 3, 4));
        let mut acc = b.d_const([1, 2, 3, 4]);
        let ds = b.k_const(tag::OBSERVE);
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
        let (circuit, a, failures) = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let counts = circuit.row_counts();
        assert_eq!(counts[Table::Hash as usize], 61);
        assert!(counts.iter().all(|&n| n > 1 && !n.is_power_of_two()), "{counts:?}");
        let proof = prove_run(&circuit, &a);
        assert_eq!(verify_run(&circuit, &a.statement, &proof), Ok(()));
    }
}
