//! The bus: a single shared channel balanced by a grand product (§sec:gp through §sec:leafstack). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by one batched GKR over the two sides' leaf vectors `β − π_α(σ)`,
//! the push side ending on the lookup arrays' producers, whose leaves are those raised
//! to the powers their multiplicities' bits select. Each side reduces to a leaf claim
//! `Ṽ₀(ζ)`, decomposed into evaluation claims on the committed columns. Tuple
//! coordinates `σ_i` are `K`-valued (column entries, separators, tags); the
//! fingerprint challenges `α, β` are `E`-valued, so a leaf accumulates via the mixed
//! `mul_base` product (2 PMULL per coordinate).

use crate::gkr;
use crate::gkr::GkrError;
use fiat_shamir::arith::Verifier;
use fiat_shamir::transcript::{Challenger, ProverState, TranscriptError, Transmitter};
use primitives::field::{F64, F192, F192Unreduced, Weights8, dot_base};
use primitives::multilinear::eq_table;
use std::collections::HashMap;
use std::sync::Arc;
use thiserror::Error;

mod coord;
mod decompose;
mod layout;
mod leaves;

pub(crate) use coord::PublicColumns;
pub use coord::{Coord, PublicColumn, SparseColumn};
pub(crate) use decompose::producer_public_twist;
pub use decompose::{BusForm, PackedForm, SparseShare, producer_affine_evals};
pub use layout::{Block, Layout, N_TUPLE_BITS, Owner, Producer, fingerprint_weights, layout, stacked_bytecode_table};
pub use leaves::{build_leaves, producer_columns};

use layout::check_soundness;
use tracing::info_span;

/// An evaluation claim on a committed column, settled against the witness.
/// Reconstructed identically by both sides (its value rides the stream).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnClaim<E = F192> {
    pub col: usize,
    pub point: Vec<E>,
    pub value: E,
}

/// Why the bus does not balance.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum BusError {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The grand products' GKR rejects.
    #[error(transparent)]
    Gkr(#[from] GkrError),
    /// The layout has too many factors for the challenge field and its grinding to give the bus its margin.
    #[error("the bus layout gives {bits} bits of soundness and {grinding} of grinding, below {required}")]
    Soundness { bits: u32, grinding: u32, required: u32 },
}

/// The framework blocks' column claims, deduplicated: push and pull share their GKR
/// point, so a column read by both sides (or by two same-κ blocks of one side) is
/// streamed and opened ONCE; later occurrences reuse the value. Alongside them, each
/// producer's weight on each of its bits' blocks, which its air owes the push side, and
/// the sparse public columns' shares, which the decomposition leaves out.
struct Openings<E> {
    claims: Vec<ColumnClaim<E>>,
    /// `(column, κ)` to the column's value at `ζ[..κ]`: every claim is at a prefix of
    /// the one bus point, so its length names it.
    known: HashMap<(usize, usize), E>,
    /// A public column's value at a prefix of the point, by the column's address and the prefix's length.
    public: HashMap<(usize, usize), E>,
    /// Per producer, its bits' blocks' selectors, in order.
    producers: Vec<Vec<E>>,
    /// The side's blocks' selectors, in order.
    selectors: Vec<E>,
    sparse: Vec<SparseShare<E>>,
    /// The memory logs' blocks' leaves at the bus point, in log order.
    logs: Vec<LogShare<E>>,
}

/// A memory log's block's leaves at a prefix of the bus point, which the log's argument settles.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogShare<E = F192> {
    pub point: Vec<E>,
    pub value: E,
}

impl<E: Copy> Openings<E> {
    /// A public column at a prefix of the bus point, evaluated once per column and prefix length.
    fn public<A: PublicColumns<E = E>>(&mut self, a: &mut A, column: &PublicColumn, point: &[E]) -> E {
        let key = (Arc::as_ptr(&column.values) as usize, point.len());
        if let Some(&x) = self.public.get(&key) {
            return x;
        }
        let x = a.column_mle(column, point);
        self.public.insert(key, x);
        x
    }
}

impl<E> Default for Openings<E> {
    fn default() -> Self {
        Self {
            claims: Vec::new(),
            known: HashMap::new(),
            public: HashMap::new(),
            producers: Vec::new(),
            selectors: Vec::new(),
            sparse: Vec::new(),
            logs: Vec::new(),
        }
    }
}

/// The bus fingerprint `(eq(alpha, .), beta)` and its challenges `alpha`.
struct Fingerprint<E> {
    alphas: Vec<E>,
    w: Vec<E>,
    beta: E,
}

/// One bus side: its blocks and producers, and where they stack.
struct Side<'a> {
    blocks: &'a [Block],
    producers: &'a [Producer],
    lay: Layout,
}

/// The two bus sides in `[push, pull]` order, which both parties lay out the same way before the GKR.
struct BusSetup<'a> {
    sides: [Side<'a>; 2],
    /// The proof-of-work bits before the fingerprint challenges.
    grinding: u32,
}

impl<'a> BusSetup<'a> {
    /// Lay the sides out. The push side ends on the
    /// producers' bits, which no pull pairs with, so the two sides no longer match block
    /// for block: the shorter tree is padded to the taller's depth (identity leaves),
    /// and both run as ONE RLC-batched GKR at ONE shared point.
    ///
    /// # Errors
    ///
    /// A layout too large for the bus's soundness margin at this grinding.
    fn new(push: &'a [Block], pull: &'a [Block], producers: &'a [Producer], grinding: u32) -> Result<Self, BusError> {
        let mut push_lay = layout(push, producers);
        let mut pull_lay = layout(pull, &[]);
        let mu = push_lay.mu.max(pull_lay.mu);
        check_soundness(push, pull, producers, mu, grinding)?;
        (push_lay.mu, pull_lay.mu) = (mu, mu);
        Ok(Self {
            grinding,
            sides: [
                Side {
                    blocks: push,
                    producers,
                    lay: push_lay,
                },
                Side {
                    blocks: pull,
                    producers: &[],
                    lay: pull_lay,
                },
            ],
        })
    }

    /// The depth of the batched GKR.
    const fn mu(&self) -> usize {
        self.sides[0].lay.mu
    }

    /// Each table's form on every side, empty.
    fn empty_forms<E: Copy>(tables: &[(usize, usize)], zero: E) -> [Vec<BusForm<E>>; 2] {
        std::array::from_fn(|_| tables.iter().map(|&(_, n)| BusForm::new(n, zero)).collect())
    }
}

/// What a producer's air is owed and summed over, prover-side: its weight on each
/// bit's block, its columns ([`producer_columns`]), and what its summand sums to
/// against `eq(ζ[..κ], ·)`.
pub struct ProducerProof {
    pub coefficients: Vec<F192>,
    pub columns: Vec<Vec<F192>>,
    pub sigma: F192,
}

/// Prove the bus balances; returns the per-column claims to open (§sec:leafstack). `alpha`/
/// `beta` follow the witness commitment (the only ordering the grand product
/// needs), and the block structure is public, so no shape is observed.
/// Everything the bus hands on: the framework blocks' column claims,
/// the shared GKR point (the table sumcheck's eq point),
/// per side the tables' linear forms plus what each is claimed to sum to, and the
/// producers' share of the push side.
pub struct BusProof {
    pub claims: Vec<ColumnClaim>,
    /// The memory logs' blocks' leaves at the bus point.
    pub logs: Vec<LogShare>,
    /// The GKR point ζ: the zerocheck reuses it, so no fresh point is sampled.
    pub point: Vec<F192>,
    /// `forms[side][table]`, in `[push, pull]` order.
    pub forms: [Vec<BusForm>; 2],
    /// Each table's columns at `ζ[..τ]`: what a table with linear forms sends in place of a sumcheck.
    pub evals: Vec<Vec<F192>>,
    /// `sigmas[side][table]`: each form's eq-weighted sum over its table's rows.
    /// Prover-side only. NOTHING here travels: the batch's target is the caller's
    /// derived `Σ_s η^·totals[s]`, and the shares serve only to build each round's
    /// waiting line, which rides inside the round polynomial.
    pub sigmas: [Vec<F192>; 2],
    /// The producers' share of the push side, in their order.
    pub producers: Vec<ProducerProof>,
    /// The fingerprint weights `eq(α⃗, ·)` and `β`, which the producers' public
    /// columns are made of.
    pub weights: Vec<F192>,
    pub beta: F192,
}

/// Prove the bus balances, after a proof of work of the given bits when there are any.
///
/// `logs` gives each memory log's leaves under the fingerprint's weights and shift.
#[expect(
    clippy::too_many_arguments,
    reason = "the sides, the columns, the logs and the transcript"
)]
pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    producers: &[Producer],
    grinding: u32,
    cols: &[&[F64]],
    logs: impl FnOnce(&[F192], F192) -> Vec<Vec<F192>>,
    tables: &[(usize, usize)],
    ps: &mut ProverState,
) -> BusProof {
    let setup = BusSetup::new(push, pull, producers, grinding).expect("the size caps keep every bus layout sound");
    // No grinding sends no nonce.
    if setup.grinding > 0 {
        ps.grind(setup.grinding);
    }
    let alphas = ps.sample_vec(N_TUPLE_BITS);
    let fp = Fingerprint {
        w: fingerprint_weights(&alphas),
        alphas,
        beta: ps.sample(),
    };
    // The logs' leaves, under the fingerprint.
    let logs = logs(&fp.w, fp.beta);
    let logs = logs.as_slice();
    // Two independent leaf vectors, built one after another: each `build_leaves`
    // already fans its own blocks out across the whole pool, so nesting an outer
    // split on top would only add a barrier. The all-one padding stays implicit.
    let leaves = info_span!("Bus leaves").in_scope(|| {
        setup
            .sides
            .each_ref()
            .map(|side| build_leaves(side.blocks, side.producers, &side.lay, cols, logs, &fp.w, fp.beta))
    });
    // Both trees run as ONE RLC-batched GKR, the shorter padded, so every claim lands
    // on ONE point ζ.
    let bus_gkr = info_span!("Bus GKR").in_scope(|| gkr::prove_products(leaves, ps));

    // Framework blocks keep their per-column claims (deduped: push/pull share ζ);
    // every table block becomes a form for the zerocheck instead, and every producer
    // bit a weight for its producer's air.
    // Each table's columns at ζ[..τ], computed once and shared by the two sides
    // (a form's linear part factors through them). No total travels: the verifier derives
    // each side's table share as `Ṽ₀(ζ)` less the framework decomposition (`verify_balance`).
    // The caller sends a linear table's evaluations, which the opening binds, and the batch
    // settles the rest. A transmitted total would appear in exactly one check, which it could
    // always be solved to satisfy, and would settle nothing.
    let mut forms = BusSetup::empty_forms(tables, F192::ZERO);
    let mut frameworks = [F192::ZERO; 2];
    let mut open = Openings::default();
    info_span!("Bus decompose").in_scope(|| {
        for (s, side) in setup.sides.iter().enumerate() {
            frameworks[s] = side.decompose_prove(&fp, cols, &bus_gkr.point, tables, &mut forms[s], &mut open, logs, ps);
        }
    });
    let (table_evals, prod_sums) = tables_and_prods_at(cols, tables, &forms, &bus_gkr.point);
    let Fingerprint { w, beta, .. } = fp;
    let producers: Vec<ProducerProof> = producers
        .iter()
        .zip(std::mem::take(&mut open.producers))
        .map(|(p, coefficients)| {
            let columns = producer_columns(p, cols, &w, beta);
            let eq = eq_table(&bus_gkr.point[..p.kappa]);
            let (bits, public) = columns.split_at(p.bits);
            // Bit `i`'s block at ζ: `Σ_x eq(ζ, x)·(1 + b_i(x)·P'_i(x))`, the eq weights summing to one.
            let sigma = parallel::map_reduce(
                p.bits,
                || F192::ZERO,
                |i| {
                    let rows = eq.iter().zip(bits[i].iter().zip(public[i].iter()));
                    let sum = rows.fold(F192::ZERO, |s, (&e, (&b, &q))| s + e * b * q);
                    coefficients[i] * (F192::ONE + sum)
                },
                |a, b| a + b,
            );
            ProducerProof {
                coefficients,
                columns,
                sigma,
            }
        })
        .collect();
    let sigmas: [Vec<F192>; 2] = std::array::from_fn(|s| {
        let sigmas: Vec<F192> = forms[s]
            .iter()
            .zip(&table_evals)
            .zip(&prod_sums)
            .map(|((f, e), p)| f.sum_at(e, p))
            .collect();
        // Completeness only: the verifier derives this identity rather than checking
        // it, so a mismatch here is a prover bug, not a rejection path.
        let producers = if s == 0 {
            producers.iter().map(|p| p.sigma).collect()
        } else {
            Vec::new()
        };
        debug_assert_eq!(
            sigmas.iter().chain(&producers).fold(frameworks[s], |acc, &b| acc + b),
            bus_gkr.values[s],
            "side {s} must decompose into its leaf value"
        );
        sigmas
    });

    BusProof {
        claims: open.claims,
        logs: open.logs,
        point: bus_gkr.point,
        forms,
        evals: table_evals,
        sigmas,
        producers,
        weights: w,
        beta,
    }
}

/// Every table's committed columns at `ζ[..τ_t]`, and, for every column pair its
/// forms multiply, `Σ_z eq(ζ[..τ], z)·col_a(z)·col_b(z)`.
///
/// One eq table per table, streamed once past every column and every pair at
/// the same time. Evaluated apart these are `n_cols + n_pairs` fold ladders
/// over the same table at the same point, and a ladder lifts every `K` word it
/// reads into an `E` it writes and reads again, where a dot against the weights
/// moves the column's own eight bytes. Pairs are deduped across the two sides
/// and the several blocks that carry the same address, so an address costs one
/// pass however often it is flushed. `tables[t] = (base, n_cols)` in the global
/// schema; a pair names LOCAL column indices.
#[allow(clippy::type_complexity)]
fn tables_and_prods_at(
    cols: &[&[F64]],
    tables: &[(usize, usize)],
    forms: &[Vec<BusForm>; 2],
    zeta: &[F192],
) -> (Vec<Vec<F192>>, Vec<Vec<(usize, usize, F192)>>) {
    /// Rows per task: the eq slice a task reads stays in L2 while every column
    /// and pair accumulator sweeps past it.
    const ROWS: usize = 1 << 12;

    tables
        .iter()
        .enumerate()
        .map(|(t, &(base, n_cols))| {
            let tau = crate::log2_strict_usize(cols[base].len());
            let mut pairs: Vec<(usize, usize)> = forms
                .iter()
                .flat_map(|side| side[t].prods.iter().map(|&(a, b, _)| (a, b)))
                .collect();
            pairs.sort_unstable();
            pairs.dedup();

            let eq = eq_table(&zeta[..tau]);
            let n_acc = n_cols + pairs.len();
            // A task packs its eq slice once, then every column and pair dots against it
            // eight rows at a time; a slice short of eight rows takes the scalar path.
            let sums = parallel::map_reduce_with_state(
                (1usize << tau).div_ceil(ROWS),
                || (Vec::with_capacity(ROWS / 8), Vec::with_capacity(ROWS)),
                || vec![F192Unreduced::ZERO; n_acc],
                |(packed, products): &mut (Vec<Weights8>, Vec<F64>), acc, chunk| {
                    let lo = chunk * ROWS;
                    let weights = &eq[lo..(lo + ROWS).min(1 << tau)];
                    let span = |c: usize| &cols[base + c][lo..lo + weights.len()];
                    let (blocks, tail) = weights.as_chunks::<8>();
                    let split = 8 * blocks.len();
                    packed.clear();
                    packed.extend(blocks.iter().map(Weights8::new));
                    let dot = |k: &[F64]| {
                        tail.iter()
                            .zip(&k[split..])
                            .fold(dot_base(packed, &k[..split]), |acc, (&w, &v)| {
                                acc ^ w.mul_base_unreduced(v)
                            })
                    };
                    for (c, slot) in acc[..n_cols].iter_mut().enumerate() {
                        *slot ^= dot(span(c));
                    }
                    for (&(a, b), slot) in pairs.iter().zip(&mut acc[n_cols..]) {
                        products.clear();
                        products.extend(span(a).iter().zip(span(b)).map(|(&x, &y)| x * y));
                        *slot ^= dot(products);
                    }
                },
                |mut left, right| {
                    for (slot, part) in left.iter_mut().zip(right) {
                        *slot ^= part;
                    }
                    left
                },
            );
            let evals = sums[..n_cols].iter().map(|s| s.reduce()).collect();
            let prods = pairs
                .iter()
                .zip(&sums[n_cols..])
                .map(|(&(a, b), s)| (a, b, s.reduce()))
                .collect();
            (evals, prods)
        })
        .unzip()
}

/// What [`verify_balance`] establishes: the per-column claims to open and the
/// table forms with their claimed sums.
pub struct BusVerify<E = F192> {
    pub claims: Vec<ColumnClaim<E>>,
    /// The memory logs' blocks' leaves at the bus point.
    pub logs: Vec<LogShare<E>>,
    /// The GKR point ζ, reused as the table sumcheck's eq point.
    pub point: Vec<E>,
    /// `forms[side][table]`, for the zerocheck to settle.
    pub forms: [Vec<BusForm<E>>; 2],
    /// Per producer, its weight on each bit's block.
    pub producers: Vec<Vec<E>>,
    /// Per side, what the tables' and the producers' blocks owe its leaf claim:
    /// `Ṽ₀(ζ)` less the framework blocks' decomposition and the tables' virtual
    /// coordinates. Derived here, pinned by the batch's target. The sparse columns' shares are not in it.
    pub totals: [E; 2],
    /// Per side, the sparse columns' shares: the tables owe `totals[s] + sum weight col(point)`.
    pub sparse: [Vec<SparseShare<E>>; 2],
    /// Per side, each block's selector `eq(sel_b, zeta_hi)`, in block order.
    pub selectors: [Vec<E>; 2],
    /// The fingerprint's challenges `alpha`.
    pub alphas: Vec<E>,
    /// The fingerprint weights `eq(alpha, .)` and `beta`, which the producers' public columns are made of.
    pub weights: Vec<E>,
    pub beta: E,
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
///
/// # Errors
///
/// Returns the GKR's refusal, a malformed stream, a nonce short of the proof of work, or a layout too large for the bus's margin at this grinding.
pub fn verify_balance<V: Verifier + PublicColumns>(
    v: &mut V,
    push: &[Block],
    pull: &[Block],
    producers: &[Producer],
    grinding: u32,
    tables: &[(usize, usize)],
) -> Result<BusVerify<V::E>, BusError> {
    let setup = BusSetup::new(push, pull, producers, grinding)?;
    if setup.grinding > 0 {
        v.grind_check(setup.grinding)?;
    }
    let alphas = v.sample_vec(N_TUPLE_BITS);
    let fp = Fingerprint {
        w: v.eq_table(&alphas),
        alphas,
        beta: v.sample(),
    };
    let bus_gkr = gkr::verify_products(v, setup.mu())?;
    // Every row of every table is a real row (`cpu::filler`), so the two sides balance
    // outright: no padding tuples to divide back out, and no announced row counts whose
    // truthfulness the soundness argument would have to establish. The GKR sends ONE root
    // for both sides, so a prover cannot even state an unbalanced bus, and there is nothing
    // to check here.

    // Framework blocks decompose as before; the tables' blocks become linear forms and the
    // producers' bits weights on their airs. Each side's share of those is DERIVED from
    // `framework + Ṽ₀(ζ)` rather than checked here, the batch's target being what pins
    // it, so no table column is opened at ζ.
    let zero = v.zero();
    let mut forms = BusSetup::empty_forms(tables, zero);
    let mut totals = [zero; 2];
    let mut sparse: [Vec<SparseShare<V::E>>; 2] = Default::default();
    let mut selectors: [Vec<V::E>; 2] = Default::default();
    let mut open = Openings::default();
    for (s, side) in setup.sides.iter().enumerate() {
        let framework = side.decompose(v, &fp, &bus_gkr.point, tables, &mut forms[s], &mut open, |v, _, _| {
            v.next_scalar()
        })?;
        // What the tables owe this side: DERIVED, never read. A transmitted total
        // would be a free variable in its own check and would settle nothing; the
        // caller instead pins these against the batch's target.
        totals[s] = v.add(framework, bus_gkr.values[s]);
        sparse[s] = std::mem::take(&mut open.sparse);
        selectors[s] = std::mem::take(&mut open.selectors);
    }

    Ok(BusVerify {
        claims: open.claims,
        logs: open.logs,
        point: bus_gkr.point,
        forms,
        producers: open.producers,
        totals,
        sparse,
        selectors,
        alphas: fp.alphas,
        weights: fp.w,
        beta: fp.beta,
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::layout::{BUS_SOUNDNESS_BITS, soundness_bits};
    use super::leaves::tuple_leaves;
    use super::{
        Block, BusError, BusSetup, Coord, F64, F192, N_TUPLE_BITS, Owner, Producer, PublicColumn, SparseColumn,
        build_leaves, fingerprint_weights, gkr, layout, prove_balance, verify_balance,
    };
    use crate::cpu::layout::{Log, Sizes};
    use crate::cpu::{Layout, Lookup, Program, UNGROUND_LOG_BYTECODE};
    use crate::pcs::MAX_MU;
    use crate::rv::Region;
    use crate::tables::PerTable;
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use std::collections::HashMap;
    use std::sync::Arc;

    /// The leaves one side has in excess of the other, as `(side, block, row)`, under
    /// one fixed fingerprint: what to look at when a bus does not balance. A producer's
    /// entry counts as its multiplicity's worth of leaves, reported as block
    /// `push.len() + p` for producer `p`. A log's block takes the leaves `logs` gives under that fingerprint, a dead
    /// row's leaf one being no tuple.
    pub(crate) fn unmatched_leaves(
        push: &[Block],
        pull: &[Block],
        producers: &[Producer],
        cols: &[&[F64]],
        logs: impl FnOnce(&[F192], F192) -> Vec<Vec<F192>>,
    ) -> Vec<(&'static str, usize, usize)> {
        let alphas: Vec<F192> = (0..N_TUPLE_BITS as u64)
            .map(|i| F192::new(3 + i, 5 + 7 * i, 11))
            .collect();
        let (w, beta) = (fingerprint_weights(&alphas), F192::new(13, 17, 19));
        let logs = logs(&w, beta);
        let side = |blocks: &[Block]| {
            let mut at = Vec::new();
            for (b, block) in blocks.iter().enumerate() {
                let leaves = match block.owner {
                    Owner::Log(l) => logs[l].clone(),
                    _ => tuple_leaves(&block.coords, block.kappa, cols, &w, beta),
                };
                let live = leaves.into_iter().enumerate().filter(|(_, leaf)| *leaf != F192::ONE);
                at.extend(live.map(|(z, leaf)| (leaf, b, z)));
            }
            at
        };
        let (mut pushed, pulled) = (side(push), side(pull));
        for (p, producer) in producers.iter().enumerate() {
            let leaves = tuple_leaves(&producer.coords, producer.kappa, cols, &w, beta);
            for (x, leaf) in leaves.into_iter().enumerate() {
                let m = cols[producer.col][x].0 & ((1u64 << producer.bits) - 1);
                pushed.extend(std::iter::repeat_n((leaf, push.len() + p, x), m as usize));
            }
        }
        let key = |leaf: &F192| (leaf.c0, leaf.c1, leaf.c2);
        let mut counts: HashMap<_, i64> = HashMap::new();
        for (leaf, ..) in &pushed {
            *counts.entry(key(leaf)).or_default() += 1;
        }
        for (leaf, ..) in &pulled {
            *counts.entry(key(leaf)).or_default() -= 1;
        }
        // Each tuple's excess, on the side that has it.
        let mut unmatched = |name: &'static str, leaves: &[(F192, usize, usize)], sign: i64| {
            let mut out = Vec::new();
            for &(leaf, b, z) in leaves {
                let excess = counts.get_mut(&key(&leaf)).expect("a counted leaf");
                if *excess * sign > 0 {
                    *excess -= sign;
                    out.push((name, b, z));
                }
            }
            out
        };
        [unmatched("push", &pushed, 1), unmatched("pull", &pulled, -1)].concat()
    }

    #[test]
    fn a_tables_virtual_coordinates_join_the_known_part() {
        // Table 0 pushes `(sep, base ^ (z << 3), public[z], col[z])`; a framework block pulls the same tuples.
        let kappa = 3;
        let column: Vec<F64> = (0..1u64 << kappa).map(|z| F64(z * 0x9e37_79b9 + 5)).collect();
        let public = Arc::new((0..1u64 << kappa).map(|z| F64(z ^ 0xabcd)).collect::<Vec<_>>());
        let coords = vec![
            Coord::Const(F64(7)),
            Coord::IntIndex {
                base: F64(0x4000),
                shift: 3,
            },
            Coord::Public(PublicColumn::new(public)),
            Coord::Col(0),
        ];
        let push = [Block::table(0, kappa, coords.clone())];
        let pull = [Block::framework(kappa, coords)];
        let tables = [(0, 1)];

        let mut ps = ProverState::from_label(b"leaf-virtual-coordinates");
        let bus = prove_balance(&push, &pull, &[], 0, &[&column], |_, _| Vec::new(), &tables, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::from_label(b"leaf-virtual-coordinates", &proof);
        let verified = verify_balance(&mut vs, &push, &pull, &[], 0, &tables).expect("an honest bus balances");

        // What the verifier derives the tables owe is what their forms sum to, the virtual coordinates aside.
        for side in 0..2 {
            assert_eq!(verified.totals[side], bus.sigmas[side][0], "side {side}");
            assert_eq!(verified.forms[side][0].coeffs, bus.forms[side][0].coeffs, "side {side}");
            assert_eq!(
                verified.forms[side][0].constant, bus.forms[side][0].constant,
                "side {side}"
            );
        }
        assert_ne!(verified.totals[0], F192::ZERO);
    }

    /// A sparse column's block-wise evaluation is its dense multilinear extension,
    /// whatever the stretches' offsets and lengths.
    #[test]
    fn sparse_column_evaluates_as_its_dense_form() {
        let words: Vec<u64> = (1..=37).map(|i| i * 0x9e37_79b9_7f4a_7c15).collect();
        let column = SparseColumn::new(9, &[(0, &words[..4]), (5, &words[4..17]), (300, &words[17..])]);
        assert_eq!(
            column.dense()[5..18],
            words[4..17].iter().map(|&w| F64(w)).collect::<Vec<_>>()
        );
        assert_eq!(column.dense().iter().filter(|w| !w.is_zero()).count(), words.len());
        let point: Vec<F192> = (0..9).map(|i| F192::new(3 + i, 5 * i + 1, 7)).collect();
        assert_eq!(
            column.eval(&point),
            primitives::multilinear::mle_eval(column.dense(), &point)
        );
    }

    /// The first product level `build_leaves` returns is `gkr::next_level` of its leaves,
    /// whichever way each four-tuple's product was formed: in a block's fill (eight rows
    /// or more, a parallel one at `PAR_THRESHOLD`), or after it (smaller blocks, a
    /// producer's bits, and the ragged last four-tuple).
    #[test]
    fn build_leaves_forms_the_first_product_level() {
        let rows = 1u64 << 11;
        let cols: Vec<Vec<F64>> = (0..3u64)
            .map(|c| {
                (0..rows)
                    .map(|z| F64((z + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (c << 40)))
                    .collect()
            })
            .collect();
        let cols: Vec<&[F64]> = cols.iter().map(Vec::as_slice).collect();
        let coords = || {
            vec![
                Coord::Const(F64(7)),
                Coord::IntIndex {
                    base: F64(0x4000),
                    shift: 3,
                },
                Coord::Col(0),
                Coord::Prod(1, 2),
            ]
        };
        // Out of size order, so the layout moves every block.
        let blocks: Vec<Block> = [2, 0, 11, 3, 1]
            .into_iter()
            .map(|kappa| Block::framework(kappa, coords()))
            .collect();
        let producers = [Producer {
            kappa: 4,
            coords: vec![Coord::Col(1)],
            col: 2,
            bits: 2,
            deferred: true,
        }];
        let lay = layout(&blocks, &producers);
        let alphas: Vec<F192> = (0..N_TUPLE_BITS as u64)
            .map(|i| F192::new(3 + i, 5 + 7 * i, 11))
            .collect();
        let w = fingerprint_weights(&alphas);
        let (leaves, products) = build_leaves(&blocks, &producers, &lay, &cols, &[], &w, F192::new(13, 17, 19));
        assert_eq!(leaves.len(), (1 << 11) + 8 + 2 * 16 + 4 + 2 + 1);
        assert_eq!(products, gkr::next_level(&leaves));
    }

    /// The bound is `N_TUPLE_BITS` per linear factor plus the GKR terms: the
    /// multilinear fingerprint fixes each factor's total degree at four, whatever
    /// the tuple's width.
    #[test]
    fn bus_soundness_tracks_factors() {
        // 2^f factors of degree four cost f + 2 bits, and the GKR's terms one more.
        let largest = (192 - BUS_SOUNDNESS_BITS - 3) as usize;
        assert!(soundness_bits(1 << largest, largest) >= BUS_SOUNDNESS_BITS);
        assert!(soundness_bits(1 << (largest + 1), largest + 1) < BUS_SOUNDNESS_BITS);
    }

    #[test]
    fn every_layout_one_commitment_holds_keeps_the_margin_with_its_grinding() {
        // Every block of a RISC-V layout at 2^MAX_MU rows, more than any block of a committed layout has.
        let program = Program::new(&[0x0000_0073], Region::TEXT.base(), vec![], 0, 0).unwrap();
        let view = program.view();
        let layout = Layout::new(&view, PerTable::default(), [Log::MIN_LOG_ROWS; 2]);
        let widest = |blocks: &[Block]| -> Vec<Block> {
            blocks
                .iter()
                .map(|b| Block {
                    kappa: MAX_MU,
                    ..b.clone()
                })
                .collect()
        };
        let (push, pull) = (widest(&layout.push), widest(&layout.pull));

        // The multiplicity column and every table's packed witness share the commitment, so the rows, every one a
        // bytecode read, number below 2^MAX_MU, and a multiplicity has at most MAX_MU bits.
        //
        // The padding tuples are the fill blocks', the same for every program, and a row pulls at most sixteen of them.
        let bytecode = |log_entries: usize| {
            let [bytecode, padding] = [Lookup::Bytecode, Lookup::Padding].map(|l| layout.producers[l as usize].clone());
            vec![
                Producer {
                    kappa: log_entries,
                    bits: MAX_MU,
                    ..bytecode
                },
                Producer {
                    bits: MAX_MU + 4,
                    ..padding
                },
            ]
        };

        // Every text the region holds keeps the margin with its grinding, and one bit less grinding loses it.
        let keeps =
            |log_bytecode: usize, grinding: u32| BusSetup::new(&push, &pull, &bytecode(log_bytecode), grinding).is_ok();
        for log_bytecode in 0..=Region::TEXT.max_log_words() {
            let sizes = Sizes {
                log_bytecode,
                ..Sizes::of(&view, [0; 2])
            };
            let grinding = Lookup::Bytecode.grinding_bits(sizes);
            assert!(keeps(log_bytecode, grinding), "2^{log_bytecode} entries");
            assert_eq!(grinding == 0, log_bytecode <= UNGROUND_LOG_BYTECODE);
            if grinding > 0 {
                assert!(!keeps(log_bytecode, grinding - 1), "2^{log_bytecode} entries");
            }
        }
    }

    #[test]
    fn a_layout_past_the_margin_is_refused() {
        // A producer of 2^30 entries whose multiplicities have 30 bits: about 2^60 factors.
        let tuple = vec![Coord::Const(F64::ONE)];
        let producers = [Producer {
            kappa: 30,
            coords: tuple.clone(),
            col: 0,
            bits: 30,
            deferred: true,
        }];
        let pull = [Block::framework(0, tuple)];

        // Without grinding, the verifier's setup refuses it with an error, before drawing any challenge.
        assert!(matches!(
            BusSetup::new(&[], &pull, &producers, 0),
            Err(BusError::Soundness {
                required: BUS_SOUNDNESS_BITS,
                ..
            })
        ));
    }
}
