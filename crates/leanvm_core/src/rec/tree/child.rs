//! A recursion machine's proof verified in rows (`rec::proof::verify`), for a node whose children are recursion
//! proofs: the bus, the table sumcheck, the `Hash` table's flock reduction and the stacked opening with its
//! ring-switched share.
//!
//! What the native verifier evaluates of the circuit, its public `next` columns and the `Pub` rows' constants, is
//! fixed by the child's shape and left as one claim on the fixed polynomial, whose value is a hint; the `Pub` rows
//! of the child's statement are evaluated here, from the statement's wires. The `Hash` table's matrices are left
//! as a matrix claim, like the RISC-V verifier's.

use super::fixed::FixedLayout;
use super::reduce::{DenseClaim, Term};
use crate::class_flock;

use crate::rec::circuit::{Builder, Dw, Ew, Kw, N_TABLES, Table};
use crate::rec::inner::bus::{verify_products, weighted_coord};
use crate::rec::inner::math::{eq_bits, eq_table, int_index_mle, poly_eval, times_one_plus};
use crate::rec::inner::pcs::RingMode;
use crate::rec::inner::{MatrixClaim, RingRegion, StackClaim};
use crate::rec::machine::{self, Fixed, N_OWNED};
use crate::rec::proof::{self, Q_COLUMN};
use crate::rec::transcript::Transcript;
use crate::witness::Placement;
use primitives::field::{F64, F192};

/// What verifying a child leaves: its `Hash` table's matrix claim, the claim on its circuit's fixed polynomial (of
/// the dense polynomials, number `poly`), the transcript's final state, and the table sumcheck's target, which the
/// native verifier derives from the bus with the fixed columns evaluated.
pub struct Child {
    pub matrix: MatrixClaim,
    pub fixed: DenseClaim,
    pub state: Dw,
    pub target: Ew,
}

/// A table's bus block on one side, kept symbolic until its columns' values are read.
struct FormBlock {
    table: Table,
    side: usize,
    selector: Ew,
    slot: usize,
}

/// One fixed column's term in the bus: its index in [`machine::fixed_columns`], its coefficient, and its side.
struct FixedTerm {
    column: usize,
    coef: Ew,
    side: usize,
}

/// Verify a recursion proof of heights `taus` and rate `log_inv_rate`, read by `t` (seeded with its statement),
/// whose statement is the words `statement`, each given as its limbs. `columns` are the child's fixed columns,
/// which only the prover holds, at `fixed` in the dense polynomial `poly`, under the coordinates `top` that name
/// its circuit there.
#[expect(
    clippy::too_many_arguments,
    reason = "a child's shape, statement and kind, each its own input"
)]
pub fn verify_child(
    b: &mut Builder,
    t: &mut Transcript,
    taus: &[usize; N_TABLES],
    log_inv_rate: usize,
    statement: &[Vec<Kw>],
    top: &[Ew],
    fixed: &FixedLayout,
    columns: Option<&[Vec<F64>]>,
    poly: usize,
) -> Child {
    let layout = proof::Layout::from_taus(*taus);
    let spans = proof::spans();
    let root = t.next_root(b);

    // The bus: the `Pub` block, then every owned table's slots, on both sides alike.
    let mut blocks: Vec<(Table, usize)> = vec![(Table::Pub, 0)];
    blocks.extend(
        Table::ALL[..N_OWNED]
            .iter()
            .flat_map(|&t| (0..t.n_slots()).map(move |s| (t, s))),
    );
    let kappas: Vec<Option<usize>> = blocks.iter().map(|&(t, _)| Some(taus[t as usize])).collect();
    let (offsets, placed) = crate::witness::stack_offsets(&kappas);
    let mu = crate::log2_ceil_usize(placed.max(1));

    let alphas = t.sample_vec(b, crate::leaf::N_TUPLE_BITS);
    let weights = eq_table(b, &alphas);
    let beta = t.sample(b);
    let (zeta, gkr_values) = b.scope("gkr", |b| verify_products(b, t, mu));

    let statement_part = b.scope("statement", |b| {
        statement_mle(b, statement, &zeta[..taus[Table::Pub as usize]], &weights)
    });
    let column_of = |f: Fixed| {
        machine::fixed_columns()
            .iter()
            .position(|&c| c == f)
            .expect("a fixed column")
    };
    let mut fixed_terms: Vec<FixedTerm> = Vec::new();
    let mut forms: Vec<FormBlock> = Vec::new();
    let mut totals = [beta; 2];
    for side in 0..2 {
        let mut acc = b.zero();
        let mut selectors = Vec::with_capacity(blocks.len());
        for (i, &(table, slot)) in blocks.iter().enumerate() {
            let kappa = taus[table as usize];
            let zeta_lo = &zeta[..kappa];
            let eq_hi = eq_bits(b, offsets[i] >> kappa, &zeta[kappa..mu]);
            selectors.push(eq_hi);
            let base = machine::key(table, slot, 0);
            // The key: the slot's own on the pull side, `next` on the push side.
            let key = if side == 1 {
                let k = int_index_mle(b, base, 0, zeta_lo);
                Some(b.mul(weights[0], k))
            } else {
                let coef = b.mul(eq_hi, weights[0]);
                fixed_terms.push(FixedTerm {
                    column: column_of(Fixed::Next(table, slot)),
                    coef,
                    side,
                });
                None
            };
            if table == Table::Pub {
                for j in 0..4 {
                    let coef = b.mul(eq_hi, weights[1 + j]);
                    fixed_terms.push(FixedTerm {
                        column: column_of(Fixed::Value(j)),
                        coef,
                        side,
                    });
                }
                let mut leaf = b.add(beta, statement_part);
                if let Some(k) = key {
                    leaf = b.add(leaf, k);
                }
                acc = b.mul_add(eq_hi, leaf, acc);
            } else {
                if let Some(k) = key {
                    acc = b.mul_add(eq_hi, k, acc);
                }
                forms.push(FormBlock {
                    table,
                    side,
                    selector: eq_hi,
                    slot,
                });
            }
        }
        selectors.push(acc);
        selectors.push(gkr_values[side]);
        let sum = b.sum(&selectors);
        totals[side] = b.add_const(sum, F192::ONE);
    }

    let xi = t.sample(b);
    for term in fixed_terms.iter_mut().filter(|term| term.side == 1) {
        term.coef = b.mul(term.coef, xi);
    }
    let fixed_claim = fixed_claim(b, fixed, taus, &zeta, top, &fixed_terms, columns, poly);
    let target = b.mul_add(xi, totals[1], totals[0]);
    let target = b.add(target, fixed_claim.value);

    let (chi, table_values) = b.scope("table sumcheck", |b| {
        table_sumcheck(b, t, taus, &zeta, target, xi, beta, &weights, &forms)
    });

    let mut slots = Vec::new();
    for (ti, &(base, n_cols)) in spans.iter().enumerate() {
        let point = chi[..taus[ti]].to_vec();
        for (c, &value) in table_values[ti].iter().enumerate().take(n_cols) {
            slots.push(match layout.placements[base + c] {
                Placement::Committed(window) => StackClaim::Point {
                    offset: window.offset,
                    low_point: point.clone(),
                    value,
                },
                Placement::Port {
                    offset,
                    port,
                    stride_log,
                } => StackClaim::Strided {
                    offset,
                    slot: port,
                    stride_log,
                    point: point.clone(),
                    value,
                },
            });
        }
    }

    let (slice, matrix) = b.scope("flock", |b| {
        crate::rec::inner::flock::verify_reduction(
            b,
            t,
            class_flock::shape(machine::hash_flock()),
            taus[Table::Hash as usize],
        )
    });
    let window = layout.window(Q_COLUMN);
    let rings = [RingRegion {
        offset: window.offset,
        qflock_vars: window.n_vars,
        claims: vec![slice],
    }];
    b.scope("opening", |b| {
        crate::rec::inner::pcs::verify(b, t, &slots, &rings, layout.shape, log_inv_rate, root, RingMode::Prove)
    });
    if !t.finished() {
        b.scope("transcript", |b| b.fail("the proof has data the verifier never reads"));
    }
    Child {
        matrix,
        fixed: fixed_claim,
        state: t.state(),
        target,
    }
}

/// The `Pub` rows' share of the bus from the statement's rows: `Σ_{z < S} eq(z, ζ)·Σ_j w_{1+j}·limb_j(word_z)`.
fn statement_mle(b: &mut Builder, statement: &[Vec<Kw>], zeta: &[Ew], weights: &[Ew]) -> Ew {
    let s_log = crate::log2_ceil_usize(statement.len().max(1));
    assert!(s_log <= zeta.len(), "the statement fits the `Pub` table");
    let eq = eq_table(b, &zeta[..s_log]);
    let mut sum = b.zero();
    for (word, &e) in statement.iter().zip(&eq) {
        let mut inner = b.zero();
        for (j, &limb) in word.iter().enumerate() {
            inner = b.mul_k_add(weights[1 + j], limb, inner);
        }
        sum = b.mul_add(e, inner, sum);
    }
    zeta[s_log..].iter().fold(sum, |acc, &z| times_one_plus(b, acc, z))
}

/// The fixed columns' terms as one claim on the fixed polynomial, under the coordinates `top`, its value a hint the
/// prover computes from `columns`.
#[expect(
    clippy::too_many_arguments,
    reason = "the claim's point is the bus's, its terms the bus's coefficients"
)]
fn fixed_claim(
    b: &mut Builder,
    fixed: &FixedLayout,
    taus: &[usize; N_TABLES],
    zeta: &[Ew],
    top: &[Ew],
    terms: &[FixedTerm],
    columns: Option<&[Vec<F64>]>,
    poly: usize,
) -> DenseClaim {
    let tau_of = |column: usize| taus[fixed.columns[column].table() as usize];
    let value = columns.map_or(F192::ZERO, |columns| {
        let z: Vec<F192> = zeta.iter().map(|&w| b.e(w)).collect();
        terms.iter().fold(F192::ZERO, |acc, term| {
            let tau = tau_of(term.column);
            acc + b.e(term.coef) * primitives::multilinear::mle_eval(&columns[term.column], &z[..tau])
        })
    });
    let value = b.free_e(value);
    let terms = terms
        .iter()
        .map(|term| {
            let tau = tau_of(term.column);
            let sel = fixed.offsets[term.column] >> tau;
            Term {
                coef: Some(term.coef),
                n_low: tau,
                bits: (0..fixed.omega - tau).map(|k| (sel >> k) & 1 == 1).collect(),
                top: top.to_vec(),
            }
        })
        .collect();
    DenseClaim {
        poly,
        low: zeta.to_vec(),
        terms,
        value,
    }
}

/// `constraints::verify` on the recursion machine's airs (`machine::summands`): returns the point and each owned
/// table's columns' values there, the final identity checked.
#[expect(clippy::too_many_arguments, reason = "the batch's target and the bus's fingerprint")]
fn table_sumcheck(
    b: &mut Builder,
    t: &mut Transcript,
    taus: &[usize; N_TABLES],
    zeta: &[Ew],
    target: Ew,
    xi: Ew,
    beta: Ew,
    weights: &[Ew],
    forms: &[FormBlock],
) -> (Vec<Ew>, Vec<Vec<Ew>>) {
    let n = taus[..N_OWNED].iter().copied().max().unwrap_or(0);
    let mut claim = target;
    let mut air_weights: Vec<Option<Ew>> = vec![None; N_OWNED];
    let mut chi: Vec<Option<Ew>> = vec![None; n];
    for j in 0..n {
        let m = n - 1 - j;
        let h = t.next_round_poly(b, 4, claim, None);
        let rk = t.sample(b);
        chi[m] = Some(rk);
        claim = poly_eval(b, &h, rk);
        let s = b.add(zeta[m], rk);
        for (w, &tau) in air_weights.iter_mut().zip(&taus[..N_OWNED]) {
            *w = Some(match (*w, tau > m) {
                (Some(w), true) => times_one_plus(b, w, s),
                (None, true) => b.add_const(s, F192::ONE),
                (Some(w), false) => b.mul(w, rk),
                (None, false) => rk,
            });
        }
    }
    let chi: Vec<Ew> = chi
        .into_iter()
        .map(|c| c.expect("every round binds its variable"))
        .collect();

    // The identities' powers of `xi` start at `xi^2`, each table's range after the previous one's.
    let xi2 = b.square(xi);
    let mut power = xi2;
    let mut residual = b.zero();
    let mut values_all = Vec::with_capacity(N_OWNED);
    for (ti, &table) in Table::ALL[..N_OWNED].iter().enumerate() {
        let values = t.next_scalars(b, machine::n_cols(table));
        let mut summand = b.zero();
        for side in 0..2 {
            let mut form = b.zero();
            for block in forms.iter().filter(|f| f.side == side && f.table == table) {
                let mut leaf = beta;
                for (i, c) in machine::slot(table, block.slot).iter().enumerate() {
                    leaf = weighted_coord(b, weights[1 + i], c, &values, leaf);
                }
                form = b.mul_add(block.selector, leaf, form);
            }
            summand = if side == 0 {
                b.add(form, summand)
            } else {
                b.mul_add(xi, form, summand)
            };
        }
        for id in machine::identities(table) {
            let mut v = b.e_const(id.constant);
            for (c, &coef) in id.coeffs.iter().enumerate() {
                if !coef.is_zero() {
                    v = b.mul_const_add(values[c], coef, v);
                }
            }
            for &(x, y, coef) in &id.prods {
                let p = b.mul(values[x], values[y]);
                v = b.mul_const_add(p, coef, v);
            }
            summand = b.mul_add(power, v, summand);
            power = b.mul(power, xi);
        }
        let w = air_weights[ti].unwrap_or_else(|| b.one());
        residual = b.mul_add(w, summand, residual);
        values_all.push(values);
    }
    b.scope("final", |b| b.eq_e(claim, residual));
    (chi, values_all)
}
