//! Phase 4, the table sumcheck (`NativeVm/Model/Tables.lean`), and phase 5, the public input
//! (`NativeVm/Model/PublicInput.lean`).

use crate::buf::Buf;
use crate::bus::BusW;
use crate::data::TABLES;
use crate::field::{EW, ONE, ZERO, dot, multilinear_eval, powers};
use crate::gkr::N_TREES;
use crate::layout::{FormBuf, LayoutW, MEMORY_0, MEMORY_1, N_TABLES, constraints_w, evaluate, global_column_base};
use crate::stack::{ClaimsW, push_claim};
use crate::transcript::{TState, grinding_bits, require};

/// `tablePointCap`: a table's point, at most `30` coordinates.
pub const TABLE_POINT_CAP: usize = 30;
/// `widthCap`: the widest table, `KECCAK`'s.
pub const WIDTH_CAP: usize = 92;
/// The constraints of every table (`JUMP`'s two).
const N_CONSTRAINTS: usize = 2;

/// `EvalsAt`'s entry: a table's point and its evaluations.
#[repr(C)]
pub struct TableEvalW {
    pub point: Buf<EW, TABLE_POINT_CAP>,
    pub values: Buf<EW, WIDTH_CAP>,
}

/// `tableWeights`: coordinate `v` contributes `1 + equality_point[v] + r_v` to a table taller
/// than `v`, `r_v` to the others.
#[inline(never)]
fn table_weights(heights: &[usize; N_TABLES], equality_point: &[EW], point: &[EW]) -> [EW; N_TABLES] {
    let mut weights = [ONE; N_TABLES];
    for (coord, &challenge) in point.iter().enumerate() {
        let equality = ONE + equality_point.get(coord).copied().unwrap_or(ZERO) + challenge;
        for (w, &h) in weights.iter_mut().zip(heights) {
            *w = *w * if coord < h { equality } else { challenge };
        }
    }
    weights
}

/// `tableTerms`: each table's evaluations read (`tableTermsStep`), its weighted terms added to the
/// final sum; each table's point and evaluations into `evals`.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn table_terms(
    t: &mut TState,
    constraint_powers: &[EW],
    form_powers: &[EW],
    point: &[EW],
    heights: &[usize; N_TABLES],
    forms: &[[FormBuf; 3]; N_TABLES],
    weights: &[EW; N_TABLES],
    evals: &mut [TableEvalW; N_TABLES],
) -> Option<EW> {
    let (mut cursor, mut final_sum) = (0usize, ZERO);
    for (i, table) in TABLES.iter().enumerate() {
        let out = evals.get_mut(i)?;
        let evaluations = out.values.resize(table.width)?;
        t.read_scalars(evaluations)?;
        let mut constraints = [ZERO; N_CONSTRAINTS];
        let n = constraints_w(table.opcode, evaluations, &mut constraints);
        let powers = constraint_powers.get(cursor..).unwrap_or(&[]);
        let powers = powers.get(..table.n_constraints).unwrap_or(powers);
        let summand = dot(powers, constraints.get(..n)?);
        let row = forms.get(i)?;
        let mut form_values = [ZERO; 3];
        for (v, f) in form_values.iter_mut().zip(row) {
            *v = evaluate(f.terms(), evaluations);
        }
        final_sum = final_sum + *weights.get(i)? * (summand + dot(form_powers, &form_values));
        let h = *heights.get(i)?;
        out.point.set(point.get(..h).unwrap_or(point))?;
        cursor += table.n_constraints;
    }
    Some(final_sum)
}

/// `tableSumcheck`.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn table_sumcheck(
    t: &mut TState,
    heights: &[usize; N_TABLES],
    bus: &BusW,
    constraint_powers: &[EW],
    form_powers: &[EW],
    target: EW,
    evals: &mut [TableEvalW; N_TABLES],
) -> Option<()> {
    let n_rounds = heights.iter().fold(0, |m, &h| m.max(h));
    let mut challenges = [ZERO; TABLE_POINT_CAP];
    let challenges = challenges.get_mut(..n_rounds)?;
    let claim = t.sumcheck_plain(target, 4, challenges)?;
    challenges.reverse();
    let point = &*challenges;
    let weights = table_weights(heights, bus.point.as_slice(), point);
    let final_sum = table_terms(t, constraint_powers, form_powers, point, heights, &bus.forms, &weights, evals)?;
    require(final_sum == claim)
}

/// **Phase 4** (`tablePhase`): each table's point and evaluations into `evals`.
#[inline(never)]
pub fn table_phase(t: &mut TState, layout: &LayoutW, bus: &BusW, evals: &mut [TableEvalW; N_TABLES]) -> Option<()> {
    let n_powers = N_CONSTRAINTS + N_TREES;
    t.grind(grinding_bits(n_powers as u64 - 1))?;
    let xi = t.sample_challenge();
    let mut xi_powers = [ZERO; N_CONSTRAINTS + N_TREES];
    powers(xi, &mut xi_powers);
    let (constraint_powers, form_powers) = xi_powers.split_at(N_CONSTRAINTS);
    let target = dot(form_powers, &bus.totals);
    table_sumcheck(t, &layout.table_log_heights, bus, constraint_powers, form_powers, target, evals)
}

/// `tableColumnClaims`: each table's evaluations at its point, on its global columns, appended.
#[inline(never)]
pub fn table_column_claims(evals: &[TableEvalW; N_TABLES], claims: &mut ClaimsW) -> Option<()> {
    for (t, e) in evals.iter().enumerate() {
        let base = global_column_base(t);
        for (column, &value) in e.values.as_slice().iter().enumerate() {
            push_claim(claims, base + column, e.point.as_slice(), value)?;
        }
    }
    Some(())
}

/// **Phase 5** (`publicInputPhase`): the two memory columns' claims at `(c, 0, …, 0)`, appended.
#[inline(never)]
pub fn public_input_phase(t: &mut TState, layout: &LayoutW, public_input: &[u64; 4], claims: &mut ClaimsW) -> Option<()> {
    let public_challenge = t.sample_challenge();
    let limb = |l: usize| {
        multilinear_eval(&[EW::of_k(public_input[l]), EW::of_k(public_input[2 + l])], &[public_challenge])
    };
    let mut point = [ZERO; TABLE_POINT_CAP + 1];
    let n = 1 + layout.placement(MEMORY_0).variable_count.saturating_sub(1);
    let point = point.get_mut(..n)?;
    point[0] = public_challenge;
    push_claim(claims, MEMORY_0, point, limb(0))?;
    push_claim(claims, MEMORY_1, point, limb(1))
}
