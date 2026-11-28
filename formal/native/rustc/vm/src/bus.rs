//! Phase 3: the bus (`NativeVm/Model/Bus.lean`).

use crate::buf::Buf;
use crate::data::{COUNT_BLOCKS, PULL_BLOCKS, PUSH_BLOCKS, TABLES};
use crate::field::{EW, GEN, ONE, ZERO, dot, eq_kernel, gpow, index_mle, multilinear_eval_by, padding_weight};
use crate::gkr::{BUS_POINT_CAP, GkrStateW, N_TREES, verify_gkr_grand_products};
use crate::layout::{
    BUS_BITS, BYTECODE_FINAL_COUNTERS, Block, FormBuf, LayoutW, MEMORY_0, MEMORY_1, MEMORY_FINAL_COUNTERS, N_TABLES,
    Placement, eq_above, evaluate, form_terms, stack_offsets, tuple_forms,
};
use crate::stack::{ClaimsW, push_claim};
use crate::transcript::{TState, grinding_bits, require};

/// The most table blocks on a side, the push side's.
const MAX_BLOCKS: usize = PUSH_BLOCKS.len();

/// `BusLayoutW`: a side's depth, the framework blocks' placements, the table blocks'.
#[repr(C)]
struct BusLayoutW {
    depth: usize,
    framework: Buf<Placement, 3>,
    tables: Buf<Placement, MAX_BLOCKS>,
}

/// `busLayout frameworkLogRows blocks`.
#[inline(never)]
fn bus_layout(framework_log_rows: &[usize], blocks: &[Block], layout: &LayoutW) -> Option<BusLayoutW> {
    let mut sizes = [0usize; 3 + MAX_BLOCKS];
    let n = framework_log_rows.len() + blocks.len();
    let sizes = sizes.get_mut(..n)?;
    let (head, tail) = sizes.split_at_mut_checked(framework_log_rows.len())?;
    for (slot, &s) in head.iter_mut().zip(framework_log_rows) {
        *slot = s;
    }
    for (slot, block) in tail.iter_mut().zip(blocks) {
        *slot = layout.block_rows(block.owner).0;
    }
    let mut offsets = [0u64; 3 + MAX_BLOCKS];
    let depth = stack_offsets(sizes, &mut offsets)?;
    let mut out = BusLayoutW { depth, framework: Buf { len: 0, items: [Placement::default(); 3] }, tables: Buf { len: 0, items: [Placement::default(); MAX_BLOCKS] } };
    for (i, (&size, &offset)) in sizes.iter().zip(&offsets).enumerate() {
        let p = Placement { variable_count: size, index: offset };
        if i < framework_log_rows.len() { out.framework.push(p)? } else { out.tables.push(p)? }
    }
    Some(out)
}

/// `BusAt`: the bus's result phase 4 reads, each table's form per side, the GKR point, the totals.
/// The column claims go to the claims; the bytecode point no later phase reads.
#[repr(C)]
pub struct BusW {
    pub forms: [[FormBuf; 3]; N_TABLES],
    pub point: Buf<EW, BUS_POINT_CAP>,
    pub totals: [EW; N_TREES],
}

/// `sepStateW`, `sepMemW`.
const SEP_STATE: EW = ONE;
const SEP_MEM: EW = GEN;

/// `fingerprints`: the boundary state's, the memory cell's and the bytecode tuple's.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn fingerprints(
    weights: &[EW],
    memory: &[EW; 2],
    memory_low: &[EW],
    bytecode_low: &[EW],
    bytecode_share: EW,
    pc: EW,
    memory_count: EW,
    bytecode_count: EW,
) -> [EW; 3] {
    let w = |n: usize| weights.get(..n).unwrap_or(weights);
    [
        dot(w(3), &[SEP_STATE, pc, gpow(0)]),
        dot(w(5), &[SEP_MEM, index_mle(memory_low), memory_count, memory[0], memory[1]]),
        dot(w(3), &[gpow(2), index_mle(bytecode_low), bytecode_count]) + bytecode_share,
    ]
}

/// `blockForm`: `side_beta` plus the block's fingerprint, a tuple slot at a time, into `form`.
#[inline(never)]
fn block_form(block: &Block, side_weights: &[EW], side_beta: EW, form: &mut FormBuf) -> Option<()> {
    form.set_const(side_beta);
    for (slot, coordinate) in tuple_forms(block.tuple).enumerate() {
        form.add_scaled(form_terms(coordinate), side_weights.get(slot).copied().unwrap_or(ZERO))?;
    }
    Some(())
}

/// `accumulateSide`: the side's table blocks added to `forms`; the side's total.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn accumulate_side(
    forms: &mut [[FormBuf; 3]; N_TABLES],
    side: usize,
    blocks: &[Block],
    layout: &LayoutW,
    side_layout: &BusLayoutW,
    framework_fingerprints: &[EW],
    side_weights: &[EW],
    side_beta: EW,
    point: &[EW],
    tree_value: EW,
) -> Option<EW> {
    let framework = side_layout.framework.as_slice();
    let mut known = ZERO;
    let mut ones_padding = ONE;
    for (&p, &fp) in framework.iter().zip(framework_fingerprints) {
        known = known + eq_above(p, point) * (side_beta + fp);
    }
    for &p in framework {
        ones_padding = ones_padding + eq_above(p, point);
    }
    let mut padding_rows = ZERO;
    let mut form = FormBuf { len: 0, terms: [crate::layout::TermW { degree: 0, cols: [0, 0], coeff: ZERO }; crate::layout::FORM_CAP] };
    for (&p, block) in side_layout.tables.as_slice().iter().zip(blocks) {
        let selector = eq_above(p, point);
        ones_padding = ones_padding + selector;
        block_form(block, side_weights, side_beta, &mut form)?;
        let padding = TABLES.get(block.owner)?.padding();
        forms.get_mut(block.owner)?.get_mut(side)?.add_scaled(form.terms(), selector)?;
        let (log_rows, rows) = layout.block_rows(block.owner);
        let low = point.get(..log_rows).unwrap_or(point);
        padding_rows = padding_rows + selector * padding_weight(low, rows) * (evaluate(form.terms(), padding) + ONE);
    }
    Some(tree_value + known + ones_padding + padding_rows)
}

/// `bytecodeShare`: the share, its sumcheck over the slot, the value; the bytecode point into
/// `point` (its length returned), the share and the value.
#[inline(never)]
fn bytecode_share(
    t: &mut TState,
    weights: &[EW],
    bytecode_low: &[EW],
    point: &mut [EW; BUS_POINT_CAP + BUS_BITS],
) -> Option<(EW, usize, EW)> {
    let share = t.read_scalar()?;
    let mut slot_point = [ZERO; BUS_BITS];
    let claim = t.sumcheck_plain(share, 3, &mut slot_point)?;
    let value = t.read_scalar()?;
    let mut kernel = [ZERO; 1 << BUS_BITS];
    eq_kernel(&slot_point, &mut kernel)?;
    require(claim == dot(&kernel, weights) * value)?;
    let n = bytecode_low.len() + BUS_BITS;
    let (head, tail) = point.get_mut(..n)?.split_at_mut_checked(bytecode_low.len())?;
    for (slot, &v) in head.iter_mut().zip(bytecode_low) {
        *slot = v;
    }
    for (slot, &v) in tail.iter_mut().zip(&slot_point) {
        *slot = v;
    }
    Some((share, n, value))
}

/// `computedBytecodeValue`: the bytecode's multilinear extension at the point is the value.
#[inline(never)]
fn computed_bytecode_value(words: &[u64], point: &[EW], value: EW) -> Option<()> {
    let at = |i: usize| EW::of_k(words.get(i).copied().unwrap_or(0));
    require(multilinear_eval_by(words.len(), at, point) == value)
}

/// **Phase 3** (`verifyBusBalance`): the bus's result into `bus`, its four column claims appended
/// to `claims`.
#[inline(never)]
pub fn verify_bus_balance(
    t: &mut TState,
    layout: &LayoutW,
    bytecode: &[u64],
    bus: &mut BusW,
    claims: &mut ClaimsW,
) -> Option<()> {
    let framework_log_rows = [0, layout.log_memory, layout.log_bytecode];
    let push_layout = bus_layout(&framework_log_rows, &PUSH_BLOCKS, layout)?;
    let pull_layout = bus_layout(&framework_log_rows, &PULL_BLOCKS, layout)?;
    let count_layout = bus_layout(&[], &COUNT_BLOCKS, layout)?;
    require(push_layout.depth < 64)?;
    t.grind(grinding_bits(1u64 << push_layout.depth))?;
    let mut weights = [ZERO; 1 << BUS_BITS];
    t.sample_challenges(&mut weights);
    let beta = t.sample_challenge();
    let mut gkr = GkrStateW { values: [ZERO; N_TREES], point: Buf { len: 0, items: [ZERO; BUS_POINT_CAP] } };
    let count_root = verify_gkr_grand_products(t, push_layout.depth, &mut gkr)?;
    require(count_root != ZERO)?;
    let point = gkr.point.as_slice();
    let memory_low = point.get(..layout.log_memory).unwrap_or(point);
    let bytecode_low = point.get(..layout.log_bytecode).unwrap_or(point);
    let mut memory = [ZERO; 2];
    t.read_scalars(&mut memory)?;
    let memory_final = t.read_scalar()?;
    let bytecode_final = t.read_scalar()?;
    claims.clear();
    push_claim(claims, MEMORY_0, memory_low, memory[0])?;
    push_claim(claims, MEMORY_1, memory_low, memory[1])?;
    push_claim(claims, MEMORY_FINAL_COUNTERS, memory_low, memory_final)?;
    push_claim(claims, BYTECODE_FINAL_COUNTERS, bytecode_low, bytecode_final)?;
    let mut bytecode_point = [ZERO; BUS_POINT_CAP + BUS_BITS];
    let (share, n, value) = bytecode_share(t, &weights, bytecode_low, &mut bytecode_point)?;
    computed_bytecode_value(bytecode, bytecode_point.get(..n)?, value)?;
    let fp = |pc, memory_count, bytecode_count| {
        fingerprints(&weights, &memory, memory_low, bytecode_low, share, pc, memory_count, bytecode_count)
    };
    let pc_final = gpow((1u64 << layout.log_bytecode) - 1);
    for row in bus.forms.iter_mut() {
        for form in row.iter_mut() {
            form.clear();
        }
    }
    let tree = gkr.values;
    let total0 = accumulate_side(
        &mut bus.forms, 0, &PUSH_BLOCKS, layout, &push_layout, &fp(gpow(0), ONE, ONE), &weights, beta, point, tree[0],
    )?;
    let total1 = accumulate_side(
        &mut bus.forms,
        1,
        &PULL_BLOCKS,
        layout,
        &pull_layout,
        &fp(pc_final, memory_final, bytecode_final),
        &weights,
        beta,
        point,
        tree[1],
    )?;
    let total2 = accumulate_side(&mut bus.forms, 2, &COUNT_BLOCKS, layout, &count_layout, &[], &[ONE], ZERO, point, tree[2])?;
    bus.point.set(point)?;
    bus.totals = [total0, total1, total2];
    Some(())
}
