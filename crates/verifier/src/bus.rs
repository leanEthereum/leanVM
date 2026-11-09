//! Bus balance and decomposition, then the table sumcheck.

use crate::field::{E, ONE, ZERO};
use crate::layout::{
    BUS_BITS, BYTECODE_FINAL_COUNTERS, BusBlock, Form, KECCAK_MIN_STEPS_LOG, Layout, MEMORY_0, MEMORY_1,
    MEMORY_FINAL_COUNTERS, SEP_BYTECODE, SEP_MEM, SEP_STATE, Table, constant, gpow,
};
use crate::multilinear::{
    Placement, dot, eq_eval, eq_kernel, index_mle, multilinear_eval, padding_weight, poly_eval, stack_offsets,
};
use crate::transcript::{Transcript, grinding_bits, sumcheck};
use crate::{StackClaim, VerifierError, require};

/// The grind before the fingerprint `(weights, beta)`: unequal push and pull multisets pass the product check with
/// probability at most `2^mu / |E|`, `mu` the push depth.
fn bus_grinding_bits(mu: usize) -> u32 {
    grinding_bits(1 << mu)
}

/// The trees the bus GKR batches, in its order: push, pull, then the count tree, weighing the count alone at `beta = 0`.
pub const N_TREES: usize = 3;

/// A GKR round is `eq` times a product of four lines, degree five, and grinds for it. In the last layer its challenge
/// is also a coordinate of zeta, which the table sumcheck's zerocheck reads, one more: six, as many bits.
const _: () = assert!(grinding_bits(4 + 1 + 1) == grinding_bits(4 + 1));
/// The zerocheck reads at least zeta's first two coordinates, the last layer's `y`.
const _: () = assert!(KECCAK_MIN_STEPS_LOG >= 2);

/// The batched GKR over the [`N_TREES`] trees. The stream: the push and pull trees' one root, then the count root;
/// then each layer from the root down: a grind and the combiner, the sumcheck rounds (each its coefficients, its grind
/// and its challenge), every tree's children, a grind and `y`. Returns the count root, the point zeta and the trees'
/// leaf values there.
fn verify_gkr_grand_products(depth: usize, transcript: &mut Transcript) -> Result<(E, Vec<E>, Vec<E>), VerifierError> {
    let (shared, count) = (transcript.next_scalar()?, transcript.next_scalar()?);
    let mut values = vec![shared, shared, count];
    let mut point: Vec<E> = Vec::new();

    let mut layer = depth;
    while layer > 0 {
        // Two levels a step. An odd depth starts with one.
        let step = if layer % 2 == 1 { 1 } else { 2 };
        // The combiner batches the trees' claims, degree N_TREES - 1 in it.
        transcript.grind_check(grinding_bits(N_TREES as u128 - 1))?;
        let combiner = transcript.sample();
        let claim = poly_eval(&values, combiner);
        // The product is degree 2^step, so one more coefficient than that per round.
        let equalities: Vec<Option<E>> = point.iter().copied().map(Some).collect();
        let (x, claim) = sumcheck(transcript, claim, (1 << step) + 1, &equalities)?;

        let children = (0..N_TREES)
            .map(|_| transcript.next_scalars(1 << step))
            .collect::<Result<Vec<_>, _>>()?;
        if transcript.checked() {
            let products: Vec<E> = children
                .iter()
                .map(|child| child.iter().fold(ONE, |acc, &value| acc * value))
                .collect();
            require(claim == poly_eval(&products, combiner), VerifierError::GkrLayer(layer))?;
        }

        // `y`: each child's multilinear is degree `step` in it. The last layer's are zeta's first coordinates, which
        // the table sumcheck's zerocheck also reads, `step` more.
        let last = layer == step;
        transcript.grind_check(grinding_bits((step << usize::from(last)) as u128))?;
        let y = transcript.samples(step);
        values = children
            .iter()
            .map(|child| multilinear_eval(child, &y))
            .collect::<Result<_, _>>()?;
        point = [y, x].concat();
        layer -= step;
    }

    Ok((count, point, values))
}

/// Where a side's blocks sit in the stacked leaf cube. Split by kind because framework coordinates are
/// public, so the verifier evaluates their fingerprints outright, while a table's stay symbolic until its sumcheck.
struct BusLayout {
    depth: usize,              // log2 of the padded cube, so how many layers the side's GKR walks
    framework: Vec<Placement>, // the blocks no table owns, stacked first: boundary state, memory, bytecode (none on the count side)
    tables: Vec<Placement>,    // one per block a table owns, in the side's own block order
}

fn bus_layout(framework_log_rows: &[usize], blocks: &[BusBlock]) -> BusLayout {
    let sizes: Vec<usize> = framework_log_rows
        .iter()
        .copied()
        .chain(blocks.iter().map(|block| block.log_rows))
        .collect();
    let (offsets, depth) = stack_offsets(&sizes);
    let mut framework: Vec<Placement> = sizes
        .iter()
        .zip(offsets)
        .map(|(&variables, index)| Placement { variables, index })
        .collect();
    let tables = framework.split_off(framework_log_rows.len());
    BusLayout {
        depth,
        framework,
        tables,
    }
}

pub struct ColumnClaim {
    pub column: usize,
    pub point: Vec<E>,
    pub value: E,
}

impl ColumnClaim {
    /// `None` for a column nothing commits, whose claim never reaches the stack.
    pub fn on_stack(&self, layout: &Layout) -> Option<StackClaim<'static>> {
        let point = layout.placements[self.column]?.stack_point(&self.point, layout.stack_log);
        Some((Box::new(move |x| eq_eval(&point, x)), self.value))
    }
}

/// One bus tree: its blocks, their layout, its framework fingerprints, its tuple weights and its beta.
type Side<'a> = (&'a [BusBlock], &'a BusLayout, Vec<E>, &'a [E], E);

pub struct BusResult {
    pub claims: Vec<ColumnClaim>,
    pub bytecode_point: Vec<E>, // where the bytecode sumcheck leaves the stacked bytecode: zeta's low coordinates, then its point
    pub point: Vec<E>,          // the GKR point zeta, which the table sumcheck reuses
    pub forms: Vec<Vec<Form>>,  // forms[table][tree]
    pub totals: Vec<E>,         // what the tables owe each tree, derived
}

/// The bus, in stream order: the grind and the fingerprint `(weights, beta)`, a weight per tuple slot; the batched GKR;
/// the framework blocks' committed columns at zeta; the bytecode's share and its sumcheck.
pub fn verify_bus_balance(layout: &Layout, transcript: &mut Transcript) -> Result<BusResult, VerifierError> {
    let framework_log_rows = [0, layout.log_memory, layout.log_bytecode]; // state, memory, bytecode
    let push_layout = bus_layout(&framework_log_rows, &layout.push);
    let pull_layout = bus_layout(&framework_log_rows, &layout.pull);
    let count_layout = bus_layout(&[], &layout.count);
    // The announced sizes' caps keep the depth far below this.
    require(push_layout.depth < 64, VerifierError::AnnouncedTableSizes)?;

    transcript.grind_check(bus_grinding_bits(push_layout.depth))?;
    let weights = transcript.samples(1 << BUS_BITS);
    let beta = transcript.sample();
    let (count_root, point, tree_values) = verify_gkr_grand_products(push_layout.depth, transcript)?;
    if transcript.checked() {
        require(count_root != ZERO, VerifierError::BusCountZero)?;
    }

    // The framework blocks' committed columns, in the order the trees first
    // name them: the memory image on push, then each array's final count on pull.
    let memory_low = &point[..layout.log_memory];
    let bytecode_low = &point[..layout.log_bytecode];
    let memory = transcript.next_scalars(2)?;
    let memory_final = transcript.next_scalar()?;
    let bytecode_final = transcript.next_scalar()?;
    let claim = |column: usize, point: &[E], value: E| ColumnClaim {
        column,
        point: point.to_vec(),
        value,
    };
    let mut claims: Vec<ColumnClaim> = [MEMORY_0, MEMORY_1]
        .map(|column| claim(column, memory_low, memory[column]))
        .into();
    claims.push(claim(MEMORY_FINAL_COUNTERS, memory_low, memory_final));
    claims.push(claim(BYTECODE_FINAL_COUNTERS, bytecode_low, bytecode_final));
    let memory_index = index_mle(memory_low);
    let bytecode_index = index_mle(bytecode_low);

    // The program's share of a bytecode leaf, `sum_x weights[x] P(bytecode_low, x)` over the stacked bytecode's slots,
    // then a sumcheck over `x`, its low bit first, down to one evaluation of `P`, the claim an aggregate defers. A replay
    // leaves the one pass over the table out.
    let bytecode_share = transcript.next_scalar()?;
    let (slot_point, claim) = sumcheck(transcript, bytecode_share, 3, &[None; BUS_BITS])?;
    let bytecode_value = transcript.next_scalar()?;
    let bytecode_point = [bytecode_low, &slot_point].concat();
    if transcript.checked() {
        require(
            claim == dot(&eq_kernel(&slot_point), &weights) * bytecode_value,
            VerifierError::BytecodeShare,
        )?;
        require(
            layout.bytecode.evaluate(&bytecode_point)? == bytecode_value,
            VerifierError::BytecodeValue,
        )?;
    }

    // The three framework tuples, each its coordinates weighted by the slots' weights; slots past the ones
    // named are zero. A side differs only here: push seeds each array at count one, pull finalizes it
    // with the committed final count and ends at the last pc. Both boundaries sit in frame 0.
    let framework = |pc: E, memory_count: E, bytecode_count: E| {
        vec![
            dot(&weights[..3], &[SEP_STATE, pc, gpow(0)]),
            dot(
                &weights[..5],
                &[SEP_MEM, memory_index, memory_count, memory[0], memory[1]],
            ),
            dot(&weights[..3], &[SEP_BYTECODE, bytecode_index, bytecode_count]) + bytecode_share,
        ]
    };

    let final_pc = gpow((1 << layout.log_bytecode) - 1); // the execution ends at the bytecode's last instruction
    let sides: [Side; N_TREES] = [
        (&layout.push, &push_layout, framework(gpow(0), ONE, ONE), &weights, beta),
        (
            &layout.pull,
            &pull_layout,
            framework(final_pc, memory_final, bytecode_final),
            &weights,
            beta,
        ),
        (&layout.count, &count_layout, vec![], &[ONE], ZERO), // The count channel owns no framework block and weighs its count alone, at beta = 0.
    ];

    let mut totals = Vec::new(); // what remains to be proven by the next table sumcheck
    let mut forms = vec![vec![Form::default(); N_TREES]; layout.tables.len()];
    for (side, (blocks, side_layout, framework_fingerprints, side_weights, side_beta)) in sides.into_iter().enumerate()
    {
        let framework_selectors: Vec<E> = side_layout.framework.iter().map(|p| p.eq_above(&point)).collect();
        let table_selectors: Vec<E> = side_layout.tables.iter().map(|p| p.eq_above(&point)).collect();
        let shifted: Vec<E> = framework_fingerprints.iter().map(|&f| side_beta + f).collect();
        let known = dot(&framework_selectors, &shifted);
        // A table's blocks stay symbolic: they accumulate into the form its sumcheck settles over its own columns.
        // That form is summed over the padding rows too, whose leaves hold 1 instead: the difference is public.
        let mut padding_rows = ZERO;
        for (&selector, block) in table_selectors.iter().zip(blocks) {
            let form = &mut forms[block.owner][side];
            let mut block_form = constant(side_beta);
            for (slot, coordinate) in block.coordinates.iter().enumerate() {
                block_form.add_scaled(coordinate, side_weights[slot]); // the fingerprint, one tuple slot at a time
            }
            form.add_scaled(&block_form, selector);
            let padding = &layout.tables[block.owner].padding;
            let weight = padding_weight(&point[..block.log_rows], block.rows);
            padding_rows += selector * weight * (block_form.evaluate(padding) + ONE);
        }
        // The leaves outside every block hold 1.
        let ones_padding = E::sum(framework_selectors.into_iter().chain(table_selectors)) + ONE;
        totals.push(tree_values[side] + known + ones_padding + padding_rows); // what the forms owe: the GKR value, less framework and padding
    }

    Ok(BusResult {
        claims,
        bytecode_point,
        point,
        forms,
        totals,
    })
}

/// A table's point, and its columns' evaluations there.
pub type TableEvaluations = (Vec<E>, Vec<E>);

/// A table sumcheck round is degree three and grinds for it. A challenge that is also a coordinate of the KECCAK
/// table's point, at which the Keccak reduction pins the committed middle states, adds one: four, as many bits.
const _: () = assert!(grinding_bits(3 + 1) == grinding_bits(3));

pub fn table_sumcheck(
    tables: &[Table],
    table_log_heights: &[usize],
    bus_forms: &[Vec<Form>],
    constraint_powers: &[E],
    form_powers: &[E],
    equality_point: &[E],
    target: E,
    transcript: &mut Transcript,
) -> Result<Vec<TableEvaluations>, VerifierError> {
    let n_rounds = table_log_heights.iter().copied().max().unwrap_or(0);
    let (challenges, claim) = sumcheck(transcript, target, 4, &vec![None; n_rounds])?;
    let point: Vec<E> = challenges.into_iter().rev().collect();
    let mut weights = vec![ONE; tables.len()];
    for (variable, &challenge) in point.iter().enumerate() {
        let equality = ONE + equality_point[variable] + challenge;
        for (index, &height) in table_log_heights.iter().enumerate() {
            weights[index] *= if height > variable { equality } else { challenge };
        }
    }

    let mut rows = Vec::with_capacity(tables.len());
    for (table, &height) in tables.iter().zip(table_log_heights) {
        rows.push((point[..height].to_vec(), transcript.next_scalars(table.width())?));
    }
    if transcript.checked() {
        let mut terminal = ZERO;
        let mut cursor = 0;
        for (((table, (_, evaluations)), forms), &weight) in tables.iter().zip(&rows).zip(bus_forms).zip(&weights) {
            let n_constraints = table.n_constraints();
            let summand = dot(
                &constraint_powers[cursor..cursor + n_constraints],
                &(table.constraints)(evaluations),
            );
            let form_values: Vec<E> = forms.iter().map(|form| form.evaluate(evaluations)).collect();
            terminal += weight * (summand + dot(form_powers, &form_values));
            cursor += n_constraints;
        }
        require(terminal == claim, VerifierError::TableSumcheckTerminal)?;
    }
    Ok(rows)
}
