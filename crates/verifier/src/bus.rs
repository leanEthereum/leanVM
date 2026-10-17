//! Bus balance and decomposition, then the table sumcheck.

use crate::field::{E, ONE, ZERO};
use crate::layout::{
    BUS_BITS, BYTECODE_FINAL_COUNTERS, BusBlock, Form, GLOBAL_COLUMN_BASES, Layout, MEMORY_0, MEMORY_1, MEMORY_2,
    MEMORY_FINAL_COUNTERS, SEP_BYTECODE, SEP_MEM, SEP_STATE, Table, constant, gpow,
};
use crate::multilinear::{Placement, dot, eq_eval, eq_kernel, index_mle, multilinear_eval, poly_eval, stack_offsets};
use crate::transcript::{Transcript, sumcheck};
use crate::{StackClaim, VerifierError, require};

pub(crate) fn verify_gkr_grand_products(
    depth: usize,
    transcript: &mut Transcript,
) -> Result<(E, Vec<E>, Vec<E>), VerifierError> {
    let (shared, count) = (transcript.next_scalar()?, transcript.next_scalar()?);
    let mut point: Vec<E> = Vec::new();
    let mut values = vec![shared, shared, count]; // 3 grand product GKR are batched together: push, pull, count

    let mut layer = depth;
    while layer > 0 {
        // Two levels a step. An odd depth starts with one.
        let step = if layer % 2 == 1 { 1 } else { 2 };
        let combiner = transcript.sample();
        let claim = poly_eval(&values, combiner);
        // The product is degree 2^step, so one more coefficient than that per round.
        let equalities: Vec<Option<E>> = point.iter().copied().map(Some).collect();
        let (x, claim) = sumcheck(transcript, claim, (1 << step) + 1, &equalities)?;

        let children = [
            transcript.next_scalars(1 << step)?,
            transcript.next_scalars(1 << step)?,
            transcript.next_scalars(1 << step)?,
        ];
        if transcript.checked() {
            let products = children
                .each_ref()
                .map(|child| child.iter().fold(ONE, |acc, &value| acc * value));
            require(claim == poly_eval(&products, combiner), VerifierError::GkrLayer(layer))?;
        }

        let y = transcript.samples(step);
        values.clear();
        for child in &children {
            values.push(multilinear_eval(child, &y)?);
        }
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
        .map(|(&variables, index)| Placement {
            variables,
            index,
            low: 0,
        })
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
    pub fn on_stack(&self, layout: &Layout) -> StackClaim<'static> {
        let point = layout.placements[self.column].stack_point(&self.point, layout.stack_log);
        (Box::new(move |x| eq_eval(&point, x)), self.value)
    }
}

/// One side of the bus: its blocks, their layout, its framework fingerprints, its tuple weights and its beta.
type Side<'a> = (&'a [BusBlock], &'a BusLayout, Vec<E>, &'a [E], E);

pub struct BusResult {
    pub claims: Vec<ColumnClaim>,
    pub bytecode_point: Vec<E>, // where the bus reads the stacked bytecode: zeta's low coordinates, then alpha
    pub point: Vec<E>,          // the GKR point zeta, which the table sumcheck reuses
    pub forms: Vec<Vec<Form>>,  // forms[table][side]
    pub totals: Vec<E>,         // what the tables owe each side, derived
}

pub fn verify_bus_balance(layout: &Layout, transcript: &mut Transcript) -> Result<BusResult, VerifierError> {
    let framework_log_rows = [0, layout.log_memory, layout.log_bytecode]; // state, memory, bytecode
    let push_layout = bus_layout(&framework_log_rows, &layout.push);
    let pull_layout = bus_layout(&framework_log_rows, &layout.pull);
    let count_layout = bus_layout(&[], &layout.count);

    let alphas = transcript.samples(BUS_BITS);
    let weights = eq_kernel(&alphas);
    let beta = transcript.sample();
    let (count_root, point, tree_values) = verify_gkr_grand_products(push_layout.depth, transcript)?;
    if transcript.checked() {
        require(count_root != ZERO, VerifierError::BusCountZero)?;
    }

    // The framework blocks' committed columns, in the order the two sides first
    // name them: the memory image on push, then each array's final count on pull.
    let memory_low = &point[..layout.log_memory];
    let bytecode_low = &point[..layout.log_bytecode];
    let memory = transcript.next_scalars(3)?;
    let memory_final = transcript.next_scalar()?;
    let bytecode_final = transcript.next_scalar()?;
    let claim = |column: usize, point: &[E], value: E| ColumnClaim {
        column,
        point: point.to_vec(),
        value,
    };
    let mut claims: Vec<ColumnClaim> = [MEMORY_0, MEMORY_1, MEMORY_2]
        .map(|column| claim(column, memory_low, memory[column]))
        .into();
    claims.push(claim(MEMORY_FINAL_COUNTERS, memory_low, memory_final));
    claims.push(claim(BYTECODE_FINAL_COUNTERS, bytecode_low, bytecode_final));
    let memory_index = index_mle(memory_low);
    let bytecode_index = index_mle(bytecode_low);
    let bytecode_point = [bytecode_low, &alphas].concat();
    // A replay leaves the one pass over the table out: the value only feeds the table sumcheck's target, which it does not check.
    let bytecode_value = if transcript.checked() {
        layout.bytecode.evaluate(&bytecode_point)?
    } else {
        ZERO
    };

    // The three framework tuples, each its coordinates weighted by eq(alpha, .); slots past the ones
    // named are zero. A side differs only here: push seeds each array at count one, pull finalizes it
    // with the committed final count and ends at the last pc. Both boundaries sit in frame 0.
    let fingerprints = |pc: E, memory_count: E, bytecode_count: E| {
        vec![
            dot(&weights[..3], &[SEP_STATE, pc, gpow(0)]),
            dot(
                &weights[..6],
                &[SEP_MEM, memory_index, memory_count, memory[0], memory[1], memory[2]],
            ),
            dot(&weights[..3], &[SEP_BYTECODE, bytecode_index, bytecode_count]) + bytecode_value,
        ]
    };

    let final_pc = gpow((1 << layout.log_bytecode) - 1); // the execution ends at the bytecode's last instruction
    let sides: [Side; 3] = [
        (
            &layout.push,
            &push_layout,
            fingerprints(gpow(0), ONE, ONE),
            &weights,
            beta,
        ),
        (
            &layout.pull,
            &pull_layout,
            fingerprints(final_pc, memory_final, bytecode_final),
            &weights,
            beta,
        ),
        (&layout.count, &count_layout, vec![], &[ONE], ZERO), // The count channel owns no framework block and runs at alpha = beta = 0.
    ];
    let mut totals = Vec::new(); // what remains to be proven by the next table sumcheck
    let mut forms = vec![vec![Form::default(); 3]; layout.tables.len()];
    for (side, (blocks, side_layout, framework_fingerprints, side_weights, side_beta)) in sides.into_iter().enumerate()
    {
        let framework_selectors: Vec<E> = side_layout.framework.iter().map(|p| p.eq_above(&point)).collect();
        let table_selectors: Vec<E> = side_layout.tables.iter().map(|p| p.eq_above(&point)).collect();
        let shifted: Vec<E> = framework_fingerprints.iter().map(|&f| side_beta + f).collect();
        let known = dot(&framework_selectors, &shifted);
        // A table's blocks stay symbolic: they accumulate into the form its sumcheck settles over its own columns.
        let beta_form = constant(side_beta);
        for (&selector, block) in table_selectors.iter().zip(blocks) {
            let form = &mut forms[block.owner][side];
            form.add_scaled(&beta_form, selector);
            for (slot, coordinate) in block.coordinates.iter().enumerate() {
                form.add_scaled(coordinate, selector * side_weights[slot]); // the fingerprint, one tuple slot at a time
            }
        }
        // Every occupied row holds beta + its fingerprint; the rest of the leaf cube holds 1.
        let ones_padding = E::sum(framework_selectors.into_iter().chain(table_selectors)) + ONE;
        totals.push(tree_values[side] + known + ones_padding); // what the forms owe: the GKR value, less framework and padding
    }

    Ok(BusResult {
        claims,
        bytecode_point,
        point,
        forms,
        totals,
    })
}

pub fn table_sumcheck(
    tables: &[Table],
    table_log_heights: &[usize],
    bus_forms: &[Vec<Form>],
    constraint_powers: &[E],
    form_powers: &[E],
    equality_point: &[E],
    target: E,
    transcript: &mut Transcript,
) -> Result<Vec<ColumnClaim>, VerifierError> {
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

    let mut claims = Vec::new();
    let mut rows = Vec::with_capacity(tables.len());
    for (table, &height) in tables.iter().zip(table_log_heights) {
        let evaluations = transcript.next_scalars(table.width())?;
        let table_point = &point[..height];
        claims.extend(evaluations.iter().enumerate().map(|(local, &value)| ColumnClaim {
            column: GLOBAL_COLUMN_BASES[table.opcode] + local,
            point: table_point.to_vec(),
            value,
        }));
        rows.push(evaluations);
    }
    if transcript.checked() {
        let mut terminal = ZERO;
        let mut cursor = 0;
        for (((table, evaluations), forms), &weight) in tables.iter().zip(&rows).zip(bus_forms).zip(&weights) {
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
    Ok(claims)
}
