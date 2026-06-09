use crate::DIMENSION;
use crate::EF;
use crate::F;
use crate::MemoryAccess;
use crate::RunnerError;
use crate::TableTrace;
use crate::tables::extension_op::{EXT_OP_FLAG_BE, EXT_OP_LEN_MULTIPLIER, ExtensionOp, air::*};
use backend::*;

fn compute_elem(v_a: EF, v_b: EF, op: ExtensionOp) -> EF {
    match op {
        ExtensionOp::Add => v_a + v_b,
        ExtensionOp::DotProduct => v_a * v_b,
        // eq: a*b + (1-a)*(1-b)
        ExtensionOp::Eq => (v_a * v_b).double() - v_a - v_b + F::ONE,
    }
}

fn accumulate(elem: EF, acc_tail: EF, op: ExtensionOp) -> EF {
    match op {
        ExtensionOp::Eq => elem * acc_tail,
        ExtensionOp::Add | ExtensionOp::DotProduct => elem + acc_tail,
    }
}

/// For single-element Add/Mul ops, solve for an unknown operand when the result is known.
/// A op B = C: if A unknown, A = C inv_op B; if B unknown, B = C inv_op A.
fn solve_unknowns(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    flag_be: bool,
    op: ExtensionOp,
    memory: &mut impl MemoryAccess,
) -> Result<(), RunnerError> {
    let addr_a = ptr_a.to_usize();
    let addr_b = ptr_b.to_usize();
    let addr_res = ptr_res.to_usize();

    let a = if flag_be {
        memory.get(addr_a).map(EF::from)
    } else {
        memory.get_ef_element(addr_a)
    };
    let b = memory.get_ef_element(addr_b);
    let c = memory.get_ef_element(addr_res);

    if op == ExtensionOp::DotProduct && !flag_be {
        // detect "copy_ef" (single EF-element copy: dot_product_ee against EF::ONE)
        if b == Ok(EF::ONE) {
            memory.make_slices_equal_and_defined(ptr_a.to_usize(), ptr_res.to_usize(), DIMENSION)?;
            return Ok(());
        }
        if a == Ok(EF::ONE) {
            memory.make_slices_equal_and_defined(ptr_b.to_usize(), ptr_res.to_usize(), DIMENSION)?;
            return Ok(());
        }
    }

    match (a, b, c) {
        (Ok(a), Ok(b), Ok(c)) => {
            if compute_elem(a, b, op) != c {
                return Err(RunnerError::InvalidExtensionOp);
            }
        }
        (Ok(_), Ok(_), Err(_)) => {} // result unknown: compute normally
        (Err(_), Ok(b), Ok(c)) => {
            let a = match op {
                ExtensionOp::Add => c - b,
                ExtensionOp::DotProduct => c * b.try_inverse().ok_or(RunnerError::DivByZero)?,
                ExtensionOp::Eq => unreachable!(),
            };
            if flag_be {
                memory.set(addr_a, a.as_base().ok_or(RunnerError::InvalidExtensionOp)?)?;
            } else {
                memory.set_ef_element(addr_a, a)?;
            }
        }
        (Ok(a), Err(_), Ok(c)) => {
            let b = match op {
                ExtensionOp::Add => c - a,
                ExtensionOp::DotProduct => c * a.try_inverse().ok_or(RunnerError::DivByZero)?,
                ExtensionOp::Eq => unreachable!(),
            };
            memory.set_ef_element(addr_b, b)?;
        }
        _ => return Err(RunnerError::InvalidExtensionOp),
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn exec_multi_row(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    flag_be: bool,
    op: ExtensionOp,
    memory: &mut impl MemoryAccess,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    assert!(size >= 1);

    if size == 1 && op != ExtensionOp::Eq {
        solve_unknowns(ptr_a, ptr_b, ptr_res, flag_be, op, memory)?;
    }

    let a_stride = if flag_be { 1 } else { DIMENSION };

    // 1. Read all operands and compute elem values
    let mut elems = Vec::with_capacity(size);
    let mut v_bs = Vec::with_capacity(size);
    let mut idx_as = Vec::with_capacity(size);
    let mut idx_bs = Vec::with_capacity(size);

    for i in 0..size {
        let addr_a = ptr_a.to_usize() + i * a_stride;
        let addr_b = ptr_b.to_usize() + i * DIMENSION;
        let idx_a_f = F::from_usize(addr_a);
        let idx_b_f = F::from_usize(addr_b);

        let v_a = if flag_be {
            EF::from(memory.get(addr_a)?)
        } else {
            memory.get_ef_element(addr_a)?
        };
        let v_b = memory.get_ef_element(addr_b)?;

        elems.push(compute_elem(v_a, v_b, op));
        v_bs.push(v_b);
        idx_as.push(idx_a_f);
        idx_bs.push(idx_b_f);
    }

    // 2. Backward accumulation: compute acc[i] from bottom to top
    let mut accs = vec![EF::ZERO; size];
    accs[size - 1] = elems[size - 1];
    for i in (0..size - 1).rev() {
        accs[i] = accumulate(elems[i], accs[i + 1], op);
    }

    // 3. Write result to memory
    let result = accs[0];
    memory.set_ef_element(ptr_res.to_usize(), result)?;

    // 4. Push trace rows
    let flag_be_f = F::from_bool(flag_be);
    let flag_add_f = F::from_bool(op == ExtensionOp::Add);
    let flag_dot_product_f = F::from_bool(op == ExtensionOp::DotProduct);
    let flag_eq_f = F::from_bool(op == ExtensionOp::Eq);
    let mode_bits = op.flag() + EXT_OP_FLAG_BE * flag_be as usize;

    let result_coords = result.as_basis_coefficients_slice();

    for i in 0..size {
        let is_start = i == 0;
        let current_len = size - i;

        trace.columns[COL_FLAG_BE].push(flag_be_f);
        trace.columns[COL_FLAG_START].push(F::from_bool(is_start));
        trace.columns[COL_FLAG_ADD].push(flag_add_f);
        trace.columns[COL_FLAG_DOT_PRODUCT].push(flag_dot_product_f);
        trace.columns[COL_FLAG_EQ].push(flag_eq_f);
        trace.columns[COL_LEN].push(F::from_usize(current_len));
        trace.columns[COL_IDX_A].push(idx_as[i]);
        trace.columns[COL_IDX_B].push(idx_bs[i]);
        trace.columns[COL_IDX_RES].push(ptr_res);

        // COL_V_A+0..5: filled later by fill_trace_extension_op (push zeros as placeholders)
        for k in 0..DIMENSION {
            trace.columns[COL_V_A + k].push(F::ZERO);
        }
        for (k, &val) in v_bs[i].as_basis_coefficients_slice().iter().enumerate() {
            trace.columns[COL_V_B + k].push(val);
        }
        for (k, &val) in result_coords.iter().enumerate() {
            trace.columns[COL_RES + k].push(val);
        }
        for (k, &val) in accs[i].as_basis_coefficients_slice().iter().enumerate() {
            trace.columns[COL_ACC + k].push(val);
        }

        // Virtual columns
        trace.columns[COL_MULTIPLICITY_EXTENSION_OP].push(F::from_bool(is_start));
        trace.columns[COL_DOMAINSEP_EXTENSION_OP].push(F::from_usize(mode_bits + EXT_OP_LEN_MULTIPLIER * current_len));
    }

    Ok(())
}

/// Fill the v_A columns (5 base field coordinates) after execution
/// by looking up memory at idx_A addresses.
pub fn fill_trace_extension_op(trace: &mut TableTrace, memory: &[F]) {
    let n = trace.columns[COL_IDX_A].len();
    for i in 0..n {
        let addr = trace.columns[COL_IDX_A][i].to_usize();
        for k in 0..DIMENSION {
            trace.columns[COL_V_A + k][i] = memory[addr + k];
        }
    }
}
