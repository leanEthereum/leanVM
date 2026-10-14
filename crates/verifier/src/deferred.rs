//! The claims an aggregate defers to its outermost verifier, on polynomials fixed by the protocol (doc/leanvm, "Deferred evaluation claims").
//!
//! The stacked bytecode is the first, evaluated by [`crate::Bytecode::evaluate`]. The other two are flock's matrices.

use crate::field::E;
use crate::flock::blake2s_row_values;
use crate::layout::BLAKE2S_R1CS_LOG_SIZE;
use crate::multilinear::{eq_kernel, multilinear_eval};
use crate::{VerifierError, require};

/// The multilinear extensions of `A0` and `B0` at `point`: the row coordinates, then the column coordinates.
///
/// The same forward walk of the BLAKE2s circuit as the lincheck's terminal check, against eq weights on both sides.
pub fn matrix_values(point: &[E]) -> Result<(E, E), VerifierError> {
    require(point.len() == 2 * BLAKE2S_R1CS_LOG_SIZE, VerifierError::MultilinearSize)?;
    let (row, column) = point.split_at(BLAKE2S_R1CS_LOG_SIZE);
    let (left_values, right_values) = blake2s_row_values(&eq_kernel(column));
    Ok((
        multilinear_eval(&left_values, row)?,
        multilinear_eval(&right_values, row)?,
    ))
}
