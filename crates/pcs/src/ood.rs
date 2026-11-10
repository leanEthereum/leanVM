//! The level-0 commitment's OOD sample.
//!
//! The level-0 commitment takes no OOD points inside the opening, so on its own it binds a list of up to `L_0`
//! stacks. Right after its root, the caller takes its OOD sample: grind [`OOD_GRINDING_BITS`], sample `z` of the
//! stack's `m` variables, then send the stack's MLE at `z`. Two list members that differ collide there with
//! probability at most `m / q`: the sample fails to bind with at most `C(L_0, 2) m / q`, and every later challenge
//! faces one candidate.
//!
//! The value becomes a [`StackClaim::Point`] over the whole stack, which joins the stacked opening's claims last.

use fiat_shamir::transcript::ProverState;
use primitives::field::F64;
use primitives::multilinear::mle_eval_par;

use crate::stack_open::StackClaim;
use crate::whir_config::OOD_GRINDING_BITS;

/// The OOD sample of the level-0 commitment to `stack`, the committed lanes of a `2^log_n`-word stack that is zero
/// past them; call it right after the root is sent. Returns the claim the stacked opening must discharge.
pub fn ood_sample(ps: &mut ProverState, stack: &[F64], log_n: usize) -> StackClaim {
    ps.grind(OOD_GRINDING_BITS);
    let low_point = ps.sample_vec(log_n);
    let value = tracing::info_span!("OOD").in_scope(|| mle_eval_par(stack, &low_point));
    ps.add_scalar(value);
    StackClaim::Point {
        offset: 0,
        low_point,
        value,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::F128;
    use primitives::test_rng::Rng;

    /// The value is the zero-padded stack's MLE at the sampled point, written out one eq weight at a time.
    #[test]
    fn value_is_the_padded_stack_evaluation() {
        let mut rng = Rng::new(0x919);
        let (log_n, lane_vars) = (16, 10);
        let stack: Vec<F64> = (0..13 << lane_vars).map(|_| F64(rng.next_u64())).collect();
        let mut ps = ProverState::new([F64(1); 4], [F64(2); 4]);
        let StackClaim::Point {
            offset,
            low_point,
            value,
        } = ood_sample(&mut ps, &stack, log_n);
        assert_eq!((offset, low_point.len()), (0, log_n));
        let naive: F128 = stack
            .iter()
            .enumerate()
            .map(|(j, &word)| {
                let eq = low_point.iter().enumerate().fold(F128::ONE, |w, (i, &p)| {
                    w * if (j >> i) & 1 == 1 { p } else { F128::ONE + p }
                });
                eq.mul_base(word)
            })
            .sum();
        assert_eq!(value, naive);
    }
}
