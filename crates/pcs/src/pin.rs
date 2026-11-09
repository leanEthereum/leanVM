//! The level-0 list pin.
//!
//! The level-0 commitment takes no OOD sample of its own, so it binds a list of up to `L_0` stacks. Right after its
//! root, the caller pins that list: grind [`OOD_GRINDING_BITS`], sample `z` of `m` coordinates, then, for each
//! aligned block of the committed lanes (the binary expansion of their count, largest block first, `m` the largest
//! block's variables), send the block's MLE at `z`'s first coordinates. Two list members that differ on the committed
//! lanes differ on some block, so they collide there with probability at most `m / q`: the pin fails with at most
//! `C(L_0, 2) m / q`, and every later challenge faces one candidate. Every claim's weight vanishes past the committed
//! lanes, so members that agree on them answer every claim alike.
//!
//! Each block's value becomes a [`StackClaim::Point`], discharged with the other point claims by the stacked opening.

use fiat_shamir::transcript::ProverState;
use primitives::field::F64;
use primitives::multilinear::mle_eval_par;

use crate::stack_open::StackClaim;
use crate::whir_config::OOD_GRINDING_BITS;

/// The pin's blocks `(offset, variables)` over `n_lanes` committed lanes of `2^lane_vars` words, largest first.
pub fn blocks(n_lanes: usize, lane_vars: usize) -> Vec<(usize, usize)> {
    let mut offset = 0;
    (0..usize::BITS as usize)
        .rev()
        .filter(|&bit| n_lanes >> bit & 1 == 1)
        .map(|bit| {
            let block = (offset, lane_vars + bit);
            offset += 1 << (lane_vars + bit);
            block
        })
        .collect()
}

/// Pin the list of the level-0 commitment to `stack`, the committed lanes of a `2^log_n`-word stack whose lanes
/// are `2^(log_n - initial_k)` words; call it right after the root is sent. Returns the point claims the stacked
/// opening must discharge, in the order their values were sent.
pub fn pin_commitment(ps: &mut ProverState, stack: &[F64], log_n: usize, initial_k: usize) -> Vec<StackClaim> {
    let lane_vars = log_n - initial_k;
    let n_lanes = stack.len() >> lane_vars;
    assert!(
        n_lanes >= 1 && stack.len() == n_lanes << lane_vars,
        "the stack is whole lanes"
    );
    let blocks = blocks(n_lanes, lane_vars);
    ps.grind(OOD_GRINDING_BITS as u32);
    let z = ps.sample_vec(blocks[0].1);
    let _span = tracing::info_span!("Pin").entered();
    blocks
        .into_iter()
        .map(|(offset, vars)| {
            let low_point = z[..vars].to_vec();
            let value = mle_eval_par(&stack[offset..offset + (1 << vars)], &low_point);
            ps.add_scalar(value);
            StackClaim::Point {
                offset,
                low_point,
                value,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::F128;
    use primitives::test_rng::Rng;

    #[test]
    fn blocks_are_the_binary_expansion_largest_first() {
        assert_eq!(blocks(48, 10), vec![(0, 15), (32 << 10, 14)]);
        assert_eq!(blocks(64, 9), vec![(0, 15)]);
        assert_eq!(blocks(7, 3), vec![(0, 5), (32, 4), (48, 3)]);
    }

    /// Each value is its block's MLE at the sampled point, written out one eq weight at a time.
    #[test]
    fn values_are_the_block_evaluations() {
        let mut rng = Rng::new(0x919);
        let (log_n, initial_k) = (16, 6);
        let stack: Vec<F64> = (0..13 << (log_n - initial_k)).map(|_| F64(rng.next_u64())).collect();
        let mut ps = ProverState::new([F64(1); 4], [F64(2); 4]);
        let claims = pin_commitment(&mut ps, &stack, log_n, initial_k);
        assert_eq!(claims.len(), 3);
        for claim in &claims {
            let StackClaim::Point {
                offset,
                low_point,
                value,
            } = claim;
            let naive: F128 = (0..1usize << low_point.len())
                .map(|j| {
                    let eq = low_point.iter().enumerate().fold(F128::ONE, |w, (i, &p)| {
                        w * if (j >> i) & 1 == 1 { p } else { F128::ONE + p }
                    });
                    eq.mul_base(stack[offset + j])
                })
                .sum();
            assert_eq!(*value, naive);
        }
    }
}
