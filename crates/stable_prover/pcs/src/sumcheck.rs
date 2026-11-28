//! The sumcheck of a product of two tables.

use primitives::field::{F128, mul};
use primitives::multilinear::fold;
use primitives::transcript::ProverState;

/// The sumcheck of `scale * sum of a * b` over the row index, rows of `width`, its lowest variable first, down to one
/// row of each: returns those rows and the point. A round sends its constant and `X^2` coefficients; the running claim
/// fixes the linear one.
pub fn product_sumcheck(
    ps: &mut ProverState,
    mut a: Vec<F128>,
    mut b: Vec<F128>,
    width: usize,
    scale: F128,
) -> (Vec<F128>, Vec<F128>, Vec<F128>) {
    let mut point = Vec::new();
    while a.len() > width {
        let (mut zero, mut infinity) = (F128::ZERO, F128::ZERO);
        for (a, b) in a.chunks_exact(2 * width).zip(b.chunks_exact(2 * width)) {
            let ((a0, a1), (b0, b1)) = (a.split_at(width), b.split_at(width));
            for (((&a0, &a1), &b0), &b1) in a0.iter().zip(a1).zip(b0).zip(b1) {
                zero += a0 * b0;
                infinity += (a0 + a1) * (b0 + b1);
            }
        }
        ps.add_round_poly(&[mul(scale, zero), F128::ZERO, mul(scale, infinity)], false);
        let challenge = ps.sample();
        point.push(challenge);
        a = fold(&a, width, challenge);
        b = fold(&b, width, challenge);
    }
    (a, b, point)
}
