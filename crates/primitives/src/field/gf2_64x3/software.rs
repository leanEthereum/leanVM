use super::{F192, F192Unreduced};
use crate::field::gf2_64::software::clmul;

/// Schoolbook: nine base products into the five coefficients of y^0..y^4, then the y-fold.
pub fn mul_unreduced(a: F192, b: F192) -> F192Unreduced {
    let (a, b) = ([a.c0, a.c1, a.c2], [b.c0, b.c1, b.c2]);
    let mut e = [0u128; 5];
    // a_i * b_j lands on y^(i + j).
    for i in 0..3 {
        for j in 0..3 {
            e[i + j] ^= clmul(a[i], b[j]);
        }
    }
    // y^3 = y + 1 and y^4 = y^2 + y.
    F192Unreduced::from_wide([e[0] ^ e[3], e[1] ^ e[3] ^ e[4], e[2] ^ e[4]])
}

pub fn mul(a: F192, b: F192) -> F192 {
    mul_unreduced(a, b).reduce()
}
