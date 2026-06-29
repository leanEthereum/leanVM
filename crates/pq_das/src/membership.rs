use backend::{BasedVectorSpace, Field, PrimeCharacteristicRing, TwoAdicField};
use lean_vm::{EF, F};

use crate::{Commitment, config::EXT_DEGREE, hashing::Digest};

pub type CheckVector = Vec<[F; EXT_DEGREE]>;

/// Interprets the first five digest coordinates as one quintic-extension element.
fn ext_from_digest(digest: &Digest) -> EF {
    EF::from_basis_coefficients_slice(&digest[..EXT_DEGREE]).unwrap()
}

/// Serializes one quintic-extension element into its five KoalaBear coordinates.
fn coeffs(value: EF) -> [F; EXT_DEGREE] {
    value.as_basis_coefficients_slice().try_into().unwrap()
}

/// Derives the extension-field special-barycentric challenge from public data.
pub fn challenge(commitment: &Commitment) -> EF {
    ext_from_digest(&crate::hashing::fiat_shamir_digest(commitment))
}

/// Computes the public half-rate special-barycentric check vector.
pub fn check_vector(commitment: &Commitment) -> Option<CheckVector> {
    let profile = commitment.profile;
    let omega = F::two_adic_generator(profile.m.ilog2() as usize);
    let omega_sq = omega.square();
    let p = challenge(commitment);
    let q = p / EF::from(omega);
    let h_inv = F::from_usize(profile.k).inverse();
    let common_p = (p.exp_u64(profile.k as u64) - EF::ONE) * EF::from(h_inv);
    let common_q = (q.exp_u64(profile.k as u64) - EF::ONE) * EF::from(h_inv);

    let mut xs = Vec::with_capacity(profile.k);
    let mut denominator_inverses = Vec::with_capacity(profile.m);
    let mut x = F::ONE;
    for _ in 0..profile.k {
        if p == EF::from(x) || q == EF::from(x) {
            return None;
        }
        xs.push(x);
        denominator_inverses.push(p - EF::from(x));
        denominator_inverses.push(q - EF::from(x));
        x *= omega_sq;
    }

    // Montgomery's trick replaces 2k extension-field inversions with one
    // inversion and O(k) multiplications.
    batch_invert(&mut denominator_inverses);

    let mut vector = vec![[F::ZERO; EXT_DEGREE]; profile.m];
    for (r, x) in xs.into_iter().enumerate() {
        vector[2 * r] = coeffs(common_p * EF::from(x) * denominator_inverses[2 * r]);
        vector[2 * r + 1] = coeffs(-(common_q * EF::from(x) * denominator_inverses[2 * r + 1]));
    }
    Some(vector)
}

/// Batch-inverts nonzero extension elements using one actual field inversion.
fn batch_invert(values: &mut [EF]) {
    let mut accumulator = EF::ONE;
    let mut prefixes = Vec::with_capacity(values.len());
    for &value in values.iter() {
        prefixes.push(accumulator);
        accumulator *= value;
    }

    let mut inverse = accumulator.inverse();
    for (value, prefix) in values.iter_mut().zip(prefixes).rev() {
        let original = *value;
        *value = inverse * prefix;
        inverse *= original;
    }
}
