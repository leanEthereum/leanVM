use backend::{Field, PrimeCharacteristicRing, TwoAdicField};
use lean_vm::F;

use crate::config::ParameterProfile;

pub type Blob = Vec<F>;
pub type Codeword = Vec<F>;
pub type Data = Vec<Blob>;
pub type Codewords = Vec<Codeword>;

/// Applies an in-place radix-2 FFT using the supplied root of unity.
fn fft(values: &mut [F], root: F) {
    assert!(values.len().is_power_of_two());
    let n = values.len();
    for i in 1..n {
        let j = i.reverse_bits() >> (usize::BITS - n.ilog2());
        if i < j {
            values.swap(i, j);
        }
    }
    let mut len = 2;
    while len <= n {
        let step = root.exp_u64((n / len) as u64);
        for chunk in values.chunks_exact_mut(len) {
            let mut twiddle = F::ONE;
            let (left, right) = chunk.split_at_mut(len / 2);
            for (a, b) in left.iter_mut().zip(right) {
                let odd = *b * twiddle;
                let even = *a;
                *a = even + odd;
                *b = even - odd;
                twiddle *= step;
            }
        }
        len *= 2;
    }
}

/// Applies an inverse radix-2 FFT and normalizes the resulting coefficients.
fn ifft(values: &mut [F], root: F) {
    fft(values, root.inverse());
    let n_inv = F::from_usize(values.len()).inverse();
    for value in values {
        *value *= n_inv;
    }
}

/// Multiplies two coefficient-form polynomials using a radix-2 FFT convolution.
fn multiply_polynomials(left: &[F], right: &[F]) -> Vec<F> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let output_len = left.len() + right.len() - 1;
    if left.len().min(right.len()) <= 16 {
        let mut output = vec![F::ZERO; output_len];
        for (i, &a) in left.iter().enumerate() {
            for (j, &b) in right.iter().enumerate() {
                output[i + j] += a * b;
            }
        }
        return output;
    }

    let fft_len = output_len.next_power_of_two();
    let root = F::two_adic_generator(fft_len.ilog2() as usize);
    let mut left_evals = vec![F::ZERO; fft_len];
    let mut right_evals = vec![F::ZERO; fft_len];
    left_evals[..left.len()].copy_from_slice(left);
    right_evals[..right.len()].copy_from_slice(right);
    fft(&mut left_evals, root);
    fft(&mut right_evals, root);
    for (left, right) in left_evals.iter_mut().zip(right_evals) {
        *left *= right;
    }
    ifft(&mut left_evals, root);
    left_evals.truncate(output_len);
    left_evals
}

/// Builds the monic polynomial whose roots are the supplied field elements.
fn root_polynomial(roots: &[F]) -> Vec<F> {
    const CHUNK_ROOTS: usize = 16;

    let mut level: Vec<Vec<F>> = roots
        .chunks(CHUNK_ROOTS)
        .map(|chunk| {
            let mut polynomial = vec![F::ONE];
            for &root in chunk {
                let mut next = vec![F::ZERO; polynomial.len() + 1];
                for (degree, &coefficient) in polynomial.iter().enumerate() {
                    next[degree] -= coefficient * root;
                    next[degree + 1] += coefficient;
                }
                polynomial = next;
            }
            polynomial
        })
        .collect();
    if level.is_empty() {
        return vec![F::ONE];
    }

    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut pairs = level.chunks_exact(2);
        for pair in &mut pairs {
            next.push(multiply_polynomials(&pair[0], &pair[1]));
        }
        if let Some(last) = pairs.remainder().first() {
            next.push(last.clone());
        }
        level = next;
    }
    level.pop().unwrap()
}

/// Computes a truncated formal power-series inverse with Newton iteration.
fn invert_series(polynomial: &[F], target_len: usize) -> Vec<F> {
    debug_assert!(!polynomial.is_empty() && polynomial[0] != F::ZERO);
    let mut inverse = vec![polynomial[0].inverse()];
    while inverse.len() < target_len {
        let next_len = (2 * inverse.len()).min(target_len);
        let product = multiply_polynomials(&polynomial[..polynomial.len().min(next_len)], &inverse);
        let mut correction = vec![F::ZERO; next_len];
        correction[0] = F::TWO;
        for (output, value) in correction.iter_mut().zip(product) {
            *output -= value;
        }
        inverse = multiply_polynomials(&inverse, &correction);
        inverse.truncate(next_len);
    }
    inverse
}

/// Systematically RS-encodes one blob on a subgroup using a k-IFFT and m-FFT.
pub fn encode_blob(profile: ParameterProfile, blob: &[F]) -> Codeword {
    assert_eq!(blob.len(), profile.k);
    let omega = F::two_adic_generator(profile.m.ilog2() as usize);
    let systematic_root = omega.exp_u64(profile.systematic_stride() as u64);
    let mut coefficients = blob.to_vec();
    ifft(&mut coefficients, systematic_root);
    coefficients.resize(profile.m, F::ZERO);
    fft(&mut coefficients, omega);
    coefficients
}

/// RS-encodes all blobs into the rows of the PQ-DAS codeword matrix.
pub fn encode(profile: ParameterProfile, data: &Data) -> Codewords {
    assert_eq!(data.len(), profile.n);
    data.iter().map(|blob| encode_blob(profile, blob)).collect()
}

/// Reuses locator data to recover many rows with the same arbitrary erasure pattern.
#[derive(Debug)]
pub struct ErasureDecoder {
    profile: ParameterProfile,
    known_indices: Vec<usize>,
    locator_evaluations: Vec<F>,
    reversed_locator_inverse: Vec<F>,
    numerator_max_degree: usize,
}

impl ErasureDecoder {
    /// Precomputes the arbitrary-erasure locator, its domain evaluations, and its reversed inverse.
    pub fn new(profile: ParameterProfile, known_indices: &[usize]) -> Option<Self> {
        if known_indices.len() < profile.k {
            return None;
        }
        let mut known = vec![false; profile.m];
        for &index in known_indices {
            if index >= profile.m || std::mem::replace(&mut known[index], true) {
                return None;
            }
        }

        let omega = F::two_adic_generator(profile.m.ilog2() as usize);
        let mut point = F::ONE;
        let mut erased_points = Vec::with_capacity(profile.m - known_indices.len());
        for is_known in &known {
            if !is_known {
                erased_points.push(point);
            }
            point *= omega;
        }

        // Z(X) vanishes exactly at missing codeword positions. The subproduct
        // tree uses FFT polynomial multiplication for quasi-linear preparation.
        let locator = root_polynomial(&erased_points);
        let mut locator_evaluations = vec![F::ZERO; profile.m];
        locator_evaluations[..locator.len()].copy_from_slice(&locator);
        fft(&mut locator_evaluations, omega);

        // Exact division N(X)/Z(X) becomes a truncated series product after
        // reversing both polynomials; Newton iteration prepares 1/rev(Z).
        let reversed_locator: Vec<_> = locator.iter().rev().copied().collect();
        let reversed_locator_inverse = invert_series(&reversed_locator, profile.k);
        Some(Self {
            profile,
            known_indices: known_indices.to_vec(),
            locator_evaluations,
            reversed_locator_inverse,
            numerator_max_degree: profile.k + erased_points.len() - 1,
        })
    }

    /// Recovers one systematic row using numerator IFFT, fast exact division, and a systematic-domain FFT.
    pub fn reconstruct_blob(&self, values: &[F]) -> Option<Blob> {
        if values.len() != self.known_indices.len() {
            return None;
        }

        // N(X)=f(X)Z(X). Its complete evaluation vector is known: it is zero
        // at erasures and equals the received value times Z at known points.
        let mut numerator = vec![F::ZERO; self.profile.m];
        for (&index, &value) in self.known_indices.iter().zip(values) {
            numerator[index] = value * self.locator_evaluations[index];
        }
        let omega = F::two_adic_generator(self.profile.m.ilog2() as usize);
        ifft(&mut numerator, omega);

        let reversed_numerator: Vec<_> = (0..self.profile.k)
            .map(|offset| numerator[self.numerator_max_degree - offset])
            .collect();
        let mut reversed_coefficients = multiply_polynomials(&reversed_numerator, &self.reversed_locator_inverse);
        reversed_coefficients.truncate(self.profile.k);
        reversed_coefficients.reverse();

        let systematic_root = omega.exp_u64(self.profile.systematic_stride() as u64);
        fft(&mut reversed_coefficients, systematic_root);
        Some(reversed_coefficients)
    }
}

/// Reconstructs one systematic blob from arbitrary indexed codeword evaluations.
pub fn reconstruct_blob(profile: ParameterProfile, samples: &[(usize, F)]) -> Option<Blob> {
    if samples.len() < profile.k {
        return None;
    }
    let indices: Vec<_> = samples.iter().map(|(index, _)| *index).collect();
    let values: Vec<_> = samples.iter().map(|(_, value)| *value).collect();
    ErasureDecoder::new(profile, &indices)?.reconstruct_blob(&values)
}

/// Produces deterministic field-element input data for a selected profile.
pub fn demo_data(profile: ParameterProfile) -> Data {
    (0..profile.n)
        .map(|row| {
            (0..profile.k)
                .map(|col| F::from_usize(1 + row * profile.k + col))
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    /// Checks generalized systematic FFT encoding on the tiny profile.
    fn encoding_is_systematic() {
        let profile = ParameterProfile::TINY;
        let data = demo_data(profile);
        let codewords = encode(profile, &data);
        for row in 0..profile.n {
            let systematic: Vec<_> = (0..profile.k)
                .map(|i| codewords[row][i * profile.systematic_stride()])
                .collect();
            assert_eq!(systematic, data[row]);
        }
    }

    #[test]
    /// Recovers a row from an arbitrary non-subgroup half of its codeword positions.
    fn arbitrary_erasure_reconstruction() {
        let profile = ParameterProfile::MEDIUM;
        let blob = demo_data(profile).remove(0);
        let codeword = encode_blob(profile, &blob);
        let indices: Vec<_> = (0..profile.k).map(|i| (37 * i + 11) % profile.m).collect();
        let samples: Vec<_> = indices.iter().map(|&index| (index, codeword[index])).collect();
        assert_eq!(reconstruct_blob(profile, &samples).unwrap(), blob);
    }
}
