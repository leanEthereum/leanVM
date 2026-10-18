//! Multilinear and stacking helpers.

use crate::field::{E, GEN, ONE, Scaled, ZERO};
use crate::{VerifierError, require};

/// `eq(i, point)` for every index `i`, LSB-first, at one product per entry: `v * (1 + r) = v + v * r`.
pub fn eq_kernel(point: &[E]) -> Vec<E> {
    let mut out = vec![ZERO; 1 << point.len()];
    out[0] = ONE;
    for (k, &r) in point.iter().enumerate() {
        let (low, high) = out[..2 << k].split_at_mut(1 << k);
        let scale = Scaler::new(r, low.len());
        for (v, h) in low.iter_mut().zip(high) {
            *h = scale.mul(*v);
            *v += *h;
        }
    }
    out
}

/// Multiplication by `r`, through [`Scaled`] once it multiplies enough values to repay the table.
enum Scaler {
    Table(Scaled),
    Plain(E),
}

impl Scaler {
    fn new(r: E, uses: usize) -> Self {
        if uses >= 256 {
            Self::Table(Scaled::new(r))
        } else {
            Self::Plain(r)
        }
    }

    #[inline]
    fn mul(&self, value: E) -> E {
        match self {
            Self::Table(table) => table.mul(value),
            Self::Plain(r) => value * *r,
        }
    }
}

pub fn multilinear_eval<T: Copy + Into<E>>(mle: &[T], point: &[E]) -> Result<E, VerifierError> {
    require(
        point.len() < 64 && mle.len() == 1 << point.len(),
        VerifierError::MultilinearSize,
    )?;
    let mut cur: Vec<E> = mle.iter().map(|&value| value.into()).collect();
    for &r in point {
        let scale = Scaler::new(r, cur.len() / 2);
        for i in 0..cur.len() / 2 {
            cur[i] = cur[2 * i] + scale.mul(cur[2 * i] + cur[2 * i + 1]);
        }
        cur.truncate(cur.len() / 2);
    }
    Ok(cur[0])
}

pub fn log2_ceil(value: u64) -> usize {
    (64 - value.saturating_sub(1).leading_zeros()) as usize
}

pub fn log2_strict(value: u64) -> Result<usize, VerifierError> {
    require(value.is_power_of_two(), VerifierError::NotPowerOfTwo)?;
    Ok(value.trailing_zeros() as usize)
}

pub fn eq_eval(left: &[E], right: &[E]) -> E {
    assert_eq!(left.len(), right.len());
    let mut result = ONE;
    for (&x, &y) in left.iter().zip(right) {
        result *= ONE + x + y;
    }
    result
}

pub fn dot(left: &[E], right: &[E]) -> E {
    assert_eq!(left.len(), right.len());
    let mut result = ZERO;
    for (&x, &y) in left.iter().zip(right) {
        result += x * y;
    }
    result
}

/// `pad_n(point)`, the multilinear extension of `[z >= n]`, `n <= 2^len(point)` (lemma lem:suffix).
pub fn padding_weight(point: &[E], n: u64) -> E {
    let bit = |k: usize| E::new(n >> k & 1, 0, 0);
    let low = point
        .iter()
        .enumerate()
        .fold(ONE, |pad, (k, &r)| (ONE + bit(k)) * r + (ONE + bit(k) + r) * pad);
    (ONE + bit(point.len())) * low
}

/// MLE of `[1, g, g^2, ...]` at an LSB-first point.
pub fn index_mle(point: &[E]) -> E {
    let mut result = ONE;
    let mut generator_power = GEN;
    for &challenge in point {
        result *= ONE + challenge * (ONE + generator_power);
        generator_power = generator_power.square();
    }
    result
}

/// A polynomial at `point`, by Horner over its coefficients, constant first.
pub fn poly_eval(coefficients: &[E], point: E) -> E {
    coefficients.iter().rev().fold(ZERO, |acc, &c| acc * point + c)
}

/// Where something sits in the stacked cube: a claim's point fills the `variables` coordinates above `low`, the bits of `index` fixing the rest.
/// `low` is zero for a block with a cube of its own, and the slot width for a column interleaved into a bigger block.
#[derive(Clone, Copy, Debug)]
pub struct Placement {
    pub variables: usize,
    pub index: u64,
    pub low: usize,
}

impl Placement {
    pub fn stack_point(&self, point: &[E], stack_log: usize) -> Vec<E> {
        let bits = selector_point(self.index, stack_log);
        [&bits[..self.low], point, &bits[self.low + self.variables..]].concat()
    }

    /// eq weight of the coordinates above the window.
    pub fn eq_above(&self, point: &[E]) -> E {
        let window = self.low + self.variables;
        let bits = selector_point(self.index >> window, point.len() - window);
        eq_eval(&bits, &point[window..])
    }
}

pub fn stack_offsets(sizes: &[usize]) -> (Vec<u64>, usize) {
    let mut order: Vec<usize> = (0..sizes.len()).collect();
    order.sort_by_key(|&index| (std::cmp::Reverse(sizes[index]), index));
    let mut offsets = vec![0; sizes.len()];
    let mut total = 0;
    for index in order {
        offsets[index] = total;
        total += 1 << sizes[index];
    }
    (offsets, log2_ceil(total))
}

fn selector_point(selector: u64, length: usize) -> Vec<E> {
    (0..length).map(|bit| E::new(selector >> bit & 1, 0, 0)).collect()
}
