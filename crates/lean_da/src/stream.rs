//! Expand the membership weights one cell column at a time and share them across rows.
//!
//! Write `x = (B << s) + u`, where `s = log2(c)` and `u` is in the cell's
//! fixed subspace. The normalized subspace polynomial `Vhat_j = X_{2^j}` is
//! additive and vanishes on that subspace for `j >= s`. Consequently,
//!
//! ```text
//! L(x) = G(B) · ∏_{j < s} (a_j(B) + z_j · Vhat_j(u))
//! a_j(B) = 1 + z_j · Vhat_j(B << s)
//! G(B) = ∏_{s ≤ j < log2(k)} a_j(B)
//! ```
//!
//! A size-`c` additive NTT evaluates the tensor `G(B) · ⊗_j(a_j(B), z_j)`.
//! Its twiddles are independent of `B`. [`StreamTables`] derives those `c-1`
//! twiddles and `log2(k) · (log2(m)-s)` shift generators from the encoder.
//! The guest mirrors this expansion to reduce intermediate writes.

use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F192};

use crate::{CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, DA_LOG_CELL, DA_LOG_K, LOG_M, row_count};

/// Constants shared by every block of the membership test.
pub struct StreamTables {
    /// Size-c NTT twiddles, indexed by `(1 << layer) - 1 + block`.
    pub twiddles: [F64; CELL_SYMBOLS - 1],
    /// `novel_at_basis[j][i] = Vhat_j(β_{DA_LOG_CELL+i})`.
    pub novel_at_basis: [[F64; LOG_M - DA_LOG_CELL]; DA_LOG_K],
}

impl Default for StreamTables {
    /// Read the normalized subspace polynomials from the encoder's twiddle tables.
    fn default() -> Self {
        let (s, log_m) = (DA_LOG_CELL, LOG_M);
        let block = AdditiveNttF64::standard(s);
        let mut twiddles = [F64::ZERO; CELL_SYMBOLS - 1];
        for layer in 0..s {
            for b in 0..1 << layer {
                twiddles[(1 << layer) - 1 + b] = block.twiddle(layer, b);
            }
        }
        let full = AdditiveNttF64::standard(log_m);
        let novel_at_basis = std::array::from_fn(|j| {
            std::array::from_fn(|offset| {
                let i = s + offset;
                if i < j {
                    F64::ZERO
                } else if i == j {
                    F64::ONE
                } else {
                    full.twiddle(log_m - j - 1, 1 << (i - j - 1))
                }
            })
        });
        Self {
            twiddles,
            novel_at_basis,
        }
    }
}

impl StreamTables {
    /// `A_j(B) = Vhat_j(B << s)`, linear in the block's bits.
    fn shift(&self, j: usize, block: usize) -> F64 {
        self.novel_at_basis[j]
            .iter()
            .enumerate()
            .filter(|(i, _)| (block >> i) & 1 == 1)
            .fold(F64::ZERO, |acc, (_, &g)| acc + g)
    }
}

/// `L` over one block, written into `out` (`c` words).
///
/// This is the routine the guest mirrors: everything it touches is either one of
/// the two baked tables, the `log k` challenges, or `O(c)` scratch.
pub fn expand_block(tables: &StreamTables, z: &[F192], block: usize, out: &mut [F192]) {
    let s = DA_LOG_CELL;
    let c = 1usize << s;
    assert_eq!(out.len(), c, "one block is one cell");
    assert_eq!(z.len(), DA_LOG_K, "one challenge per novel-basis variable");
    assert!(block < CELLS_PER_ROW, "block must lie in the domain");

    // Factors with j >= s are constant on the block; the others form its coefficients.
    let mut head = F192::ONE;
    for (j, &zj) in z.iter().enumerate().skip(s) {
        head *= F192::ONE + zj.mul_base(tables.shift(j, block));
    }

    out[0] = head;
    for (j, &zj) in z.iter().enumerate().take(s) {
        let aj = F192::ONE + zj.mul_base(tables.shift(j, block));
        let (low, high) = out[..1 << (j + 1)].split_at_mut(1 << j);
        for (h, l) in high.iter_mut().zip(low.iter_mut()) {
            *h = *l * zj;
            *l *= aj;
        }
    }

    // The size-`c` transform over `span(β_0, …, β_{s-1})`, twiddles fixed.
    for layer in 0..s {
        let half = 1usize << (s - layer - 1);
        for b in 0..1usize << layer {
            let twiddle = tables.twiddles[(1 << layer) - 1 + b];
            let start = b << (s - layer);
            for idx0 in start..start + half {
                let v = out[idx0 | half];
                let new_u = out[idx0] + v.mul_base(twiddle);
                out[idx0] = new_u;
                out[idx0 | half] = v + new_u;
            }
        }
    }
}

/// `⟨L, w_i⟩` for every row, in one column-major pass: the shape the guest runs.
///
/// Each block of `L` is expanded once and swept by every row, so the expansion is
/// amortized over `n` rows exactly as it is in the guest.
pub fn streaming_residuals(tables: &StreamTables, z: &[F192], codewords: &[u64]) -> Vec<F192> {
    assert_eq!(z.len(), DA_LOG_K, "one challenge per novel-basis variable");
    let n_rows = row_count(codewords.len(), CODEWORD_SYMBOLS);
    let (c, m) = (CELL_SYMBOLS, CODEWORD_SYMBOLS);
    let mut sums = vec![F192::ZERO; n_rows];
    let mut block = vec![F192::ZERO; c];

    for j in 0..CELLS_PER_ROW {
        expand_block(tables, z, j, &mut block);
        for (i, sum) in sums.iter_mut().enumerate() {
            let cell = &codewords[i * m + j * c..i * m + (j + 1) * c];
            for (&l, &w) in block.iter().zip(cell) {
                *sum += l.mul_base(F64(w));
            }
        }
    }
    sums
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BLOB_SYMBOLS;
    use crate::{encode_rows, membership::dual_codeword, row_residuals};
    use rand::{Rng, SeedableRng, rngs::StdRng};

    fn challenges(rng: &mut StdRng, n: usize) -> Vec<F192> {
        (0..n)
            .map(|_| F192::new(rng.random(), rng.random(), rng.random()))
            .collect()
    }

    /// The block-local factorization has to reproduce the whole-domain codeword
    /// exactly, block for block. This is the claim the guest's whole membership
    /// pass rests on, and the one place the `A_j` generators and the fixed
    /// within-block twiddles are pinned against the real encoder.
    #[test]
    fn blocks_reproduce_the_dual_codeword() {
        let tables = StreamTables::default();
        let mut rng = StdRng::seed_from_u64(17);
        let z = challenges(&mut rng, DA_LOG_K);
        let whole = dual_codeword(&z);
        let mut block = vec![F192::ZERO; CELL_SYMBOLS];
        for j in 0..CELLS_PER_ROW {
            expand_block(&tables, &z, j, &mut block);
            assert_eq!(
                &block[..],
                &whole[j * CELL_SYMBOLS..(j + 1) * CELL_SYMBOLS],
                "block {j}"
            );
        }
    }

    /// The streaming pass and the whole-domain pass must agree on every row: the
    /// guest computes the residuals one way and the native prover the other.
    #[test]
    fn streaming_matches_the_whole_domain_pass() {
        let n_rows = 5;
        let tables = StreamTables::default();
        let mut rng = StdRng::seed_from_u64(23);
        let z = challenges(&mut rng, DA_LOG_K);

        let payload: Vec<u64> = (0..n_rows * BLOB_SYMBOLS).map(|_| rng.random()).collect();
        let mut codewords = encode_rows(&payload);
        // One corrupted row, so the test also pins the two passes' agreement away
        // from zero, where any two implementations agree for free.
        codewords[2 * CODEWORD_SYMBOLS + 7] ^= 1;

        let dual = dual_codeword(&z);
        assert_eq!(
            streaming_residuals(&tables, &z, &codewords),
            row_residuals(&codewords, &dual)
        );
    }

    #[test]
    fn truncated_challenges_cannot_weaken_membership() {
        let tables = StreamTables::default();
        let mut codewords = vec![0; CODEWORD_SYMBOLS];
        codewords[BLOB_SYMBOLS] = 1;
        AdditiveNttF64::standard(LOG_M).forward_transform_scalar(crate::encode::as_field_mut(&mut codewords));
        let (commitment, _) = crate::commit_codewords(codewords.clone());
        let z = crate::membership_challenges(&commitment);
        assert_ne!(streaming_residuals(&tables, &z, &codewords)[0], F192::ZERO);

        // With only log_cell challenges, the dual degree is too small to detect
        // this degree-k row. Both entry points must reject the truncated vector.
        assert!(std::panic::catch_unwind(|| streaming_residuals(&tables, &z[..DA_LOG_CELL], &codewords)).is_err());
        assert!(
            std::panic::catch_unwind(|| {
                expand_block(&tables, &z[..DA_LOG_CELL], 0, &mut vec![F192::ZERO; CELL_SYMBOLS]);
            })
            .is_err()
        );
    }
}
