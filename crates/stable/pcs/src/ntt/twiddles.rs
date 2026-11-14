//! The points of the domain: the table of normalized subspace polynomials and its twiddles.

use primitives::field::F64;
use primitives::log2_strict_usize;

/// Table of the normalized subspace polynomials at the basis, rows end to end.
///
/// - Row `i` holds `s_i(b_j)` for every basis element `b_j` with `j >= i`, so `l - i` values.
/// - Each row is scaled so that its first entry is one.
fn generate_evals_from_subspace(basis: &[F64]) -> Vec<F64> {
    let l = basis.len();
    let mut evals = Vec::with_capacity(l * (l + 1) / 2);
    evals.extend_from_slice(basis);
    let mut prev = 0;
    for i in 1..l {
        for k in 1..=l - i {
            let (v, first) = (evals[prev + k], evals[prev]);
            evals.push(v * (v + first));
        }
        prev += l - i + 1;
    }
    let mut rest = &mut evals[..];
    for i in 0..l {
        let (row, tail) = rest.split_at_mut(l - i);
        let inv = row[0].inv();
        row.iter_mut().for_each(|v| *v *= inv);
        rest = tail;
    }
    evals
}

/// `Σ_j bit_j(idx) · basis[j]`.
#[inline]
fn span_get(basis: &[F64], idx: usize) -> F64 {
    let mut acc = F64::ZERO;
    for (j, &b) in basis.iter().enumerate() {
        if (idx >> j) & 1 == 1 {
            acc += b;
        }
    }
    acc
}

/// Additive NTT over F_{2^64} on the standard polynomial-basis subspace `{1, x, x^2, ...}`: the integers under
/// their natural encoding.
///
/// - It owns the rows of `generate_evals_from_subspace` and the byte tables built from them, so the twiddle of
///   every block at every layer.
/// - The encodes (`encode.rs`), the layer sweeps (`layers.rs`) and the reads of rows an encode left out of its
///   codeword (`openings.rs`) are its methods.
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    /// The rows of [`generate_evals_from_subspace`], end to end.
    evals: Vec<F64>,
    /// Per eval row, the subset sums of `row[1..]` over each byte of a block index:
    /// a twiddle of a block below `2^24` is three loads and two XORs.
    tables: Vec<[[F64; 256]; 3]>,
}

impl AdditiveNttF64 {
    /// Row `i`, which starts after `l + (l - 1) + ... + (l - i + 1)` values.
    fn row(&self, i: usize) -> &[F64] {
        let l = self.tables.len();
        let start = i * l - i * i.saturating_sub(1) / 2;
        &self.evals[start..start + l - i]
    }

    fn new(basis: &[F64]) -> Self {
        let evals = generate_evals_from_subspace(basis);
        let mut rest = &evals[..];
        let tables = (0..basis.len())
            .map(|i| {
                let (row, tail) = rest.split_at(basis.len() - i);
                rest = tail;
                let basis = &row[1..];
                let mut t = [[F64::ZERO; 256]; 3];
                for (k, part) in t.iter_mut().enumerate() {
                    let sub = &basis[(8 * k).min(basis.len())..(8 * k + 8).min(basis.len())];
                    for (x, slot) in part.iter_mut().enumerate() {
                        *slot = span_get(sub, x);
                    }
                }
                t
            })
            .collect();
        Self { evals, tables }
    }

    /// Standard NTT with basis `{1, x, …, x^(dim-1)}`. Requires `dim ≤ 63` so
    /// the evaluation domain (and the twiddles) stay inside F_{2^64} without
    /// wrap; far beyond any codeword size in use.
    pub fn standard(dim: usize) -> Self {
        assert!(dim <= 63, "standard NTT requires dim ≤ 63");
        let basis: Vec<F64> = (0..dim).map(|i| F64(1u64 << i)).collect();
        Self::new(&basis)
    }

    pub(super) fn log_domain_size(&self) -> usize {
        self.tables.len()
    }

    /// Twiddle of one block at one layer.
    ///
    /// - It is `s_i(sum_j bit_j(block) * b_(i+1+j))`, with `i = log_domain_size - layer - 1`.
    /// - The normalized `s_i` is F_2-linear, so this is a subset sum of row `i` of the table.
    #[inline]
    pub fn twiddle(&self, layer: usize, block: usize) -> F64 {
        let row = self.log_domain_size() - layer - 1;
        if block < 1 << 24 {
            let t = &self.tables[row];
            t[0][block & 255] + t[1][(block >> 8) & 255] + t[2][(block >> 16) & 255]
        } else {
            span_get(&self.row(row)[1..], block)
        }
    }

    /// The seven twiddles a radix-8 group needs, breadth-first: layer `layer`,
    /// then `layer + 1` (one per half), then `layer + 2` (one per quarter).
    ///
    /// `span_get` is F_2-linear in the block index, so a deeper layer's twiddles are its
    /// first child's plus a fixed offset per child: three lookups instead of seven.
    pub(super) fn radix8(&self, layer: usize, block: usize) -> [F64; 7] {
        let l = self.log_domain_size();
        let (v1, v2) = (self.row(l - layer - 2), self.row(l - layer - 3));
        // `a` and `c` are the deeper layers' twiddles of this block's first sub-block.
        let t0 = self.twiddle(layer, block);
        let a = self.twiddle(layer + 1, 2 * block);
        let c = self.twiddle(layer + 2, 4 * block);
        let (d, e0, e1) = (v1[1], v2[1], v2[2]);
        [t0, a, a + d, c, c + e0, c + e1, c + e0 + e1]
    }

    /// Recover novel-basis coefficients from evaluations with a scalar inverse NTT.
    pub fn inverse_transform(&self, data: &mut [F64]) {
        let log_d = log2_strict_usize(data.len());
        assert!(log_d <= self.log_domain_size());
        for layer in (0..log_d).rev() {
            let num_blocks = 1usize << layer;
            let block_size_half = 1usize << (log_d - layer - 1);
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block << (log_d - layer);
                for idx0 in block_start..(block_start + block_size_half) {
                    let idx1 = idx0 | block_size_half;
                    let u = data[idx0];
                    let new_v = data[idx1] + u;
                    data[idx1] = new_v;
                    data[idx0] = u + new_v * twiddle;
                }
            }
        }
    }
}
