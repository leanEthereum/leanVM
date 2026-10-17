//! The block R1CS `(A_0, B_0, C_0)` as padded sparse GF(2) matrices, and the column layout of one instance.
//!
//! Rows and columns are padded to `2^k_log` (`k_log >= MIN_K_LOG`). The first `64 * public_words()` columns are the
//! public region: column 0 is the constant one, columns `1..=n_public` the public bits, the rest zero. Private
//! signals are renumbered to start right after it, so the public region is whole packed words of every instance.

use crate::format::{FormatError, MAX_LOG, R1csFile};
use flock::lincheck::LincheckCircuit;
use primitives::field::F192;

/// Smallest block: `2^7` rows and columns.
pub const MIN_K_LOG: usize = 7;

/// A GF(2) matrix in compressed sparse row form: every listed entry is 1, and each row's columns are strictly
/// increasing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Csr {
    pub row_ptr: Vec<u32>,
    pub cols: Vec<u32>,
}

impl Csr {
    pub fn n_rows(&self) -> usize {
        self.row_ptr.len() - 1
    }

    pub fn nnz(&self) -> usize {
        self.cols.len()
    }

    /// The columns of row `r`.
    #[inline]
    pub fn row(&self, r: usize) -> &[u32] {
        &self.cols[self.row_ptr[r] as usize..self.row_ptr[r + 1] as usize]
    }
}

/// The padded block matrices, `2^k_log` rows and columns each.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockMatrices {
    pub k_log: usize,
    pub a: Csr,
    pub b: Csr,
    pub c: Csr,
}

/// Why a block R1CS was rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockError {
    /// The file's own invariants do not hold.
    Format(FormatError),
    /// The padded block would exceed `2^MAX_LOG`, or the nonzeros overflow a `u32`.
    TooLarge,
}

impl std::fmt::Display for BlockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl std::error::Error for BlockError {}

/// A validated block R1CS: its padded matrices, its signal counts and the digest of its canonical file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockR1cs {
    pub matrices: BlockMatrices,
    pub n_signals: usize,
    pub n_public: usize,
    pub n_constraints: usize,
    /// BLAKE2s of the canonical `CLB1` encoding.
    pub digest: [u8; 32],
}

impl BlockR1cs {
    pub fn new(file: &R1csFile) -> Result<Self, BlockError> {
        let (n_signals, n_public) = (file.n_signals, file.n_public);
        if n_signals == 0 || n_public >= n_signals || n_signals > 1 << MAX_LOG {
            return Err(BlockError::Format(FormatError::BadHeader));
        }
        for (index, constraint) in file.constraints.iter().enumerate() {
            for side in [&constraint.a, &constraint.b, &constraint.c] {
                if let Some(&signal) = side.iter().find(|&&s| s as usize >= n_signals) {
                    return Err(BlockError::Format(FormatError::SignalOutOfRange {
                        constraint: index,
                        signal,
                    }));
                }
                if side.windows(2).any(|w| w[0] >= w[1]) {
                    return Err(BlockError::Format(FormatError::NotIncreasing { constraint: index }));
                }
            }
        }

        let public_words = (n_public + 1).div_ceil(64);
        let shift = 64 * public_words - (n_public + 1);
        let used_cols = n_signals + shift;
        let n_constraints = file.constraints.len();
        let k_log = (used_cols.max(n_constraints).next_power_of_two().trailing_zeros() as usize).max(MIN_K_LOG);
        if k_log > MAX_LOG {
            return Err(BlockError::TooLarge);
        }
        let k = 1usize << k_log;
        let column = |s: u32| if s as usize <= n_public { s } else { s + shift as u32 };

        let build = |side: fn(&crate::format::Constraint) -> &Vec<u32>| -> Result<Csr, BlockError> {
            let nnz: usize = file.constraints.iter().map(|c| side(c).len()).sum();
            if nnz > u32::MAX as usize {
                return Err(BlockError::TooLarge);
            }
            let mut row_ptr = Vec::with_capacity(k + 1);
            let mut cols = Vec::with_capacity(nnz);
            row_ptr.push(0);
            for constraint in &file.constraints {
                cols.extend(side(constraint).iter().map(|&s| column(s)));
                row_ptr.push(cols.len() as u32);
            }
            row_ptr.resize(k + 1, cols.len() as u32);
            Ok(Csr { row_ptr, cols })
        };
        let matrices = BlockMatrices {
            k_log,
            a: build(|c| &c.a)?,
            b: build(|c| &c.b)?,
            c: build(|c| &c.c)?,
        };
        Ok(Self {
            matrices,
            n_signals,
            n_public,
            n_constraints,
            digest: primitives::hash::hash(&file.encode()),
        })
    }

    pub fn k_log(&self) -> usize {
        self.matrices.k_log
    }

    /// Packed 64-bit words per instance in the public region.
    pub fn public_words(&self) -> usize {
        (self.n_public + 1).div_ceil(64)
    }

    /// Columns that can be nonzero: the public region, then the private signals.
    pub fn used_columns(&self) -> usize {
        64 * self.public_words() + self.n_signals - (self.n_public + 1)
    }

    /// Rows that can be nonzero.
    pub fn used_rows(&self) -> usize {
        self.n_constraints
    }

    /// Lay one instance's signal bytes (`ceil(n_signals / 8)` bytes, signal `j` at bit `j`) out as its block of
    /// `2^k_log / 64` packed words: the public region first, then the private signals. `out` must be zero.
    pub fn layout_instance(&self, signals: &[u8], out: &mut [u64]) {
        debug_assert_eq!(signals.len(), self.n_signals.div_ceil(8));
        debug_assert_eq!(out.len(), (1usize << self.k_log()) / 64);
        self.layout_public(signals, &mut out[..self.public_words()]);
        let n_head = self.n_public + 1;
        copy_bits(signals, n_head, self.n_signals - n_head, out, self.public_words());
    }

    /// The public region of one instance: the constant, the public bits and zero padding, `public_words()` words.
    pub fn layout_public(&self, signals: &[u8], out: &mut [u64]) {
        debug_assert_eq!(out.len(), self.public_words());
        copy_bits(signals, 0, self.n_public + 1, out, 0);
    }

    /// The first violated row of one laid-out instance, if any.
    pub fn first_violation(&self, z: &[u64]) -> Option<usize> {
        let m = &self.matrices;
        let parity = |row: &[u32]| row.iter().fold(0u64, |acc, &c| acc ^ (z[c as usize >> 6] >> (c & 63)));
        (0..self.n_constraints).find(|&r| (parity(m.a.row(r)) & parity(m.b.row(r)) ^ parity(m.c.row(r))) & 1 != 0)
    }
}

/// `len` bits of `src` from bit `src_bit` onwards, OR-ed into `dst` from the start of word `dst_word`.
fn copy_bits(src: &[u8], src_bit: usize, len: usize, dst: &mut [u64], dst_word: usize) {
    for (w, slot) in dst[dst_word..dst_word + len.div_ceil(64)].iter_mut().enumerate() {
        let bit = src_bit + 64 * w;
        let take = (len - 64 * w).min(64);
        let first = bit / 8;
        let mut window = [0u8; 16];
        let end = (first + 9).min(src.len());
        window[..end - first].copy_from_slice(&src[first..end]);
        let bits = (u128::from_le_bytes(window) >> (bit % 8)) as u64;
        *slot |= if take == 64 { bits } else { bits & ((1u64 << take) - 1) };
    }
}

impl LincheckCircuit for BlockMatrices {
    fn n_cols(&self) -> usize {
        1 << self.k_log
    }

    fn c_is_identity(&self) -> bool {
        false
    }

    fn const_pin_col(&self) -> usize {
        0
    }

    /// `eqᵀA_0 + α·eqᵀB_0 + α²·eqᵀC_0`, one sparse pass over the rows.
    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
        let alpha_sq = alpha.square();
        let mut out = vec![F192::ZERO; self.n_cols()];
        for (r, &e) in eq_inner.iter().enumerate() {
            for (m, weight) in [(&self.a, F192::ONE), (&self.b, alpha), (&self.c, alpha_sq)] {
                let row = m.row(r);
                if !row.is_empty() {
                    let v = weight * e;
                    for &c in row {
                        out[c as usize] += v;
                    }
                }
            }
        }
        out
    }
}
