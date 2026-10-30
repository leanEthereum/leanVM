//! The public API of the additive NTT, as one-line forwards to its components.

use primitives::field::F64;

use super::encode::{Encoded, Encoder, Keep, RowSink};
use super::layers::Layers;
#[cfg(doc)]
use super::openings::Kept;
use super::openings::Openings;
use super::plan::Plan;
use super::twiddles::Twiddles;

/// Additive NTT over F_{2^64} with the standard polynomial-basis subspace
/// `{1, x, x², …}`: the F_2-subspace is `{0, 1, …, 2^ℓ−1}` under the natural
/// integer encoding.
///
/// - It owns the `Twiddles` of the domain.
/// - Every method forwards to the component that does the work.
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    pub(super) tw: Twiddles,
}

impl AdditiveNttF64 {
    /// The layer sweeps over this domain.
    pub(super) fn layers(&self) -> Layers<'_> {
        Layers::new(&self.tw)
    }

    /// Standard NTT with basis `{1, x, …, x^(dim-1)}`. Requires `dim ≤ 63` so
    /// the evaluation domain (and the twiddles) stay inside F_{2^64} without
    /// wrap; far beyond any codeword size in use.
    pub fn standard(dim: usize) -> Self {
        Self {
            tw: Twiddles::standard(dim),
        }
    }

    /// Twiddle of one block at one layer.
    ///
    /// - It is `s_i(sum_j bit_j(block) * b_(i+1+j))`, with `i = L - layer - 1` on a `2^L`-point domain.
    /// - The normalized `s_i` is F_2-linear, so this is a subset sum of row `i` of the table.
    #[inline]
    pub fn twiddle(&self, layer: usize, block: usize) -> F64 {
        self.tw.twiddle(layer, block)
    }

    /// Recover novel-basis coefficients from evaluations with a scalar inverse NTT.
    pub fn inverse_transform(&self, data: &mut [F64]) {
        self.tw.inverse_transform(data)
    }

    /// RS-encode a message already stored in the codeword's first replica.
    ///
    /// - The message fills the first `1 / 2^r` of the buffer, `r` the log inverse rate.
    /// - It is row-major: word `row * n + lane` for `n` interleaved lanes.
    /// - The buffer ends as `2^r` copies of it, each transformed from layer `r` on.
    #[inline]
    pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
        Encoder::new(&self.tw).in_place(data, num_ntts, log_inv_rate)
    }

    /// Encode a lane-major message, handing `on_rows` every finished block, and keep what `keep` asks for.
    ///
    /// - The result equals a transpose into block 0 followed by the in-place encode.
    /// - With [`Keep::Nothing`], if one gathered pass covers the layers before the deep pass,
    ///   the codeword is never whole: the encode runs once per half of the cosets.
    #[inline]
    #[allow(clippy::too_many_arguments)]
    pub fn encode_lane_major(
        &self,
        msg: &[F64],
        n_lanes: usize,
        num_ntts: usize,
        log_inv_rate: usize,
        keep: Keep,
        on_rows: &RowSink<'_>,
    ) -> Encoded {
        Encoder::new(&self.tw).lane_major(msg, n_lanes, num_ntts, log_inv_rate, keep, on_rows)
    }

    /// RS-encode a message held in a buffer of its own, handing `on_rows` every finished block of rows.
    ///
    /// - The result equals encoding in place, and the codeword may start uninitialized.
    /// - With `defer_deep`, the deep pass is not written back.
    ///   [`Openings::rows`] with [`Kept::BeforeDeep`] finishes any row again.
    /// - With no separate deep pass in the plan, the buffer is the whole codeword and this returns `None`.
    ///
    /// # Panics
    ///
    /// Panics unless the codeword is exactly `2^r` messages long.
    #[inline]
    pub fn encode_interleaved_with(
        &self,
        data: &mut [F64],
        msg: &[F64],
        num_ntts: usize,
        log_inv_rate: usize,
        defer_deep: bool,
        on_rows: &RowSink<'_>,
    ) -> Option<Plan> {
        Encoder::new(&self.tw).rows(data, msg, num_ntts, log_inv_rate, defer_deep, on_rows)
    }

    /// The reads of codeword rows that an encode left out of its codeword.
    #[inline]
    pub fn openings(&self) -> Openings<'_> {
        Openings::new(self.layers())
    }
}
