//! The lane-major message: its transpose, and the stage a gathered first pass fills from it.

use primitives::field::F64;
use primitives::stream::Stream;

use super::scratch::with_scratch;
use super::source::Lanes;
use super::window::STREAM_MIN_WORDS;

/// Transpose a lane-major message into the row-major order the encodes read.
///
/// # Layout
///
/// ```text
///     input, lane-major:   [ block 0 | block 1 | ... | block n-1 ]   each 2^log_rows words
///     output, row-major:   row x = [ 0, ..., 0, block n-1 word x, ..., block 0 word x ]
/// ```
///
/// - A row is `row_words >= n` words: the first `row_words - n` lanes are zero padding.
/// - Codeword lane `t` past the padding takes message block `row_words - 1 - t`.
/// - Any lane count works: a commitment encodes only the lanes that carry data, and a caller pads
///   the row to a multiple of [`ROW_LANES`](super::ROW_LANES).
///
/// # Why descending
///
/// - The absent all-zero lanes lead every Merkle leaf image, so the proof can leave them out.
/// - `whir::commit` has the full reason.
///
/// # Performance
///
/// - Rows are handled one tile at a time.
/// - Each lane adds a contiguous burst of words to an L1-resident tile.
/// - The finished tile goes out as one contiguous run.
/// - That keeps an n-way gather at a `2^log_rows` stride near memory bandwidth.
pub(super) fn transpose_lane_major(out: &mut [F64], msg: &[F64], n_lanes: usize, row_words: usize, log_rows: usize) {
    let rows = 1usize << log_rows;
    assert!(n_lanes > 0, "a commitment needs at least one lane");
    assert!(n_lanes <= row_words, "a row holds its lanes");
    assert_eq!(msg.len(), n_lanes * rows, "message is n_lanes contiguous lane blocks");
    assert_eq!(out.len(), row_words * rows, "the output is whole padded rows");

    /// Words per cache-resident row tile.
    const TILE_WORDS: usize = 4096;
    assert!(row_words <= TILE_WORDS, "a codeword row must fit the transpose tile");
    // Largest power-of-two row count whose tile fits: both it and `rows` are then
    // powers of two, so the tiles cover every row. They have to: this is the sole
    // initializer of an uninitialized codeword's message region, and a truncating
    // tile count would leave the tail reading the previous phase's plausible bytes,
    // whose symptom is a proof that stops verifying rather than a crash.
    let tile_rows = (1usize << (TILE_WORDS / row_words).ilog2()).min(rows);
    assert_eq!(rows % tile_rows, 0, "row tiles must cover every row");

    // Nothing reads the output back before a buffer this large is evicted.
    let stream = out.len() >= STREAM_MIN_WORDS;
    let pad = row_words - n_lanes;
    parallel::chunks_mut(out, tile_rows * row_words, |t, out_tile| {
        with_scratch(out_tile.len(), |tile| {
            // First message row this tile covers.
            let r0 = t * tile_rows;
            // Fill the tile column by column: lane `lane` takes every `row_words`-th word.
            for lane in 0..row_words {
                let slots = tile[lane..].iter_mut().step_by(row_words);
                if lane < pad {
                    slots.for_each(|slot| *slot = F64::ZERO);
                } else {
                    let src = &msg[(row_words - 1 - lane) * rows + r0..][..tile_rows];
                    for (slot, &word) in slots.zip(src) {
                        *slot = word;
                    }
                }
            }
            // Write the finished tile out as one contiguous run.
            if stream {
                Stream::new().copy(out_tile, tile);
            } else {
                out_tile.copy_from_slice(tile);
            }
        });
    });
}

/// Residues a lane-major first pass takes at once, as a log: one cache line of a lane block.
pub(super) const LOG_BATCH: usize = 3;
pub(super) const BATCH: usize = 1 << LOG_BATCH;

/// The lane groups a stage moves across a row of `row_words` lanes, as `(first lane, lanes)`: whole octets, then a
/// quad where the row ends four lanes past one.
pub(super) fn lane_groups(row_words: usize) -> impl Iterator<Item = (usize, usize)> {
    assert!(row_words.is_multiple_of(4), "a staged row is whole quads of lanes");
    (0..row_words)
        .step_by(8)
        .map(move |lane| (lane, (row_words - lane).min(8)))
}

/// The transpose of a lane-major message through a stage, for one gathered pass.
///
/// - It owns the message and the geometry of the fill: the step, the message rows and the row width.
/// - [`Stage::fill`] moves one group of lanes of a batch of residues into a stage buffer.
/// - A task fills the stage, then each block of the pass transforms a copy of it.
pub(super) struct Stage<'a> {
    lanes: Lanes<'a>,
    log_step: usize,
    msg_rows: usize,
    row_words: usize,
}

impl<'a> Stage<'a> {
    /// The stage of a pass whose groups are `2^log_step` rows apart, over `lanes` of `msg_rows` rows each.
    pub(super) fn new(lanes: Lanes<'a>, log_step: usize, msg_rows: usize, row_words: usize) -> Self {
        Self {
            lanes,
            log_step,
            msg_rows,
            row_words,
        }
    }

    /// Transpose lanes `lane0..lane0 + lanes`, a group of [`lane_groups`], of a batch of [`BATCH`] consecutive
    /// residues from `t0` into `stage`.
    ///
    /// - Message row `j` is `msg_rows` words apart per lane block, and word `w` of a row of `row_words` words
    ///   is lane block `row_words - 1 - w` of the message, or zero while `w` is below the padding.
    /// - Residue `t0 + s` takes rows `t0 + s + i * step` for `i < rows`, `step = 2^log_step`.
    /// - Together with the residues, the group's lanes are `BATCH * lanes` lanes of one transform.
    /// - `stage` has `rows` rows of `BATCH * lanes` words.
    ///   Lane `lane0 + k` of row `t0 + s + i * step` is word `(i * BATCH + s) * lanes + k`.
    /// - One tile is 8 words of each lane block of the group, so each 64 byte line of a lane block is read once, whole.
    #[inline]
    pub(super) fn fill(&self, stage: &mut [F64], t0: usize, lane0: usize, lanes: usize) {
        match lanes {
            8 => self.fill_group::<8>(stage, t0, lane0),
            4 => self.fill_group::<4>(stage, t0, lane0),
            _ => unreachable!("a stage moves an octet or a quad of lanes"),
        }
    }

    #[inline(always)]
    fn fill_group<const W: usize>(&self, stage: &mut [F64], t0: usize, lane0: usize) {
        let Self {
            lanes: Lanes { words: msg, n_lanes },
            log_step,
            msg_rows,
            row_words,
        } = *self;
        // SAFETY: AVX-512F is enabled at compile time.
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        unsafe {
            fill_stage_tiles::<W>(stage, msg, t0, log_step, msg_rows, n_lanes, row_words, lane0)
        }
        // SAFETY: AVX2 is enabled at compile time.
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
        unsafe {
            fill_stage_tiles::<W>(stage, msg, t0, log_step, msg_rows, n_lanes, row_words, lane0)
        }
        #[cfg(not(any(
            all(target_arch = "x86_64", target_feature = "avx512f"),
            all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f"))
        )))]
        fill_stage_tiles::<W>(stage, msg, t0, log_step, msg_rows, n_lanes, row_words, lane0);
    }
}

/// [`Stage::fill`] of `W` lanes, a target-feature function where AVX-512 or AVX2 is enabled, so its tiles move
/// through registers.
#[cfg_attr(
    all(target_arch = "x86_64", target_feature = "avx512f"),
    target_feature(enable = "avx512f"),
    inline
)]
#[cfg_attr(
    all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")),
    target_feature(enable = "avx2"),
    inline
)]
fn fill_stage_tiles<const W: usize>(
    stage: &mut [F64],
    msg: &[F64],
    t0: usize,
    log_step: usize,
    msg_rows: usize,
    n_lanes: usize,
    row_words: usize,
    lane0: usize,
) {
    let rows = stage.len() / (BATCH * W);
    let pad = row_words - n_lanes;
    // Lane block of line `k` of the tile, which is lane `lane0 + k`.
    let block = |k: usize| row_words - 1 - (lane0 + k);
    // The lines of a tile that are padding lanes.
    let pad_lines = (0..W).filter(|k| lane0 + k < pad).fold(0u8, |m, k| m | 1 << k);
    for i in 0..rows {
        // Line `k` of the tile: 8 residues of one lane block, or zeros for a padding lane.
        let src: [usize; W] = std::array::from_fn(|k| block(k) * msg_rows + t0 + (i << log_step));
        fill_tile::<W>(stage, i * BATCH, msg, src, pad_lines);
    }
}

/// Write `stage[(tile + s) * W + k] = msg[src[k] + s]` for the 8 x `W` words of `W` lines, a line in `zeros` being
/// zeros.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
fn fill_tile<const W: usize>(stage: &mut [F64], tile: usize, msg: &[F64], src: [usize; W], zeros: u8) {
    use core::arch::x86_64::*;
    use primitives::simd::{load, store, transpose8};
    if W != 8 {
        return fill_tile_ymm::<W>(stage, tile, msg, src, zeros);
    }
    let r: [__m512i; 8] = std::array::from_fn(|k| {
        if zeros >> k & 1 == 1 {
            _mm512_setzero_si512()
        } else {
            load(&msg[src[k]..], 0)
        }
    });
    let cols = transpose8(r);
    for (s, col) in cols.into_iter().enumerate() {
        store(stage, tile + s, col);
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
use fill_tile_ymm as fill_tile;

/// [`fill_tile`] as one 4x4 transpose of YMM halves per half of each quad of lines.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "avx2")]
fn fill_tile_ymm<const W: usize>(stage: &mut [F64], tile: usize, msg: &[F64], src: [usize; W], zeros: u8) {
    use core::arch::x86_64::*;
    use primitives::{load_at, store_at};
    // Line `k`, half `h`: words `4h..4h + 4` of the line's 8 residues.
    let r: [[__m256i; 2]; W] = std::array::from_fn(|k| {
        if zeros >> k & 1 == 1 {
            [_mm256_setzero_si256(); 2]
        } else {
            [load_at(msg, src[k]), load_at(msg, src[k] + 4)]
        }
    });
    // Residue `s` is word `s` of every line: lines `4q..4q + 4` at words `4q..4q + 4` of its row.
    for h in 0..2 {
        for q in 0..W / 4 {
            let t = |k: usize| r[4 * q + k][h];
            let (a0, a1) = (_mm256_unpacklo_epi64(t(0), t(1)), _mm256_unpackhi_epi64(t(0), t(1)));
            let (a2, a3) = (_mm256_unpacklo_epi64(t(2), t(3)), _mm256_unpackhi_epi64(t(2), t(3)));
            let cols = [
                _mm256_permute2x128_si256::<0x20>(a0, a2),
                _mm256_permute2x128_si256::<0x20>(a1, a3),
                _mm256_permute2x128_si256::<0x31>(a0, a2),
                _mm256_permute2x128_si256::<0x31>(a1, a3),
            ];
            for (i, col) in cols.into_iter().enumerate() {
                store_at(stage, (tile + 4 * h + i) * W + 4 * q, col);
            }
        }
    }
}

/// [`fill_tile`] word by word.
#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "avx512f"),
    all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f"))
)))]
#[inline(always)]
fn fill_tile<const W: usize>(stage: &mut [F64], tile: usize, msg: &[F64], src: [usize; W], zeros: u8) {
    for s in 0..8 {
        for k in 0..W {
            stage[(tile + s) * W + k] = if zeros >> k & 1 == 1 {
                F64::ZERO
            } else {
                msg[src[k] + s]
            };
        }
    }
}
