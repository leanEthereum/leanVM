//! Codeword rows read back from an encode that did not write its whole codeword.

use primitives::field::F64;

use super::encode::Codeword;
use super::plan::Plan;
use super::scratch::with_scratch;
use super::source::Lanes;
use super::stage::{BATCH, Stage};
use super::twiddles::AdditiveNttF64;

/// The rows at the sorted `positions` of a codeword kept whole, `row_words` words each, back to back.
fn gather_rows(words: &[F64], row_words: usize, positions: &[usize]) -> Vec<F64> {
    let mut out = Vec::with_capacity(positions.len() * row_words);
    for &q in positions {
        out.extend_from_slice(&words[q * row_words..][..row_words]);
    }
    out
}

/// The rows at the sorted `positions`, `n` words each, back to back.
///
/// - The rows group by the block of `2^log_block` rows that holds them, one pool task per block.
/// - `build(i, block, live, scratch)` writes block number `block`, the `i`-th one touched, into the thread's scratch.
/// - Only the rows `live` (sorted, within the block) must come out right, and only they are copied out of it.
pub(super) fn built_rows(
    n: usize,
    log_block: usize,
    positions: &[usize],
    build: impl Fn(usize, usize, &[usize], &mut [F64]) + Sync,
) -> Vec<F64> {
    debug_assert!(positions.is_sorted());
    let places: Vec<usize> = positions.iter().map(|q| q & ((1 << log_block) - 1)).collect();
    // SAFETY: the fill writes every element before it reads any.
    unsafe {
        primitives::filled_vec(positions.len() * n, |out| {
            let mut rest = out;
            let mut at = 0;
            let mut parts = positions
                .chunk_by(|a, b| a >> log_block == b >> log_block)
                .map(|run| {
                    let (head, tail) = std::mem::take(&mut rest).split_at_mut(run.len() * n);
                    rest = tail;
                    at += run.len();
                    (head, run, &places[at - run.len()..at])
                })
                .collect::<Vec<_>>();
            parallel::chunks_mut(&mut parts, 1, |i, part| {
                let (dst, run, live) = &mut part[0];
                let block = run[0] >> log_block;
                with_scratch(n << log_block, |scratch| {
                    build(i, block, live, scratch);
                    for (dst, &p) in dst.chunks_exact_mut(n).zip(live.iter()) {
                        dst.copy_from_slice(&scratch[p * n..][..n]);
                    }
                });
            });
        })
    }
}

/// The reads of codeword rows, from what an encode kept of its codeword.
impl AdditiveNttF64 {
    /// The rows at the sorted `positions` of `codeword`, back to back. A [`Codeword::Nothing`] is recomputed from
    /// its lane-major message `msg`, which no other codeword reads.
    pub fn rows(&self, codeword: &Codeword, msg: &[F64], positions: &[usize]) -> Vec<F64> {
        match *codeword {
            Codeword::Whole(ref words, plan) => gather_rows(words, plan.num_ntts, positions),
            Codeword::BeforeDeep(ref words, plan) => {
                let sub_len = plan.sub_len();
                self.finished_rows(&plan, positions, |_, sub| &words[sub * sub_len..][..sub_len])
            }
            Codeword::Nothing(plan, n_lanes) => {
                let log_sub = plan.log_sub();
                let mut subs: Vec<usize> = positions.iter().map(|q| q >> log_sub).collect();
                subs.dedup();
                let built = Rebuild::new(&plan, Lanes { words: msg, n_lanes }, &subs).run(self);
                let sub_len = plan.sub_len();
                self.finished_rows(&plan, positions, |i, _| &built[i * sub_len..][..sub_len])
            }
        }
    }

    /// The rows at `positions` (sorted), back to back, from the sub-blocks before their deep layers.
    ///
    /// `src(i, sub)` is the `i`-th sub-block, number `sub` in the codeword. Each finishes into the thread's
    /// scratch, so only the queried rows are written.
    fn finished_rows<'a>(
        &self,
        plan: &Plan,
        positions: &[usize],
        src: impl Fn(usize, usize) -> &'a [F64] + Sync,
    ) -> Vec<F64> {
        let Plan {
            log_d,
            num_ntts,
            deep_start,
            ..
        } = *plan;
        built_rows(num_ntts, plan.log_sub(), positions, |i, sub_idx, live, sub| {
            let src = Some(src(i, sub_idx));
            self.run_layers(sub, src, log_d, num_ntts, deep_start, deep_start, sub_idx, Some(live));
        })
    }
}

/// The re-run of the gathered pass of an encode that kept no buffer, for the sub-blocks a query reads.
///
/// - The encode ran one gathered pass over its lane-major message: a group is one residue of one coset,
///   and its transform leaves row `i` of the group as row `r` of sub-block `coset << g | i`, `g` layers deep.
/// - So each group transforms again here, skipping the blocks that feed no row of the sub-blocks,
///   and keeps only the rows that fall in one of them.
/// - It owns the [`Stage`] of that pass and, per coset with queried sub-blocks, the rows it keeps.
struct Rebuild<'a> {
    plan: Plan,
    stage: Stage<'a>,
    /// Each coset with queried sub-blocks: its index, those sub-blocks' places in `subs`, and their group rows.
    cosets: Vec<(usize, std::ops::Range<usize>, Vec<usize>)>,
    n_subs: usize,
}

impl<'a> Rebuild<'a> {
    /// The rebuild of the deep sub-blocks `subs` (sorted, distinct).
    ///
    /// # Panics
    ///
    /// Panics unless the encode had the plan this reads back: one lane-major gathered pass.
    fn new(plan: &Plan, lanes: Lanes<'a>, subs: &[usize]) -> Self {
        let Plan {
            log_d,
            num_ntts,
            start,
            deep_start,
            ..
        } = *plan;
        let g = deep_start - start;
        let (rows, log_step) = (1usize << g, plan.log_sub());
        let msg_rows = 1usize << (log_d - start);
        assert!(plan.rebuilds_from_lanes(), "one gathered pass reads the lanes");
        assert_eq!(lanes.words.len(), lanes.n_lanes * msg_rows);
        let mut next = 0;
        let cosets = subs
            .chunk_by(|a, b| a >> g == b >> g)
            .map(|run| {
                next += run.len();
                (
                    run[0] >> g,
                    next - run.len()..next,
                    run.iter().map(|sub| sub & (rows - 1)).collect(),
                )
            })
            .collect();
        let stage = Stage::new(lanes, log_step, msg_rows, num_ntts);
        Self {
            plan: *plan,
            stage,
            cosets,
            n_subs: subs.len(),
        }
    }

    /// The sub-blocks back to back, before their deep layers.
    fn run(&self, ntt: &AdditiveNttF64) -> Vec<F64> {
        let Plan {
            num_ntts,
            start,
            deep_start,
            ..
        } = self.plan;
        let (rows, log_step) = (1usize << (deep_start - start), self.plan.log_sub());
        let sub_len = self.plan.sub_len();
        // SAFETY: the groups below write every element, and `built` is read only once they are done.
        let mut built = unsafe { primitives::uninit_vec(self.n_subs * sub_len) };
        // A group writes row `r` of every queried sub-block, and the groups cover every residue `r`.
        let out = parallel::SendPtr(built.as_mut_ptr());
        parallel::for_each_chunk((1usize << log_step) / BATCH, |lo, hi| {
            // One octet of lanes of a batch of residues is 64 lanes of one transform.
            let stage_len = rows * BATCH * 8;
            // `built` is far larger than a node's L3 share and is read only after every task: its lines stream.
            let stream = primitives::stream::Stream::new();
            with_scratch(2 * stage_len, |all| {
                let (stage, scratch) = all.split_at_mut(stage_len);
                for t in lo..hi {
                    for octet in 0..num_ntts / 8 {
                        self.stage.fill(stage, t * BATCH, octet);
                        for (coset, run, live) in &self.cosets {
                            let live_rows = Some(&live[..]);
                            ntt.run_layers(
                                scratch,
                                Some(stage),
                                deep_start,
                                BATCH * 8,
                                start,
                                start,
                                *coset,
                                live_rows,
                            );
                            for (pos, &i) in run.clone().zip(live) {
                                for (s, line) in scratch[i * BATCH * 8..][..BATCH * 8]
                                    .as_chunks::<8>()
                                    .0
                                    .iter()
                                    .enumerate()
                                {
                                    // SAFETY: this task alone owns row `t * BATCH + s` of every sub-block,
                                    // and `built` outlives the tasks.
                                    let dst =
                                        unsafe { out.slice(pos * sub_len + (t * BATCH + s) * num_ntts + 8 * octet, 8) };
                                    stream.copy(dst, line);
                                }
                            }
                        }
                    }
                }
            });
        });
        built
    }
}
