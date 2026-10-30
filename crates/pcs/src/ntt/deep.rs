//! The deep pass: the near layers, which hand their finished rows to the hasher while they are in L2.

use primitives::field::F64;
use primitives::stream::Stream;

use super::encode::RowSink;
use super::layers::Layers;
use super::plan::Plan;
use super::scratch::with_scratch;
use super::source::Source;
use super::window::Window;

/// The deep pass: layers `deep_start..log_d` over sub-blocks of `2^log_sub` rows, one task per run of sub-blocks.
///
/// - It owns the sub-block geometry, and the sink that takes each finished sub-block.
/// - With a separate message, each sub-block is built in scratch and written out once.
/// - Otherwise the buffer holds the replicas, and the layers run in place.
/// - With `defer`, an in-place sub-block is finished in scratch and the buffer keeps its pre-deep state.
/// - Each finished sub-block goes to the sink while it is in L2.
pub(super) struct DeepPass<'s> {
    plan: Plan,
    /// Log of the rows of a sub-block, its words, and the log of the sub-blocks the domain holds.
    log_sub: usize,
    sub_len: usize,
    outer: usize,
    defer: bool,
    sink: Option<&'s RowSink<'s>>,
}

impl<'s> DeepPass<'s> {
    pub(super) fn new(plan: &Plan, sink: Option<&'s RowSink<'s>>, defer: bool) -> Self {
        let log_sub = plan.log_sub();
        let outer = plan.log_d - log_sub;
        Self {
            plan: *plan,
            log_sub,
            sub_len: plan.num_ntts << log_sub,
            outer,
            defer,
            sink,
        }
    }

    pub(super) fn run(&self, layers: Layers, win: &mut Window, src: Source<'_>) {
        match src {
            Source::Rows(msg) => self.with_message(layers, win, msg),
            _ => self.in_place(layers, win),
        }
    }

    /// A separate message: build each sub-block in scratch, hash it, then write it out once.
    ///
    /// Streamed out whole, the codeword is written without ever being read.
    fn with_message(&self, layers: Layers, win: &mut Window, msg: &[F64]) {
        let Plan {
            log_d,
            num_ntts,
            start,
            deep_start,
            ..
        } = self.plan;
        let (sub_len, outer, log_sub, sink) = (self.sub_len, self.outer, self.log_sub, self.sink);
        let (base, total) = (win.base(), win.len());
        let block_len = total >> start;
        parallel::for_each_chunk(1 << outer, |lo, hi| {
            with_scratch(sub_len, |scratch| {
                // One fence at the end of the task covers all its streaming stores.
                let stream = win.stream().then(Stream::new);
                for sub_idx in lo..hi {
                    // A task sits at the same offset in every replica, or covers whole replicas.
                    //
                    //     task at offset off of its replica  <-  message words [off, off + sub_len)
                    let off = (sub_idx * sub_len) % block_len;
                    // Inside one replica the first sweep reads the message; across several it is copied in.
                    let from = (sub_len <= block_len).then(|| &msg[off..][..sub_len]);
                    if from.is_none() {
                        let copy = |part: &mut [F64]| part.copy_from_slice(&msg[..part.len()]);
                        scratch.chunks_mut(block_len).for_each(copy);
                    }
                    layers.run(scratch, from, log_d, num_ntts, deep_start, log_d, outer, sub_idx, None);
                    if let Some(f) = sink {
                        f(sub_idx << log_sub, scratch);
                    }
                    // SAFETY: the sub-block lies inside the codeword, and this task alone owns it.
                    let dst = unsafe { std::slice::from_raw_parts_mut(base.add(sub_idx * sub_len), sub_len) };
                    match &stream {
                        Some(s) => s.copy(dst, scratch),
                        None => dst.copy_from_slice(scratch),
                    }
                }
            });
        });
    }

    /// The buffer holds the replicas: run the layers where they are, or in scratch when deferred.
    fn in_place(&self, layers: Layers, win: &mut Window) {
        let Plan {
            log_d,
            num_ntts,
            deep_start,
            ..
        } = self.plan;
        let (sub_len, outer, log_sub, sink) = (self.sub_len, self.outer, self.log_sub, self.sink);
        let (first_coset, start) = (win.first_coset(), self.plan.start);
        parallel::chunks_mut(win.words_mut(), sub_len, |local, sub| {
            // The buffer's first sub-block, in the whole domain.
            let sub_idx = local + (first_coset << (log_d - start - log_sub));
            if self.defer && sink.is_some() {
                // The rows are hashed from scratch and the buffer keeps its pre-deep state.
                with_scratch(sub_len, |scratch| {
                    layers.run(
                        scratch,
                        Some(&*sub),
                        log_d,
                        num_ntts,
                        deep_start,
                        log_d,
                        outer,
                        sub_idx,
                        None,
                    );
                    if let Some(f) = sink {
                        f(sub_idx << log_sub, scratch);
                    }
                });
            } else {
                // The replicas are already in place: run the layers where they are.
                layers.run(sub, None, log_d, num_ntts, deep_start, log_d, outer, sub_idx, None);
                if let Some(f) = sink {
                    f(sub_idx << log_sub, sub);
                }
            }
        });
    }
}
