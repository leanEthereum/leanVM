//! The deep pass: the near layers, which hand their finished rows to the hasher while they are in L2.

use primitives::field::F64;
use primitives::stream::Stream;

use super::encode::RowSink;
use super::plan::Plan;
use super::scratch::with_scratch;
use super::source::Source;
use super::twiddles::AdditiveNttF64;
use super::window::Window;

/// The deep pass: layers `deep_start..log_d`, one task of `2^log_task` rows at a time, a run of sub-blocks.
///
/// - It owns the sub-block geometry, and the sink that takes each finished sub-block.
/// - With a separate message, each sub-block is built in scratch and written out once.
/// - Otherwise the buffer holds the replicas, and the layers run in place.
/// - With `defer`, an in-place sub-block is finished in scratch and the buffer keeps its pre-deep state.
/// - Each finished sub-block goes to the sink while it is in L2.
pub(super) struct DeepPass<'s> {
    plan: Plan,
    /// Log of the rows of a task, its words, and the log of the tasks the domain holds.
    log_task: usize,
    task_len: usize,
    outer: usize,
    defer: bool,
    sink: Option<&'s RowSink<'s>>,
}

impl<'s> DeepPass<'s> {
    pub(super) fn new(plan: &Plan, sink: Option<&'s RowSink<'s>>, defer: bool) -> Self {
        let log_task = plan.log_task();
        let outer = plan.log_d - log_task;
        Self {
            plan: *plan,
            log_task,
            task_len: plan.num_ntts << log_task,
            outer,
            defer,
            sink,
        }
    }

    pub(super) fn run(&self, ntt: &AdditiveNttF64, win: &mut Window, src: Source<'_>) {
        match src {
            Source::Rows(msg) => self.with_message(ntt, win, msg),
            _ => self.in_place(ntt, win),
        }
    }

    /// A separate message: build each task in scratch, hash it, then write it out once.
    ///
    /// Streamed out whole, the codeword is written without ever being read.
    fn with_message(&self, ntt: &AdditiveNttF64, win: &mut Window, msg: &[F64]) {
        let Plan {
            log_d,
            num_ntts,
            start,
            deep_start,
            ..
        } = self.plan;
        let (task_len, outer, log_task, sink) = (self.task_len, self.outer, self.log_task, self.sink);
        let (base, total) = (win.base(), win.len());
        let block_len = total >> start;
        parallel::for_each_chunk(1 << outer, |lo, hi| {
            with_scratch(task_len, |scratch| {
                // One fence at the end of the task covers all its streaming stores.
                let stream = win.stream().then(Stream::new);
                for task in lo..hi {
                    // A task sits at the same offset in every replica, or covers whole replicas.
                    //
                    //     task at offset off of its replica  <-  message words [off, off + task_len)
                    let off = (task * task_len) % block_len;
                    // Inside one replica the first sweep reads the message; across several it is copied in.
                    let from = (task_len <= block_len).then(|| &msg[off..][..task_len]);
                    if from.is_none() {
                        let copy = |part: &mut [F64]| part.copy_from_slice(&msg[..part.len()]);
                        scratch.chunks_mut(block_len).for_each(copy);
                    }
                    ntt.run_layers(scratch, from, log_d, num_ntts, deep_start, outer, task, None);
                    if let Some(f) = sink {
                        f(task << log_task, scratch);
                    }
                    // SAFETY: the task's rows lie inside the codeword, and this task alone owns them.
                    let dst = unsafe { std::slice::from_raw_parts_mut(base.add(task * task_len), task_len) };
                    match &stream {
                        Some(s) => s.copy(dst, scratch),
                        None => dst.copy_from_slice(scratch),
                    }
                }
            });
        });
    }

    /// The buffer holds the replicas: run the layers where they are, or in scratch when deferred.
    fn in_place(&self, ntt: &AdditiveNttF64, win: &mut Window) {
        let Plan {
            log_d,
            num_ntts,
            deep_start,
            ..
        } = self.plan;
        let (task_len, outer, log_task, sink) = (self.task_len, self.outer, self.log_task, self.sink);
        let first_task = win.first_row() >> log_task;
        parallel::chunks_mut(win.words_mut(), task_len, |local, words| {
            let task = first_task + local;
            if self.defer {
                // The rows are hashed from scratch and the buffer keeps its pre-deep state.
                with_scratch(task_len, |scratch| {
                    ntt.run_layers(scratch, Some(&*words), log_d, num_ntts, deep_start, outer, task, None);
                    if let Some(f) = sink {
                        f(task << log_task, scratch);
                    }
                });
            } else {
                // The replicas are already in place: run the layers where they are.
                ntt.run_layers(words, None, log_d, num_ntts, deep_start, outer, task, None);
                if let Some(f) = sink {
                    f(task << log_task, words);
                }
            }
        });
    }
}
