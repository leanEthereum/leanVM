//! Where the layer-`start` blocks of a transform come from: the message and its layout.

use primitives::field::F64;

use super::stage::transpose_lane_major;
use super::window::Window;

/// Where the layer-`start` blocks of a transform come from.
///
/// - It is a `Copy` enum of what the passes read, so a pass matches on it once per group.
/// - The first pass takes it, and every pass after that reads the buffer.
#[derive(Clone, Copy)]
pub(super) enum Source<'a> {
    /// The buffer holds them: every pass after the first, and the tests' plain transform.
    Replicas,
    /// Each is a copy of the buffer's own block 0, which the first pass overwrites last.
    InPlace,
    /// Each is a copy of this row-major message.
    Rows(&'a [F64]),
    /// Each is this lane-major message transposed; the buffer holds the cosets from its `first_row` on.
    Lanes(Lanes<'a>),
}

/// A lane-major message: `n_lanes` lane blocks, each as long as the message has rows.
#[derive(Clone, Copy)]
pub(super) struct Lanes<'a> {
    pub(super) words: &'a [F64],
    pub(super) n_lanes: usize,
}

impl<'a> Source<'a> {
    /// The source for the first pass, leaving [`Source::Replicas`] for the passes after it.
    pub(super) fn take(&mut self) -> Self {
        std::mem::replace(self, Source::Replicas)
    }

    /// Log of the rows of the whole domain this encode covers, with layers from `start`.
    ///
    /// A lane-major message gives its own length, and any other source the buffer's.
    pub(super) fn log_d(&self, win: &Window, start: usize) -> usize {
        match self {
            Source::Lanes(lanes) => primitives::log2_strict_usize(lanes.words.len() / lanes.n_lanes) + start,
            _ => primitives::log2_strict_usize(win.len() / win.num_ntts()),
        }
    }

    /// Transpose a lane-major message into block 0 of the buffer, which then holds it in place.
    pub(super) fn transpose_into(self, win: &mut Window, log_rows: usize) -> Self {
        let Source::Lanes(lanes) = self else { return self };
        let num_ntts = win.num_ntts();
        let out = &mut win.words_mut()[..num_ntts << log_rows];
        transpose_lane_major(out, lanes.words, lanes.n_lanes, num_ntts, log_rows);
        Source::InPlace
    }

    /// Fill every replica of the buffer, if a pass cannot build them itself.
    ///
    /// - A message that is block 0 of the buffer could be overwritten by a task while others still copy it.
    /// - With no layer left to run, no deep task would write the buffer at all.
    /// - Returns [`Source::Replicas`] when it copied, and the source unchanged otherwise.
    pub(super) fn replicate(self, win: &mut Window, start: usize, has_deep: bool) -> Self {
        let msg_len = win.len() >> start;
        match self {
            Source::InPlace => replicate(win, None, msg_len),
            Source::Rows(m) if !has_deep => replicate(win, Some(m), msg_len),
            other => return other,
        }
        Source::Replicas
    }
}

/// Fill every replica of the buffer with a copy of the message.
///
/// - This is the unfused form of a gathered first pass.
/// - With no `msg`, the message is the buffer's own first replica, which is left as it is.
fn replicate(win: &mut Window, msg: Option<&[F64]>, msg_len: usize) {
    // Copy granularity: small enough to spread a short message over every worker.
    const CHUNK: usize = 1 << 14;
    let replicas = win.len() / msg_len;
    let in_place = msg.is_none();
    let chunks = msg_len.div_ceil(CHUNK);
    let dst = win.base();
    let msg = parallel::SendPtr(msg.map_or(dst.0, |m| m.as_ptr().cast_mut()));
    // Replica index innermost, so one worker copies a chunk into several replicas while it is cached.
    parallel::for_each(chunks * replicas, |t| {
        let (c, replica) = (t / replicas, t % replicas);
        // The message already occupies replica 0.
        if in_place && replica == 0 {
            return;
        }
        let start = c * CHUNK;
        let len = CHUNK.min(msg_len - start);
        // SAFETY:
        // - Only this task writes this range.
        // - The range skips replica 0, so it never overlaps a message stored there.
        unsafe {
            let src = std::slice::from_raw_parts(msg.add(start), len);
            dst.slice(replica * msg_len + start, len).copy_from_slice(src);
        }
    });
}
