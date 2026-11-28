//! Parallel execution of a loop's iterations, as segments whose merged result is the serial run's, row for row and cell
//! for cell.
//!
//! A loop is found by its witness: a stream one hint pops, long enough, is taken to be popped once per iteration at the
//! iteration's first instruction. The run goes serially to the start of iteration 2, predicts every later iteration's
//! start (frame, `next_free`, stream cursors, and the arguments the previous iteration wrote into its frame) as linear in
//! its index, runs iterations `2..n-1` as one segment per pool thread, merges them in serial order, and goes on serially
//! from iteration `n-1`. Only a loop whose frames were all reserved before it started is tried.
//!
//! A segment owns its iterations' frames and heap at or above [`LOW`] and writes them in place. It reaches every other
//! cell through its overlay, which starts from memory as the dispatch found it, from the predicted arguments, or unwritten
//! for the next segment's first frame. The merge replays each segment against memory in serial order: it checks that the
//! segment ended where the next one was predicted to start, adds the links its own cells hold to memory's, replays its links and stores on overlay cells through the serial
//! `deref_cell` and `put`, and checks that no cell it saw unwritten had been written before its turn. Once every link is
//! in place, a class of linked cells holds the one value any of its cells was given, in whatever order the links and
//! stores came, so the image is the serial one; a segment gives up where its own decisions could depend on that order (a
//! read of a cell it did not see written, a test of a linked own cell). Any failed check, fault, or touch of another
//! segment's cells sends the whole run back to a serial rerun, which reports any error as the serial run does.

use std::ops::Range;

use super::execute::{
    Cell, ExecError, FastMap as HashMap, Lanes, MAX_STEPS, Machine, Mem, PAGE, PAGE_LOG, Plan, Run, State, Stop, walk,
};
use super::hints::{GPow, MAX_CELLS};
use crate::keccak::Steps;
use isa::KECCAK_WINDOW;
use parallel::SendPtr;
use primitives::field::{F64, F128};

/// Cells a range check of a bound up to `2^16` reaches, which no segment owns. It decides how often segments merge,
/// never what a run computes.
const LOW: u32 = 1 << 16;
/// Fewest iterations per segment: fewer cost more to merge than they save.
const MIN_ITERATIONS: usize = 8;

/// Whether a stream of `entries` may be a loop's that runs as segments: the two iterations that predict the rest, the
/// last, and two segments.
pub(super) fn may_be_loop(entries: usize) -> bool {
    entries >= 3 + 2 * MIN_ITERATIONS
}

/// An iteration's start, at the loop's pc.
#[derive(Clone, PartialEq, Eq)]
struct Start {
    fp: u32,
    next_free: u32,
    cursors: Vec<usize>,
}

fn start_of(run: &Run<'_>) -> Start {
    Start {
        fp: run.fp,
        next_free: run.next_free,
        cursors: run.streams.iter().map(|s| s.next).collect(),
    }
}

/// The loop at `pc`, which pops `stream`: every iteration's start, linear in its index from iteration 2's.
struct Prediction {
    pc: u32,
    stream: u32,
    at2: Start,
    stride: u32,
    dnf: u32,
    dcur: Vec<usize>,
    /// The frame cells an iteration finds written as it starts, by offset: iteration 2's cell, and the ratio of its word
    /// to iteration 1's.
    args: Vec<(u32, Cell, F64)>,
}

impl Prediction {
    fn start(&self, k: usize) -> Start {
        let j = k - 2;
        Start {
            fp: self.at2.fp + j as u32 * self.stride,
            next_free: self.at2.next_free + j as u32 * self.dnf,
            cursors: self
                .at2
                .cursors
                .iter()
                .zip(&self.dcur)
                .map(|(c, d)| c + j * d)
                .collect(),
        }
    }

    /// Iteration `k`'s argument cells.
    fn args(&self, k: usize) -> HashMap<u32, Cell> {
        let fp = self.start(k).fp;
        self.args
            .iter()
            .map(|&(o, cell, ratio)| {
                (
                    fp + o,
                    Cell {
                        word: cell.word.mul_base(ratio.pow((k - 2) as u128)),
                        ..cell
                    },
                )
            })
            .collect()
    }

    /// The cells iterations `a..b` own: their frames and heap, at and above `LOW`.
    fn own(&self, a: usize, b: usize) -> [Range<u32>; 2] {
        let (start, end) = (self.start(a), self.start(b));
        [
            start.fp.max(LOW)..end.fp.max(LOW),
            start.next_free.max(LOW)..end.next_free.max(LOW),
        ]
    }

    fn stop(&self, pops: usize) -> Stop {
        Stop::At {
            pc: self.pc,
            stream: self.stream,
            pops,
        }
    }
}

fn touched(c: &Cell) -> bool {
    c.state != State::Unwritten
}

/// The prediction of the loop at `pc`, which pops `stream`, from iterations 1 and 2.
fn predict(m: &Mem<'_>, pc: u32, stream: u32, at1: Start, frame1: &[Cell], at2: Start) -> Option<Prediction> {
    let stride = at2.fp.checked_sub(at1.fp).filter(|&d| d != 0)?;
    let dnf = at2.next_free.checked_sub(at1.next_free)?;
    let dcur: Vec<usize> = at2
        .cursors
        .iter()
        .zip(&at1.cursors)
        .map(|(b, a)| b.checked_sub(*a))
        .collect::<Option<_>>()?;
    if dcur[stream as usize] != 1 || stride as usize != frame1.len() {
        return None;
    }
    let mut args = Vec::new();
    for o in 0..stride {
        let (c1, c2) = (frame1[o as usize], m.cell(at2.fp + o));
        let arg = c1.state == State::Written && c2.state == State::Written;
        if at1.fp + o < LOW {
            // A range check may have touched the cell; what is not an argument is memory's.
            if !arg {
                continue;
            }
        } else if touched(&c1) != touched(&c2) || (touched(&c2) && !arg) {
            return None;
        } else if !touched(&c2) {
            continue;
        }
        let ratio = if c1.word == c2.word {
            F64::ONE
        } else if c1.word.is_zero() {
            return None;
        } else {
            (c2.word * c1.word.inv()).as_base()?
        };
        args.push((o, c2, ratio));
    }
    Some(Prediction {
        pc,
        stream,
        at2,
        stride,
        dnf,
        dcur,
        args,
    })
}

thread_local! {
    /// Loops this thread dispatched as segments, and merged.
    pub(super) static LOOPS: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}

/// Run `run` to its end, every loop the plan marks that qualifies as segments: `false` if a segment's check failed and
/// the run has to start over serially. An error is the serial run's own, from a part it ran serially.
pub(super) fn run(
    plan: &Plan<'_>,
    m: &mut Mem<'_>,
    run: &mut Run<'_>,
    step: &mut dyn Steps,
) -> Result<bool, ExecError> {
    while walk(plan, m, run, step, Stop::First)? {
        let (pc, s) = (run.pc, plan.mark(run.pc).expect("a marked pc"));
        let (n, fp0, nf0) = (run.streams[s as usize].len(), run.fp, run.next_free);
        let stop = |pops| Stop::At { pc, stream: s, pops };
        if !walk(plan, m, run, step, stop(1))? {
            break;
        }
        let at1 = start_of(run);
        let heap0 = at1.next_free - nf0;
        // Iteration 1's frame as it starts: reserved frames lie a stride apart, and a frame is far smaller than `LOW`.
        if at1.fp.saturating_sub(fp0) > LOW {
            continue;
        }
        let frame1: Vec<Cell> = (at1.fp..at1.fp + at1.fp.saturating_sub(fp0))
            .map(|c| m.cell(c))
            .collect();
        if !walk(plan, m, run, step, stop(2))? {
            break;
        }
        let Some(pred) = predict(m, pc, s, at1, &frame1, start_of(run)) else {
            continue;
        };
        let segments = ((n - 3) / MIN_ITERATIONS).min(parallel::num_threads());
        // Only a loop whose frames were all reserved before it started: an inner loop's stream, popped across many runs
        // of the loop, predicts frames past them. The segments write their own cells in place and read the shared
        // g-power table, so both have to reach the last iteration's heap before they start: only a heap that grew alike
        // in iterations 0 and 1, so that one iteration's growth does not reserve memory the serial run never uses. An
        // aligned frame's padding depends on where the heap starts modulo the window: iterations 1 and 2 starting at the
        // same residue grow alike, and iteration 0 only by its first padding.
        let j = (n - 3) as u64;
        let reserved = u64::from(pred.at2.fp) + (j + 1) * u64::from(pred.stride) <= u64::from(nf0);
        let reach = u64::from(pred.at2.next_free) + j * u64::from(pred.dnf);
        let alike =
            pred.dnf == heap0 || (pred.dnf.is_multiple_of(KECCAK_WINDOW) && pred.dnf.abs_diff(heap0) < KECCAK_WINDOW);
        if segments < 2 || !reserved || !alike || reach >= u64::from(MAX_CELLS) {
            continue;
        }
        let bounds: Vec<usize> = (0..=segments).map(|c| 2 + c * (n - 3) / segments).collect();
        if !unseen_is_empty(m, &pred, &bounds) {
            continue;
        }
        m.reserve(reach as usize);
        m.g.grow_to(reach as usize);
        let merged = dispatch(plan, m, run, step, &pred, &bounds);
        LOOPS.with(|l| l.set((l.get().0 + 1, l.get().1 + usize::from(merged))));
        if !merged {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Whether memory holds nothing about the segments' own cells that a segment would not see: links from them, which
/// live in memory's map and not the segment's, or anything in a later segment's first frame, which the segment before
/// it takes as unwritten and its own predicted arguments overwrite.
fn unseen_is_empty(m: &Mem<'_>, pred: &Prediction, bounds: &[usize]) -> bool {
    let own = pred.own(bounds[0], bounds[bounds.len() - 1]);
    !m.links.keys().any(|k| own.iter().any(|r| r.contains(k)))
        && bounds[1..bounds.len() - 1].iter().all(|&b| {
            let fp = pred.start(b).fp;
            (fp.max(LOW)..fp + pred.stride).all(|c| !touched(&m.cell(c)))
        })
}

/// Cell `c` among memory's `pages`, if its page exists. The segments share the pages: each writes only its own cells,
/// and reads only cells no segment writes.
#[inline(always)]
fn cell_ptr(pages: &[SendPtr<Cell>], c: u32) -> Option<*mut Cell> {
    let c = c as usize;
    pages.get(c >> PAGE_LOG).map(|p| p.0.wrapping_add(c & (PAGE - 1)))
}

type Out<'a, 'w> = (Run<'w>, Segment<'a>, Vec<Lanes>);

/// Run iterations `bounds[0]..bounds[last]` as segments from `run`, which is at the first's start, and merge them:
/// whether every segment's checks held.
fn dispatch(
    plan: &Plan<'_>,
    m: &mut Mem<'_>,
    run: &mut Run<'_>,
    step: &mut dyn Steps,
    pred: &Prediction,
    bounds: &[usize],
) -> bool {
    let segments = bounds.len() - 1;
    // Where the segments' own cells begin: below it, every cell is as the dispatch found it.
    let par_lo = pred
        .own(bounds[0], bounds[segments])
        .into_iter()
        .filter(|r| !r.is_empty())
        .map(|r| r.start)
        .min();
    let pages = m.page_ptrs();
    // The segments share the table, which the merge does not use.
    let g = std::mem::replace(&mut m.g, GPow::new(0));
    let outs: Vec<Option<Out>> = crate::stage!("Run segments", || {
        parallel::map_collect(segments, |c| {
            let (a, b) = (bounds[c], bounds[c + 1]);
            let (start, end) = (pred.start(a), pred.start(b));
            let mut seeds = pred.args(a);
            // The arguments in the segment's own first frame go in place, where the first segment's are already.
            seeds.retain(|&cell, seed| {
                if cell >= LOW && c != 0 {
                    // SAFETY: the cell is this segment's own, in a reserved page.
                    unsafe { *cell_ptr(&pages, cell).expect("a reserved page") = *seed };
                }
                cell < LOW
            });
            let mut seg = Segment {
                pages: &pages,
                own: pred.own(a, b),
                next: end.fp.max(LOW)..end.fp + pred.stride,
                par_lo: par_lo.unwrap_or(u32::MAX),
                seeds,
                overlay: HashMap::default(),
                links: HashMap::default(),
                events: Vec::new(),
                used: 0,
                abandoned: false,
                g: &g,
                cache: HashMap::default(),
            };
            let streams = run
                .streams
                .iter()
                .zip(&start.cursors)
                .map(|(s, &next)| {
                    let mut s = s.clone();
                    s.next = next;
                    s
                })
                .collect();
            let mut r = Run::new(pred.pc, start.fp, start.next_free, streams);
            let mut lanes = Vec::new();
            let walked = walk(plan, &mut seg, &mut r, &mut |l: &Lanes| lanes.push(*l), pred.stop(b));
            (matches!(walked, Ok(true)) && !seg.abandoned).then_some((r, seg, lanes))
        })
    });
    let merged = crate::stage!("Merge segments", || {
        let Some(mut outs) = outs.into_iter().collect::<Option<Vec<_>>>() else {
            return false;
        };
        // Each segment's first step in the serial run: the steps before it.
        let mut firsts = Vec::with_capacity(segments);
        let merged = (outs.iter_mut().enumerate()).all(|(c, (r, seg, _))| {
            firsts.push(run.steps as u32);
            merge(m, run, r, seg, pred, bounds[c + 1], c + 1 == segments).is_some()
        });
        if !merged {
            return false;
        }
        finish(run, &outs, &firsts, step);
        true
    });
    m.g = g;
    merged
}

/// Merge segment `seg`, which ran `r` up to iteration `b`, into `m` and `run`, but for its rows and Keccak steps
/// ([`finish`]), or `None` if one of its checks failed.
fn merge(
    m: &mut Mem<'_>,
    run: &mut Run<'_>,
    r: &Run<'_>,
    seg: &mut Segment<'_>,
    pred: &Prediction,
    b: usize,
    last: bool,
) -> Option<()> {
    let end = pred.start(b);
    // A step limit the serial run would have reached inside the segments.
    run.steps += r.steps;
    if run.steps > MAX_STEPS || start_of(r) != end || seg.seeds.iter().any(|(&cell, seed)| m.cell(cell) != *seed) {
        return None;
    }
    // The next segment's first frame at and above `LOW` is that segment's own, already in memory: what this one wrote
    // there has to be the arguments it assumed.
    let held = if last { 0..0 } else { seg.next.clone() };
    if !last {
        let next = pred.args(b);
        let cell = |c: Option<&Cell>| c.copied().unwrap_or(Cell::UNWRITTEN);
        if held.clone().any(|c| cell(seg.overlay.get(&c)) != cell(next.get(&c))) {
            return None;
        }
    }
    let skip = |c: u32| held.contains(&c);
    // Its own cells and their links go in before its events: an event reads an own cell as written, and a value it
    // stores into one spreads through them, as serially.
    if seg.used > m.used {
        m.ensure(seg.used - 1);
    }
    for (k, v) in std::mem::take(&mut seg.links) {
        if seg.own(k) {
            m.links.entry(k).or_default().extend(v);
        }
    }
    for e in &seg.events {
        let ok = match *e {
            Event::Put(c, v) => skip(c) || m.put(c, v).is_ok(),
            // A link into the next segment's first frame (a loop argument stored through the next frame's pointer):
            // that cell already holds the argument predicted for it, which this segment was checked to agree with,
            // so serially both ends end up written with one word.
            Event::Link(a2, a3) => match (skip(a2), skip(a3)) {
                (false, false) => m.deref_cell(a2, a3).is_ok(),
                (true, true) => false,
                _ => m.is_written(a2) && m.is_written(a3) && m.cell(a2).word == m.cell(a3).word,
            },
            Event::Unwritten(c) => skip(c) || !m.is_written(c),
        };
        if !ok {
            return None;
        }
    }
    (run.fp, run.next_free) = (end.fp, end.next_free);
    for (s, &next) in run.streams.iter_mut().zip(&end.cursors) {
        s.next = next;
    }
    Some(())
}

/// Append the merged segments' rows to the run's in serial order, each segment's steps counted from `firsts`, its
/// first step in the serial run, and hand their Keccak steps on.
fn finish(run: &mut Run<'_>, outs: &[Out], firsts: &[u32], step: &mut dyn Steps) {
    step.steps(&outs.iter().map(|o| o.2.as_slice()).collect::<Vec<_>>());
    let parts: Vec<_> = outs.iter().zip(firsts).map(|(o, &first)| (&o.0.rows, first)).collect();
    run.rows.append(&parts);
}

/// What a segment did to an overlay cell that the merge replays, in the segment's order.
enum Event {
    /// A store wrote it.
    Put(u32, F128),
    /// A `DEREF` equated these two cells, one an overlay cell.
    Link(u32, u32),
    /// A hint or an instruction found it unwritten.
    Unwritten(u32),
}

/// A segment's machine: its own cells in place, every other one in its overlay.
struct Segment<'a> {
    pages: &'a [SendPtr<Cell>],
    /// Its frames and heap, at and above `LOW`.
    own: [Range<u32>; 2],
    /// The next segment's first frame at and above `LOW`, which that segment writes.
    next: Range<u32>,
    /// Where the segments' own cells begin.
    par_lo: u32,
    /// Its predicted arguments below `LOW`.
    seeds: HashMap<u32, Cell>,
    overlay: HashMap<u32, Cell>,
    links: HashMap<u32, Vec<u32>>,
    events: Vec<Event>,
    used: usize,
    abandoned: bool,
    g: &'a GPow,
    /// Exponents this segment announced or resolved, which the shared table does not index.
    cache: HashMap<u64, u32>,
}

impl Segment<'_> {
    #[inline(always)]
    fn own(&self, c: u32) -> bool {
        self.own[0].contains(&c) || self.own[1].contains(&c)
    }

    #[inline(always)]
    fn slot(&mut self, c: u32) -> &mut Cell {
        if self.own(c) {
            // SAFETY: an own cell, in a reserved page, which no other segment reads or writes.
            unsafe { &mut *cell_ptr(self.pages, c).expect("a reserved page") }
        } else {
            self.over(c)
        }
    }

    fn over(&mut self, c: u32) -> &mut Cell {
        let next = self.next.contains(&c);
        // Another segment's cell, or past every segment's.
        let foreign = !next && c >= LOW && c >= self.par_lo;
        self.abandoned |= foreign;
        let (seeds, pages) = (&self.seeds, self.pages);
        self.overlay.entry(c).or_insert_with(|| match seeds.get(&c) {
            Some(seed) => *seed,
            None if next || foreign => Cell::UNWRITTEN,
            // SAFETY: `cell_ptr` reads inside a whole page. Segments write only their `own` cells, at or above
            // `LOW` and `par_lo`: `Prediction::start` rises with `k` (`run` checks it does not wrap), so each
            // `own(a, b)` nests in `own(bounds[0], bounds[last])`, whose least start is `par_lo`.
            None => cell_ptr(pages, c).map_or(Cell::UNWRITTEN, |p| unsafe { *p }),
        })
    }

    /// A hint or an instruction decides on cell `c`'s state.
    #[inline(always)]
    fn observe(&mut self, c: u32) -> Cell {
        let own = self.own(c);
        let cell = *self.slot(c);
        match (cell.state, own) {
            (State::Written, _) | (State::Unwritten, true) => {}
            // Whether the serial run would find a value here depends on other iterations.
            (State::Linked, true) => self.abandoned = true,
            (_, false) => self.events.push(Event::Unwritten(c)),
        }
        cell
    }

    /// `put` on one cell; whether it was linked.
    #[inline(always)]
    fn store(&mut self, cell: u32, v: F128) -> bool {
        let own = self.own(cell);
        let c = self.slot(cell);
        let s = c.state;
        if s == State::Written && c.word != v {
            // A conflict, which the serial rerun reports.
            self.abandoned = true;
            return false;
        }
        c.word = v;
        c.state = State::Written;
        if !own && s != State::Written {
            self.events.push(Event::Put(cell, v));
        }
        s == State::Linked
    }

    #[cold]
    fn spread(&mut self, cell: u32, v: F128) {
        let mut todo = vec![cell];
        while let Some(c) = todo.pop() {
            for p in self.links.remove(&c).unwrap_or_default() {
                if self.store(p, v) {
                    todo.push(p);
                }
            }
        }
    }

    fn link(&mut self, a: u32, b: u32) {
        for (x, y) in [(a, b), (b, a)] {
            self.ensure(x as usize);
            let c = self.slot(x);
            if c.state == State::Unwritten {
                c.state = State::Linked;
            }
            self.links.entry(x).or_default().push(y);
        }
    }
}

impl Machine for Segment<'_> {
    #[inline(always)]
    fn ensure(&mut self, idx: usize) {
        self.used = self.used.max(idx + 1);
    }
    #[inline(always)]
    fn written(&mut self, cell: u32) -> bool {
        self.observe(cell).state == State::Written
    }
    #[inline(always)]
    fn get(&mut self, cell: u32) -> F128 {
        self.observe(cell).word
    }
    #[inline(always)]
    fn read(&mut self, cell: u32) -> F128 {
        self.ensure(cell as usize);
        let c = *self.slot(cell);
        // An unconstrained read, which every proof refuses: the serial rerun reports it.
        self.abandoned |= c.state != State::Written;
        c.word
    }
    #[inline(always)]
    fn put(&mut self, cell: u32, v: F128) -> Result<(), ExecError> {
        self.ensure(cell as usize);
        if self.store(cell, v) {
            self.spread(cell, v);
        }
        Ok(())
    }
    #[inline(always)]
    fn deref_cell(&mut self, a2: u32, a3: u32) -> Result<(), ExecError> {
        if !self.own(a2) || !self.own(a3) {
            self.events.push(Event::Link(a2, a3));
        }
        let (c2, c3) = (*self.slot(a2), *self.slot(a3));
        if c2.state == State::Written {
            self.put(a3, c2.word)
        } else if c3.state == State::Written {
            self.put(a2, c3.word)
        } else {
            self.link(a2, a3);
            Ok(())
        }
    }
    #[inline(always)]
    fn abandoned(&self) -> bool {
        self.abandoned
    }
    fn g_note(&mut self, k: usize) {
        if self.g.covers(k) {
            self.cache.insert(self.g.pow(k).0, k as u32);
        } else {
            self.abandoned = true;
        }
    }
    #[inline(always)]
    fn g_grow(&mut self, upto: usize) {
        self.abandoned |= !self.g.covers(upto);
    }
    #[inline(always)]
    fn g_pow(&mut self, k: usize) -> F64 {
        if self.g.covers(k) {
            self.g.pow(k)
        } else {
            self.abandoned = true;
            F64::ONE
        }
    }
    #[inline(always)]
    fn g_log_below(&mut self, x: F64, bound: usize) -> Option<u32> {
        // The exponent is the discrete log whichever table finds it, so it is the serial run's.
        let k = match self.g.lookup(x).or_else(|| self.cache.get(&x.0).copied()) {
            Some(k) => k,
            None => {
                let k = self.g.find(x, bound)?;
                self.cache.insert(x.0, k);
                k
            }
        };
        ((k as usize) < bound).then_some(k)
    }
}

#[cfg(test)]
mod tests;
