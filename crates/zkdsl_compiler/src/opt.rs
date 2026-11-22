//! Copies out of the lowered code, then each frame compacted to the cells still in use.
//!
//! The lowering copies a value into a fresh cell (`LOp::Copy`, a `MUL d = s·1` by a cell it set to 1 on every path
//! there) wherever a value has to be at a place: an argument, a return cell, a `keccak` input, a loop frame's
//! argument. Three rewrites remove such a copy:
//!
//! - **Propagate**: `d` is a temporary the copy alone writes, read only after it in the same block. Its readers
//!   read `s` instead. They run after the copy, and the copy reads `s`, so `s` is written there too.
//! - **Retarget**: `d` is written by the copy alone and read nowhere else in this frame (a return cell, the next
//!   loop frame's argument), and `s` is a temporary of this frame, out of every run and hint. Renaming `s` to `d`
//!   throughout writes `d` where `s` was written, which the copy then only re-asserts.
//! - **Retarget in a block**: as above, but `d` may have other writers (a join's cell, written by each arm) and `s`
//!   be a `KECCAK` output: `s` lives only in the copy's block, so it is renamed there alone, its whole run with it.
//!
//! A copy still left into the next loop frame becomes a `DEREF` store through that frame's pointer: the same cell
//! written, on a `DEREF` row instead of a `MUL` one. A frame is then renumbered past its kept cells
//! (`Lowered::keep`) to the cells still referenced, in order, so a run stays consecutive; a cell of the next frame (a
//! loop's argument) moves with the frame's end.

use super::*;
use std::collections::HashSet;

/// How an instruction names a cell.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    /// Written, unless the instruction is a check of an already written cell.
    Dest,
    /// Read (a `MUL` operand may also be back-solved).
    Use,
    /// A `DEREF`'s frame side: written when not yet, else checked.
    DerefVal,
    /// The first of `n` consecutive cells read.
    Run(u32),
    /// The first of `n` consecutive cells written.
    OutRun(u32),
}

fn visit(op: &mut LOp, f: &mut dyn FnMut(&mut Off, Role)) {
    match op {
        LOp::MulNextFrame { .. } => unreachable!("made absolute first"),
        LOp::Set { o, .. } => f(o, Role::Dest),
        LOp::Xor { a, b, c } | LOp::Mul { a, b, c } => {
            f(a, Role::Use);
            f(b, Role::Use);
            f(c, Role::Dest);
        }
        LOp::Solve { x, b, c } => {
            f(x, Role::Dest);
            f(b, Role::Use);
            f(c, Role::Use);
        }
        LOp::Copy { src, one, dst } => {
            f(src, Role::Use);
            f(one, Role::Use);
            f(dst, Role::Dest);
        }
        LOp::Deref { o1, o3, mode, .. } => {
            f(o1, Role::Use);
            if *mode == DerefMode::Cell {
                f(o3, Role::DerefVal);
            }
        }
        LOp::Jump { oc, od, of } => {
            f(oc, Role::Use);
            f(od, Role::Use);
            f(of, Role::Use);
        }
        LOp::Slot { x, dst, .. } => {
            f(x, Role::Use);
            f(dst, Role::Dest);
        }
        LOp::Keccak {
            m,
            tail,
            b8,
            cap,
            c,
            out_cells,
            ..
        } => {
            for x in m {
                f(x, Role::Use);
            }
            f(tail, Role::Run(4));
            f(b8, Role::Use);
            f(cap, Role::Run(4));
            f(c, Role::OutRun(out_cells.cells() as u32));
        }
    }
}

/// Every frame cell a hint names, with the length of the run it starts.
fn visit_hint(h: &mut Hint, f: &mut dyn FnMut(&mut Off, u32)) {
    let bits = |b: &mut BitsDest, n: u32, f: &mut dyn FnMut(&mut Off, u32)| match b {
        BitsDest::Stack(base) => f(base, n),
        BitsDest::Heap(ptr) => f(ptr, 1),
    };
    match h {
        Hint::NextFrameAddress => {}
        Hint::AllocLoopFrames { ptr, count, .. } => {
            f(ptr, 1);
            if let LoopCount::Bound { cell, .. } = count {
                f(cell, 1);
            }
        }
        Hint::AllocFrame { ptr, .. } | Hint::AllocBuffer { ptr, .. } => f(ptr, 1),
        Hint::AllocFrameSwitch { ptr, x, .. } => {
            f(ptr, 1);
            f(x, 1);
        }
        Hint::AllocBufferDyn { ptr, size } => {
            f(ptr, 1);
            f(size, 1);
        }
        Hint::Resolved(r) => match r {
            RHint::FrameAddress { offset } => f(offset, 1),
            RHint::AllocFrames { ptr, end, .. } => {
                f(ptr, 1);
                f(end, 1);
            }
            RHint::Alloc { ptr, .. } => f(ptr, 1),
            RHint::AllocDyn { ptr, size } => {
                f(ptr, 1);
                f(size, 1);
            }
            RHint::AllocSwitch { ptr, x, .. } => {
                f(ptr, 1);
                f(x, 1);
            }
            RHint::WitnessStack { base, len, .. } => f(base, *len),
            RHint::WitnessHeap { ptr, .. } => f(ptr, 1),
            RHint::Log2Ceil {
                bits: b, dst, nbits, ..
            } => {
                bits(b, *nbits, f);
                f(dst, 1);
            }
            RHint::BitDecompose { value, bits: b, nbits } | RHint::BitDecomposeExp { value, bits: b, nbits } => {
                f(value, 1);
                bits(b, *nbits, f);
            }
            RHint::DigitDecomposeExp {
                value,
                dst,
                ndigits,
                start_cell,
                ..
            } => {
                f(value, 1);
                bits(dst, *ndigits, f);
                if let Some(c) = start_cell {
                    f(c, 1);
                }
            }
            RHint::WindowsExp {
                value, dest, at, count, ..
            } => {
                f(value, 1);
                bits(dest, *at + *count, f);
            }
            RHint::FieldLimbs { value, base, len } => {
                f(value, 1);
                f(base, *len);
            }
            RHint::Inverse { value, dst } => {
                f(value, 1);
                f(dst, 1);
            }
            RHint::Print { cell, .. } => f(cell, 1),
        },
    }
}

/// Cells `x..x + len` marked, at least `x`, those past `cells` ignored.
fn mark(cells: &mut [bool], x: Off, len: u32) {
    for c in x..x + len.max(1) {
        if let Some(cell) = cells.get_mut(c as usize) {
            *cell = true;
        }
    }
}

/// Every reference to `from` in the instructions `at` renamed to `to`.
fn rename(code: &mut [LInstr], at: impl IntoIterator<Item = usize>, from: Off, to: Off) {
    for j in at {
        visit(&mut code[j].op, &mut |x, _| {
            if *x == from {
                *x = to;
            }
        });
    }
}

/// The block holding instruction `i`, `starts` the blocks' first instructions.
fn block_of(starts: &[usize], i: usize) -> usize {
    starts.partition_point(|&s| s <= i) - 1
}

/// The end of block `b`: the next block's first instruction, or `n`.
fn block_end(starts: &[usize], b: usize, n: usize) -> usize {
    starts.get(b + 1).copied().unwrap_or(n)
}

/// What the live instructions name.
struct Refs {
    /// Per cell, every (instruction, role) naming it; a run's only at its first cell unless runs are spread.
    at: Vec<Vec<(usize, Role)>>,
    /// The cells a hint names.
    hinted: Vec<bool>,
    /// Every run, in instruction order: its instruction, first cell, length, and whether it is written.
    runs: Vec<(usize, Off, u32, bool)>,
}

impl Refs {
    fn new(code: &mut [LInstr], dead: &[bool], spread_runs: bool) -> Self {
        let mut at: Vec<Vec<(usize, Role)>> = Vec::new();
        let mut hinted = Vec::new();
        let mut runs = Vec::new();
        fn add(at: &mut Vec<Vec<(usize, Role)>>, x: Off, r: (usize, Role)) {
            if at.len() <= x as usize {
                at.resize(x as usize + 1, Vec::new());
            }
            at[x as usize].push(r);
        }
        for (i, ins) in code.iter_mut().enumerate().filter(|(i, _)| !dead[*i]) {
            for h in &mut ins.hints {
                visit_hint(h, &mut |x, len| {
                    let end = (*x + len.max(1)) as usize;
                    if hinted.len() < end {
                        hinted.resize(end, false);
                    }
                    mark(&mut hinted, *x, len);
                });
            }
            visit(&mut ins.op, &mut |x, role| match role {
                Role::Run(len) | Role::OutRun(len) => {
                    runs.push((i, *x, len, matches!(role, Role::OutRun(_))));
                    for c in *x..*x + if spread_runs { len } else { 1 } {
                        add(&mut at, c, (i, role));
                    }
                }
                _ => add(&mut at, *x, (i, role)),
            });
        }
        Self { at, hinted, runs }
    }

    fn of(&self, x: Off) -> &[(usize, Role)] {
        self.at.get(x as usize).map_or(&[], Vec::as_slice)
    }

    fn hinted(&self, x: Off) -> bool {
        self.hinted.get(x as usize).copied().unwrap_or(false)
    }

    /// How many instructions write `x`, a `DEREF`'s frame side counted when `deref`.
    fn writers(&self, x: Off, deref: bool) -> usize {
        (self.of(x).iter())
            .filter(|(_, role)| matches!(role, Role::Dest | Role::OutRun(_)) || (deref && *role == Role::DerefVal))
            .count()
    }
}

/// Every function but the ones whose frame layout an `addr()` fixes, then the jump tables' `KVal::At` targets
/// moved with the instructions dropped.
pub(crate) fn optimize(lowered: &mut [Lowered], tables: &mut JumpTables) {
    let mut at_targets: HashMap<String, Vec<u32>> = HashMap::new();
    for k in &tables.slots {
        if let KVal::At(n, i) = k {
            at_targets.entry(n.clone()).or_default().push(*i);
        }
    }
    let mut remaps: HashMap<String, Vec<u32>> = HashMap::new();
    for l in lowered.iter_mut().filter(|l| !l.fixed) {
        let targets = at_targets.get(&l.name).map_or(&[][..], Vec::as_slice);
        if let Some(remap) = optimize_fn(l, targets) {
            remaps.insert(l.name.clone(), remap);
        }
    }
    for k in &mut tables.slots {
        if let KVal::At(n, i) = k
            && let Some(remap) = remaps.get(n.as_str())
        {
            *i = remap[*i as usize];
        }
    }
}

/// Copies out, then the frame compacted; the old-to-new instruction index when instructions went.
fn optimize_fn(l: &mut Lowered, at_targets: &[u32]) -> Option<Vec<u32>> {
    let fs = l.frame_size;
    // A next-frame cell's offset past this frame's end, made absolute: renumbered with the end below.
    for ins in &mut l.code {
        if let LOp::MulNextFrame { a, b, c } = ins.op {
            ins.op = LOp::Copy {
                src: a,
                one: b,
                dst: fs + c,
            };
        }
    }
    let n = l.code.len();
    let mut dead = vec![false; n];
    // Only copies die and renames keep every target, so the blocks stay put.
    let blocks = block_starts(&l.code, &dead, at_targets);
    loop {
        let mut changed = false;
        let refs = Refs::new(&mut l.code, &dead, false);
        // Cells no rewrite may move or drop: in a hint or a run, or kept.
        let mut pinned = vec![false; fs as usize + 1];
        for (x, &h) in refs.hinted.iter().enumerate() {
            if h {
                mark(&mut pinned, x as Off, 1);
            }
        }
        // Cells an output run writes.
        let mut run_written = vec![false; fs as usize + 1];
        for &(_, x, len, out) in &refs.runs {
            mark(&mut pinned, x, len);
            if out {
                mark(&mut run_written, x, len);
            }
        }
        let is_pinned = |x: Off| x < l.keep || pinned.get(x as usize).copied().unwrap_or(false);
        // The cells this pass renamed: their references above are stale, so a copy naming one waits for the next.
        let mut touched: HashSet<Off> = HashSet::new();
        for i in 0..n {
            if dead[i] || !l.code[i].hints.is_empty() {
                continue;
            }
            let LOp::Copy { src: s, dst: d, .. } = l.code[i].op else {
                continue;
            };
            if touched.contains(&s) || touched.contains(&d) {
                continue;
            }
            // A cell written more than once (a join's) is in no rewrite.
            if s == d || refs.writers(d, false) != 1 {
                continue;
            }
            let d_refs = refs.of(d);
            // Propagate: d a temporary, read after the copy in its block only.
            if !is_pinned(d) && d < fs {
                let end = block_end(&blocks, block_of(&blocks, i), n);
                let ok = d_refs
                    .iter()
                    .all(|&(j, role)| j == i || (j > i && j < end && matches!(role, Role::Use | Role::DerefVal)));
                if ok {
                    let uses: Vec<usize> = d_refs.iter().map(|&(j, _)| j).filter(|&j| j != i).collect();
                    rename(&mut l.code, uses, d, s);
                    dead[i] = true;
                    touched.extend([s, d]);
                    changed = true;
                    continue;
                }
            }
            // Retarget: s a temporary out of every run and hint, of one writer (a `DEREF`'s frame side and a
            // back-solve counted: arms reuse cells, so a cell written twice is two values), and d written by the copy
            // alone, in this frame and before it: by no other instruction, run or hint, nor by the caller (a return
            // cell, a local, the next loop frame's, whose cells are reserved even past the last iteration). d is then
            // written wherever s is, which only adds writes no other path makes or reads.
            if d_refs.len() == 1
                && !refs.hinted(d)
                && !run_written.get(d as usize).copied().unwrap_or(false)
                && (l.rets.contains(&d) || d >= l.keep)
                && refs.writers(s, true) == 1
                && !is_pinned(s)
                && s < fs
            {
                let uses: Vec<usize> = refs.of(s).iter().map(|&(j, _)| j).filter(|&j| j != i).collect();
                rename(&mut l.code, uses, s, d);
                dead[i] = true;
                touched.extend([s, d]);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    while retarget_in_block(l, &mut dead, &blocks) {}
    // A copy left into the next loop frame stores through the next frame's pointer, the operand of the `JUMP` into
    // it: one `DEREF` row in place of one `MUL` row.
    for i in 0..n {
        let LOp::Copy { src: s, dst: c, .. } = l.code[i].op else {
            continue;
        };
        if dead[i] || c < fs {
            continue;
        }
        // Only the tail call's own copies between it and its `JUMP`.
        let jump = (i + 1..n).find(|&j| !dead[j] && !matches!(l.code[j].op, LOp::Copy { dst, .. } if dst >= fs));
        if let Some(j) = jump
            && let LOp::Jump { of, .. } = l.code[j].op
        {
            l.code[i].op = LOp::Deref {
                o1: of,
                o2: c - fs,
                o3: s,
                mode: DerefMode::Cell,
            };
        }
    }
    let remap = dead.iter().any(|&d| d).then(|| {
        // Old index to new; a dropped instruction maps to the next kept one.
        let mut remap = vec![0u32; n + 1];
        let mut k = 0u32;
        for i in 0..n {
            remap[i] = k;
            k += u32::from(!dead[i]);
        }
        remap[n] = k;
        let code = std::mem::take(&mut l.code);
        l.code = code
            .into_iter()
            .zip(&dead)
            .filter(|(_, d)| !**d)
            .map(|(mut ins, _)| {
                if let LOp::Set { k: KVal::Local(t), .. } = &mut ins.op {
                    *t = remap[*t as usize];
                }
                ins
            })
            .collect();
        remap
    });
    compact(l);
    remap
}

/// The instruction indices that start a block: the entry, every jump target, every instruction after a `JUMP`.
fn block_starts(code: &[LInstr], dead: &[bool], at_targets: &[u32]) -> Vec<usize> {
    let mut starts = vec![0usize];
    starts.extend(at_targets.iter().map(|&i| i as usize));
    for (i, ins) in code.iter().enumerate() {
        if dead[i] {
            continue;
        }
        match &ins.op {
            LOp::Set { k: KVal::Local(t), .. } => starts.push(*t as usize),
            LOp::Jump { .. } => starts.push(i + 1),
            _ => {}
        }
    }
    starts.sort_unstable();
    starts.dedup();
    starts
}

/// The frame renumbered past `keep` to the cells still referenced, in order; next-frame cells follow its end.
fn compact(l: &mut Lowered) {
    let fs = l.frame_size;
    let mut used = vec![false; fs as usize];
    for ins in &mut l.code {
        for h in &mut ins.hints {
            visit_hint(h, &mut |x, len| mark(&mut used, *x, len));
        }
        visit(&mut ins.op, &mut |x, role| match role {
            Role::Run(len) | Role::OutRun(len) => mark(&mut used, *x, len),
            _ => mark(&mut used, *x, 1),
        });
    }
    let mut map = vec![0u32; fs as usize];
    let mut next = 0u32;
    for c in 0..fs {
        if c < l.keep || used[c as usize] {
            map[c as usize] = next;
            next += 1;
        }
    }
    let rename = |x: &mut Off| {
        *x = if *x < fs { map[*x as usize] } else { next + (*x - fs) };
    };
    for ins in &mut l.code {
        for h in &mut ins.hints {
            visit_hint(h, &mut |x, _| rename(x));
        }
        visit(&mut ins.op, &mut |x, _| rename(x));
    }
    l.frame_size = next;
}

/// Per block, the blocks reachable from it (itself excluded), over a superset of the paths. A `JUMP` goes where its
/// own block sets its target (match arms reuse target cells, so a `SET` elsewhere may be another path's), and falls
/// through unless its condition is a cell only ever set to 1; any other `JUMP` (a call, a return, a dispatch) reaches
/// every later block. `None` for a function with a backward edge.
struct Cfg {
    /// Bit `c` of row `b`: block `c` is reachable from block `b`.
    reach: Vec<Vec<u64>>,
}

impl Cfg {
    fn new(code: &[LInstr], dead: &[bool], starts: &[usize], refs: &Refs) -> Option<Self> {
        let n = code.len();
        let nb = starts.len();
        // A cell only ever set to 1: every reference a `SET` of 1 or a read nothing can back-solve (a `JUMP`'s, a
        // copy's 1), as match arms reuse offsets and a `MUL` operand may be written by solving for it.
        let always_one = |x: Off| {
            !refs.hinted(x)
                && refs.of(x).iter().any(|&(_, r)| r == Role::Dest)
                && refs.of(x).iter().all(|&(i, _)| match &code[i].op {
                    LOp::Set { k: KVal::Const(c), .. } => *c == F128::ONE,
                    LOp::Jump { .. } => true,
                    LOp::Copy { src, one, dst } => *one == x && *src != x && *dst != x,
                    _ => false,
                })
        };
        let mut succ: Vec<Vec<usize>> = vec![Vec::new(); nb];
        // Every later block, a reach no successor's row can widen.
        let mut all_later = vec![false; nb];
        for b in 0..nb {
            let last = (starts[b]..block_end(starts, b, n)).rev().find(|&i| !dead[i]);
            let fall = (b + 1 < nb).then_some(b + 1);
            match last.map(|i| (i, &code[i].op)) {
                Some((j, LOp::Jump { oc, od, .. })) => {
                    let conditional = !always_one(*oc);
                    let local = (starts[b]..j).rev().find_map(|i| match &code[i].op {
                        LOp::Set { o, k: KVal::Local(t) } if !dead[i] && o == od => Some(*t as usize),
                        _ => None,
                    });
                    match local {
                        Some(t) if t > starts[b] => {
                            succ[b].push(block_of(starts, t.min(n.saturating_sub(1))));
                            if conditional {
                                succ[b].extend(fall);
                            }
                        }
                        Some(_) => return None,
                        None => all_later[b] = true,
                    }
                }
                _ => succ[b].extend(fall),
            }
        }
        // Forward edges only, so one pass from the last block back closes reachability.
        let words = nb.div_ceil(64);
        let mut reach = vec![vec![0u64; words]; nb];
        for b in (0..nb).rev() {
            if all_later[b] {
                let first = b + 1;
                for (w, word) in reach[b].iter_mut().enumerate().skip(first / 64) {
                    *word = if w == first / 64 { !0u64 << (first % 64) } else { !0 };
                }
                // Past the last block the row stays clear.
                if let Some(last) = reach[b].last_mut()
                    && !nb.is_multiple_of(64)
                {
                    *last &= (1u64 << (nb % 64)) - 1;
                }
                continue;
            }
            for &s in &succ[b] {
                if s <= b {
                    return None;
                }
                let (lo, hi) = reach.split_at_mut(s);
                lo[b][s / 64] |= 1 << (s % 64);
                for (x, &r) in lo[b].iter_mut().zip(&hi[0]) {
                    *x |= r;
                }
            }
        }
        Some(Self { reach })
    }

    fn reaches(&self, b: usize, c: usize) -> bool {
        self.reach[b][c / 64] >> (c % 64) & 1 == 1
    }
}

/// One copy whose source dies in its block renamed to the copy's target there: the target is then written where
/// the source was, and the copy goes. A source in a `KECCAK` output moves with its whole run, which needs a copy of
/// each of its cells to consecutive targets. Whether one was done.
fn retarget_in_block(l: &mut Lowered, dead: &mut [bool], starts: &[usize]) -> bool {
    let fs = l.frame_size;
    let n = l.code.len();
    let refs = Refs::new(&mut l.code, dead, true);
    let Some(cfg) = Cfg::new(&l.code, dead, starts, &refs) else {
        return false;
    };
    let runs = &refs.runs;
    // `runs` is in instruction order: the runs of the instructions in `lo..hi`.
    let runs_in = |lo: usize, hi: usize| {
        let from = runs.partition_point(|r| r.0 < lo);
        &runs[from..from + runs[from..].partition_point(|r| r.0 < hi)]
    };
    let copy_of = |i: usize| -> Option<(Off, Off)> {
        match l.code[i].op {
            LOp::Copy { src, dst, .. } if !dead[i] && l.code[i].hints.is_empty() && src != dst => Some((src, dst)),
            _ => None,
        }
    };
    let free = |x: Off| x >= l.keep && x < fs && !refs.hinted(x);
    // Rewrites planned on the code as it was, applied together at the end. A rewrite changes the references of its
    // cells in its block alone, which another block reads only for its source dying: per cell, the blocks it changed.
    let mut planned: Vec<(usize, usize, Off, u32, Off, Vec<usize>)> = Vec::new();
    let mut touched: HashMap<Off, Vec<usize>> = HashMap::new();
    for i in 0..n {
        let Some((s, d)) = copy_of(i) else { continue };
        if !free(s) || refs.hinted(d) {
            continue;
        }
        let blk = block_of(starts, i);
        let (bs, be) = (starts[blk], block_end(starts, blk, n));
        // The source run: the output run in this block holding s, or s alone.
        let (base, len, writer) = match runs_in(bs, i)
            .iter()
            .find(|&&(_, x, len, out)| out && (x..x + len).contains(&s))
        {
            Some(&(k, x, len, _)) => (x, len, Some(k)),
            None => (s, 1, None),
        };
        let target = d.wrapping_sub(s - base);
        if target.checked_add(len).is_none() {
            continue;
        }
        let stale = |c: Off, reads: bool| {
            (touched.get(&c)).is_some_and(|bs| bs.iter().any(|&b| b == blk || (reads && cfg.reaches(blk, b))))
        };
        if (base..base + len).any(|c| stale(c, true)) || (target..target + len).any(|c| stale(c, false)) {
            continue;
        }
        // Each cell of the run copied, in this block after its writer, to the consecutive targets.
        let mut copies = Vec::new();
        for j in 0..len {
            let (src, dst) = (base + j, target + j);
            let found = (bs..be).find(|&c| copy_of(c) == Some((src, dst)));
            match found {
                Some(c) if writer.is_none_or(|k| c > k) => copies.push(c),
                _ => break,
            }
        }
        if copies.len() != len as usize {
            continue;
        }
        let in_run = |x: Off| x >= base && x < base + len;
        let ok = (0..len).all(|j| {
            let (src, dst) = (base + j, target + j);
            if !free(src) || in_run(dst) || refs.hinted(dst) {
                return false;
            }
            let src_refs = refs.of(src);
            // Born in the block: its first reference there writes it, and nothing after the block reads it.
            let first = src_refs
                .iter()
                .filter(|&&(k, _)| k >= bs && k < be)
                .copied()
                .min_by_key(|&(k, _)| k);
            let born =
                matches!(first, Some((k, Role::Dest | Role::OutRun(_))) if Some(k) == writer || writer.is_none());
            // Outside the block, only on paths that miss it: neither before it, where it would be written already,
            // nor after it, where it would still be read.
            let dies = src_refs.iter().all(|&(k, _)| {
                let other = block_of(starts, k);
                (k >= bs && k < be) || (!cfg.reaches(blk, other) && !cfg.reaches(other, blk))
            });
            // The target named in the block by its copy alone.
            let alone = (refs.of(dst).iter()).all(|&(k, _)| k < bs || k >= be || copies.contains(&k));
            born && dies && alone
        });
        // Every run read in the block that meets the source run lies inside it.
        let runs_ok = (runs_in(bs, be).iter())
            .all(|&(_, x, rl, _)| x + rl <= base || x >= base + len || (x >= base && x + rl <= base + len));
        if !ok || !runs_ok {
            continue;
        }
        for c in (base..base + len).chain(target..target + len) {
            touched.entry(c).or_default().push(blk);
        }
        planned.push((bs, be, base, len, target, copies));
    }
    for (bs, be, base, len, target, copies) in &planned {
        for k in *bs..*be {
            if !dead[k] && !copies.contains(&k) {
                visit(&mut l.code[k].op, &mut |x, _| {
                    if *x >= *base && *x < base + len {
                        *x = target + (*x - base);
                    }
                });
            }
        }
        for &c in copies {
            dead[c] = true;
        }
    }
    !planned.is_empty()
}
