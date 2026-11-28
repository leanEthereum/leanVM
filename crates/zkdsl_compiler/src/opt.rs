//! Copies out of the lowered code, then each frame compacted to the cells still in use.
//!
//! The lowering copies a value into a fresh cell (`LOp::Copy`, a `MUL d = s·1` by a cell it set to 1 on every path
//! there) wherever a value has to be at a place: an argument, a return cell, a `keccak` input, a loop frame's
//! argument. Two rewrites remove such a copy:
//!
//! - **Propagate**: `d` is a temporary the copy alone writes, read only after it in the same block. Its readers
//!   read `s` instead. They run after the copy, and the copy reads `s`, so `s` is written there too.
//! - **Retarget**: `d` is written by the copy alone and named nowhere else in this frame but by the runs that read
//!   it (a return cell, a local, the next loop frame's argument), and `s` is a temporary of this frame, out of every
//!   run and hint. Renaming `s` to `d` throughout writes `d` where `s` was written, which the copy then only
//!   re-asserts.
//!
//! A copy still left into the next loop frame becomes a `DEREF` store through that frame's pointer: the same cell
//! written, on a `DEREF` row instead of a `MUL` one. A frame is then renumbered past its kept cells
//! (`Lowered::keep`) to the cells still referenced, in order, so a run stays consecutive; a cell of the next frame (a
//! loop's argument) moves with the frame's end.
//!
//! Last, every frame holding a `KECCAK` block is relaid so each block lies in one window ([`align_keccak_blocks`]).

use super::*;
use isa::KECCAK_WINDOW;
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
        LOp::Set { o, .. } => f(o, Role::Dest),
        LOp::Xor { a, b, c } | LOp::Mul { a, b, c } | LOp::Copy { src: a, one: b, dst: c } => {
            f(a, Role::Use);
            f(b, Role::Use);
            f(c, Role::Dest);
        }
        LOp::Solve { x, b, c } => {
            f(x, Role::Dest);
            f(b, Role::Use);
            f(c, Role::Use);
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
        Hint::AllocArm { ptr, sel: x, .. } => {
            f(ptr, 1);
            f(x, 1);
        }
        Hint::AllocBufferDyn { ptr, size } => {
            f(ptr, 1);
            f(size, 1);
        }
        Hint::Resolved(r) => match r {
            RHint::FrameAddress { .. } => unreachable!("resolved after the pass: it holds a frame size, not a cell"),
            RHint::AllocFrames { ptr, end, .. } => {
                f(ptr, 1);
                f(end, 1);
            }
            RHint::Alloc { ptr, .. } => f(ptr, 1),
            RHint::CellAddress { ptr, cell } => {
                f(ptr, 1);
                f(cell, 1);
            }
            RHint::AllocDyn { ptr, size } => {
                f(ptr, 1);
                f(size, 1);
            }
            RHint::AllocArm { ptr, sel: x, .. } => {
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

/// Instruction `i`'s source and target if it is a live copy, with no hint, of one cell to another.
fn copy_of(code: &[LInstr], dead: &[bool], i: usize) -> Option<(Off, Off)> {
    match code[i].op {
        LOp::Copy { src, dst, .. } if !dead[i] && code[i].hints.is_empty() && src != dst => Some((src, dst)),
        _ => None,
    }
}

/// The end of the block holding instruction `i`: the next block's first instruction, or `n`, `starts` the blocks'
/// first instructions.
fn block_end(starts: &[usize], i: usize, n: usize) -> usize {
    starts.get(starts.partition_point(|&s| s <= i)).copied().unwrap_or(n)
}

/// What the live instructions name.
struct Refs {
    /// Per cell, every (instruction, role) naming it, a run at each of its cells.
    at: Vec<Vec<(usize, Role)>>,
    /// The cells a hint names.
    hinted: Vec<bool>,
}

/// Cells `x..x + len`, at least `x`, marked in `cells`, grown to hold them.
fn mark_grow(cells: &mut Vec<bool>, x: Off, len: u32) {
    let end = (x + len.max(1)) as usize;
    if cells.len() < end {
        cells.resize(end, false);
    }
    cells[x as usize..end].fill(true);
}

impl Refs {
    fn new(code: &mut [LInstr], dead: &[bool]) -> Self {
        let mut at: Vec<Vec<(usize, Role)>> = Vec::new();
        let mut hinted = Vec::new();
        fn add(at: &mut Vec<Vec<(usize, Role)>>, x: Off, r: (usize, Role)) {
            if at.len() <= x as usize {
                at.resize(x as usize + 1, Vec::new());
            }
            at[x as usize].push(r);
        }
        for (i, ins) in code.iter_mut().enumerate().filter(|(i, _)| !dead[*i]) {
            for h in &mut ins.hints {
                visit_hint(h, &mut |x, len| mark_grow(&mut hinted, *x, len));
            }
            visit(&mut ins.op, &mut |x, role| match role {
                Role::Run(len) | Role::OutRun(len) => {
                    for c in *x..*x + len {
                        add(&mut at, c, (i, role));
                    }
                }
                _ => add(&mut at, *x, (i, role)),
            });
        }
        Self { at, hinted }
    }

    fn of(&self, x: Off) -> &[(usize, Role)] {
        self.at.get(x as usize).map_or(&[], Vec::as_slice)
    }

    fn hinted(&self, x: Off) -> bool {
        self.hinted.get(x as usize).copied().unwrap_or(false)
    }

    fn in_run(&self, x: Off) -> bool {
        (self.of(x).iter()).any(|(_, role)| matches!(role, Role::Run(_) | Role::OutRun(_)))
    }

    /// How many instructions write `x`, a `DEREF`'s frame side counted when `deref`.
    fn writers(&self, x: Off, deref: bool) -> usize {
        (self.of(x).iter())
            .filter(|(_, role)| matches!(role, Role::Dest | Role::OutRun(_)) || (deref && *role == Role::DerefVal))
            .count()
    }
}

/// Every function but the ones whose frame layout an `addr()` fixes, then every frame's `KECCAK` blocks put in
/// windows, then the jump tables' `KVal::At` targets moved with the instructions dropped and added.
pub(crate) fn optimize(lowered: &mut [Lowered], tables: &mut JumpTables) {
    let mut at_targets: HashMap<String, Vec<u32>> = HashMap::new();
    for k in &tables.slots {
        if let KVal::At(n, i) = k {
            at_targets.entry(n.clone()).or_default().push(*i);
        }
    }
    let mut remaps: HashMap<String, Vec<u32>> = HashMap::new();
    for l in lowered.iter_mut() {
        if !l.fixed {
            let targets = at_targets.get(&l.name).map_or(&[][..], Vec::as_slice);
            if let Some(remap) = optimize_fn(l, targets) {
                remaps.insert(l.name.clone(), remap);
            }
        }
        let (aligned, added) = align_keccak_blocks(l);
        l.aligned = aligned;
        if let Some(added) = added {
            let remap = compose(remaps.remove(&l.name), added);
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
    let mut dead = vec![false; l.code.len()];
    // Only copies die and renames keep every target, so the blocks stay put.
    let blocks = block_starts(&l.code, at_targets);
    while remove_copies(l, &mut dead, &blocks) {}
    store_next_frame_copies(l, &dead);
    let remap = drop_dead(l, &dead);
    compact(l);
    remap
}

/// One sweep of Propagate and Retarget over the frame; whether a copy went.
fn remove_copies(l: &mut Lowered, dead: &mut [bool], blocks: &[usize]) -> bool {
    let (fs, n) = (l.frame_size, l.code.len());
    let refs = Refs::new(&mut l.code, dead);
    // Cells no rewrite may move or drop: in a hint or a run, or kept.
    let is_pinned = |x: Off| x < l.keep || refs.hinted(x) || refs.in_run(x);
    // The cells this sweep renamed: their references above are stale, so a copy naming one waits for the next.
    let mut touched: HashSet<Off> = HashSet::new();
    for i in 0..n {
        let Some((s, d)) = copy_of(&l.code, dead, i) else {
            continue;
        };
        // A cell written more than once (a join's) is in no rewrite.
        if touched.contains(&s) || touched.contains(&d) || refs.writers(d, false) != 1 {
            continue;
        }
        let d_refs = refs.of(d);
        // Propagate: d a temporary, read after the copy in its block only.
        let end = block_end(blocks, i, n);
        let propagate = !is_pinned(d)
            && d < fs
            && (d_refs.iter())
                .all(|&(j, role)| j == i || (j > i && j < end && matches!(role, Role::Use | Role::DerefVal)));
        // Retarget: s a temporary out of every run and hint, of one writer (a `DEREF`'s frame side and a back-solve
        // counted: arms reuse cells, so a cell written twice is two values), and d written by the copy alone, in this
        // frame and before it: by no other instruction, run or hint, nor by the caller; a run may read it. d is then
        // written wherever s is, which only adds writes no other path makes and moves none a reader sees.
        let retarget = (d_refs.iter()).all(|&(j, role)| j == i || matches!(role, Role::Run(_)))
            && !refs.hinted(d)
            && !l.caller_writes(d)
            && refs.writers(s, true) == 1
            && !is_pinned(s)
            && s < fs;
        let (from, to) = match (propagate, retarget) {
            (true, _) => (d, s),
            (_, true) => (s, d),
            _ => continue,
        };
        rename(&mut l.code, refs.of(from).iter().map(|&(j, _)| j), from, to);
        dead[i] = true;
        touched.extend([s, d]);
    }
    !touched.is_empty()
}

/// A copy left into the next loop frame stores through the next frame's pointer, the operand of the `JUMP` into it:
/// one `DEREF` row in place of one `MUL` row.
fn store_next_frame_copies(l: &mut Lowered, dead: &[bool]) {
    let (fs, n) = (l.frame_size, l.code.len());
    for i in 0..n {
        let LOp::Copy { src, dst, .. } = l.code[i].op else {
            continue;
        };
        if dead[i] || dst < fs {
            continue;
        }
        // Only the tail call's own copies between it and its `JUMP`.
        let jump = (i + 1..n).find(|&j| !dead[j] && !matches!(l.code[j].op, LOp::Copy { dst, .. } if dst >= fs));
        if let Some(j) = jump
            && let LOp::Jump { of, .. } = l.code[j].op
        {
            l.code[i].op = LOp::Deref {
                o1: of,
                o2: dst - fs,
                o3: src,
                mode: DerefMode::Cell,
            };
        }
    }
}

/// The dead instructions dropped; the old-to-new index (a dropped instruction to the next kept one) when any went.
fn drop_dead(l: &mut Lowered, dead: &[bool]) -> Option<Vec<u32>> {
    if !dead.contains(&true) {
        return None;
    }
    let mut remap = Vec::with_capacity(dead.len() + 1);
    let mut k = 0u32;
    for &d in dead {
        remap.push(k);
        k += u32::from(!d);
    }
    remap.push(k);
    let code = std::mem::take(&mut l.code);
    l.code = (code.into_iter().zip(dead))
        .filter(|(_, d)| !**d)
        .map(|(mut ins, _)| {
            if let LOp::Set { k: KVal::Local(t), .. } = &mut ins.op {
                *t = remap[*t as usize];
            }
            ins
        })
        .collect();
    Some(remap)
}

/// The instruction indices that start a block: the entry, every jump target, every instruction after a `JUMP`.
fn block_starts(code: &[LInstr], at_targets: &[u32]) -> Vec<usize> {
    let mut starts = vec![0usize];
    starts.extend(at_targets.iter().map(|&i| i as usize));
    for (i, ins) in code.iter().enumerate() {
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
    let none_dead = vec![false; l.code.len()];
    let refs = Refs::new(&mut l.code, &none_dead);
    let mut map = vec![0u32; fs as usize];
    let mut next = 0u32;
    for c in 0..fs {
        if c < l.keep || !refs.of(c).is_empty() || refs.hinted(c) {
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

/// The old-to-new instruction index of `first`, if any, then `then`.
fn compose(first: Option<Vec<u32>>, then: Vec<u32>) -> Vec<u32> {
    match first {
        Some(r) => r.iter().map(|&i| then[i as usize]).collect(),
        None => then,
    }
}

/// A `KECCAK` operand that is a block of consecutive cells.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Operand {
    Tail,
    Cap,
    Out,
}

/// A `KECCAK` block of more than one cell: its instruction, operand, first cell and length.
#[derive(Clone, Copy)]
struct Block {
    at: usize,
    operand: Operand,
    x: Off,
    n: u32,
}

fn keccak_blocks(code: &[LInstr]) -> Vec<Block> {
    let mut blocks = Vec::new();
    for (at, ins) in code.iter().enumerate() {
        if let LOp::Keccak {
            tail,
            cap,
            c,
            out_cells,
            ..
        } = ins.op
        {
            let all = [
                (Operand::Tail, tail, 4),
                (Operand::Cap, cap, 4),
                (Operand::Out, c, out_cells.cells() as u32),
            ];
            blocks.extend((all.into_iter().filter(|&(.., n)| n > 1)).map(|(operand, x, n)| Block {
                at,
                operand,
                x,
                n,
            }));
        }
    }
    blocks
}

fn fits(x: Off, n: u32) -> bool {
    x % KECCAK_WINDOW + n <= KECCAK_WINDOW
}

/// Where a frame's cells may move: below `pinned` they keep their offsets (the kept cells and a cluster reaching into
/// them, or the whole frame where an `addr()` names its cells); above, each cluster (runs merged where they overlap)
/// moves whole.
struct Clusters {
    pinned: Off,
    clusters: Vec<(Off, Off)>,
}

impl Clusters {
    fn new(l: &mut Lowered) -> Self {
        let fs = l.frame_size;
        let mut runs: Vec<(Off, u32)> = Vec::new();
        for ins in &mut l.code {
            visit(&mut ins.op, &mut |x, role| {
                if let Role::Run(n) | Role::OutRun(n) = role {
                    runs.push((*x, n));
                }
            });
            for h in &mut ins.hints {
                visit_hint(h, &mut |x, n| runs.push((*x, n)));
            }
        }
        runs.retain(|&(x, n)| n > 1 && x < fs);
        runs.sort_unstable();
        let mut clusters: Vec<(Off, Off)> = Vec::new();
        for (x, n) in runs {
            match clusters.last_mut() {
                Some((_, end)) if x < *end => *end = (*end).max(x + n),
                _ => clusters.push((x, x + n)),
            }
        }
        let pinned = if l.fixed {
            fs
        } else {
            (clusters.iter())
                .filter(|&&(s, _)| s < l.keep)
                .map(|&(_, e)| e)
                .fold(l.keep, u32::max)
        };
        Self { pinned, clusters }
    }

    /// The movable clusters, each with the blocks in it.
    fn movable<'b>(&self, blocks: &'b [Block]) -> impl Iterator<Item = ((Off, Off), Vec<&'b Block>)> {
        (self.clusters.iter().filter(|&&(s, _)| s >= self.pinned))
            .map(|&(s, e)| ((s, e), blocks.iter().filter(|b| (s..e).contains(&b.x)).collect()))
    }

    /// The blocks no layout puts in windows: those pinned across one, and in a cluster that no offset suits, those
    /// crossing at the offset that suits the most cells.
    fn crossing(&self, blocks: &[Block]) -> Vec<Block> {
        let mut out: Vec<Block> = (blocks.iter())
            .filter(|b| b.x < self.pinned && !fits(b.x, b.n))
            .copied()
            .collect();
        for ((s, _), inner) in self.movable(blocks) {
            let fitting = |r: u32| inner.iter().filter(move |b| fits(r + b.x - s, b.n));
            let best = (0..KECCAK_WINDOW)
                .max_by_key(|&r| (fitting(r).map(|b| b.n).sum::<u32>(), std::cmp::Reverse(r)))
                .expect("a window");
            out.extend(inner.iter().filter(|b| !fits(best + b.x - s, b.n)).map(|b| **b));
        }
        out
    }
}

/// Each of `blocks` replaced by a fresh run past the frame, laid out in one window: an input copied there before its
/// `KECCAK`, an output copied from there after it, by a `MUL` by a cell set to 1 just before. The old-to-new
/// instruction index (an instruction to the first one inserted before it).
fn copy_out(l: &mut Lowered, blocks: &[Block]) -> Vec<u32> {
    let fs = l.frame_size;
    let mut sites: Vec<usize> = blocks.iter().map(|b| b.at).collect();
    sites.sort_unstable();
    sites.dedup();
    // Per site, in order, its cell of 1 and its blocks' runs, a run that would cross a window starting the next one.
    let mut fresh = fs;
    let mut alloc = |n: u32| {
        if !fits(fresh, n) {
            fresh = fresh.next_multiple_of(KECCAK_WINDOW);
        }
        fresh += n;
        fresh - n
    };
    let cells: Vec<(Off, Vec<Off>)> = (sites.iter())
        .map(|&at| {
            (
                alloc(1),
                blocks.iter().filter(|b| b.at == at).map(|b| alloc(b.n)).collect(),
            )
        })
        .collect();
    let extra = fresh - fs;
    // The next frame's cells move with the frame's end.
    let shift = |x: &mut Off| {
        if *x >= fs {
            *x += extra;
        }
    };
    for ins in &mut l.code {
        for h in &mut ins.hints {
            visit_hint(h, &mut |x, _| shift(x));
        }
        visit(&mut ins.op, &mut |x, _| shift(x));
    }
    l.frame_size += extra;
    let mut cells = cells.into_iter();
    let code = std::mem::take(&mut l.code);
    let mut remap = Vec::with_capacity(code.len() + 1);
    for (i, mut ins) in code.into_iter().enumerate() {
        remap.push(l.code.len() as u32);
        let here: Vec<&Block> = blocks.iter().filter(|b| b.at == i).collect();
        if here.is_empty() {
            l.code.push(ins);
            continue;
        }
        let line = ins.line;
        let emit = |code: &mut Vec<LInstr>, op: LOp, hints: Vec<Hint>| code.push(LInstr { op, line, hints });
        let (one, runs) = cells.next().expect("a site's cells");
        emit(
            &mut l.code,
            LOp::Set {
                o: one,
                k: KVal::Const(F128::ONE),
            },
            std::mem::take(&mut ins.hints),
        );
        let mut after = Vec::new();
        for (b, t) in here.into_iter().zip(runs) {
            let LOp::Keccak { tail, cap, c, .. } = &mut ins.op else {
                unreachable!("a block of a KECCAK")
            };
            *match b.operand {
                Operand::Tail => tail,
                Operand::Cap => cap,
                Operand::Out => c,
            } = t;
            for k in 0..b.n {
                if b.operand == Operand::Out {
                    after.push(LOp::Copy {
                        src: t + k,
                        one,
                        dst: b.x + k,
                    });
                } else {
                    emit(
                        &mut l.code,
                        LOp::Copy {
                            src: b.x + k,
                            one,
                            dst: t + k,
                        },
                        Vec::new(),
                    );
                }
            }
        }
        l.code.push(ins);
        for op in after {
            emit(&mut l.code, op, Vec::new());
        }
    }
    remap.push(l.code.len() as u32);
    for ins in &mut l.code {
        if let LOp::Set { k: KVal::Local(t), .. } = &mut ins.op {
            *t = remap[*t as usize];
        }
    }
    remap
}

/// The frame relaid so that, from a base that is a multiple of [`KECCAK_WINDOW`], every `KECCAK` block lies in one
/// window; whether the frame holds a block and so needs that base, and the old-to-new instruction index when
/// instructions were added. A block no layout puts in a window (pinned across one by the kept cells or an `addr()`,
/// or overlapping blocks no offset suits together) is copied to a fresh run first ([`copy_out`]). The cells below
/// `pinned` stay, each cluster moves whole to an offset that keeps its blocks in windows, and single cells fill the
/// gaps. A loop frame's size is a multiple of the window, so that each of a run of loop frames starts aligned.
fn align_keccak_blocks(l: &mut Lowered) -> (bool, Option<Vec<u32>>) {
    let w = KECCAK_WINDOW;
    let mut remap: Option<Vec<u32>> = None;
    // One copy suffices: it leaves the pinned cells only blocks in windows, each movable cluster only blocks in windows
    // at the offset `crossing` chose for it (removing runs only splits a cluster), and each fresh run in a window.
    let (blocks, layout) = loop {
        let blocks = keccak_blocks(&l.code);
        if blocks.is_empty() {
            return (false, remap);
        }
        assert!(
            blocks.iter().all(|b| b.x + b.n <= l.frame_size),
            "{}: a KECCAK block outside its frame",
            l.name
        );
        let layout = Clusters::new(l);
        let crossing = layout.crossing(&blocks);
        if crossing.is_empty() {
            break (blocks, layout);
        }
        assert!(
            remap.is_none(),
            "{}: a KECCAK block across a window after its copy",
            l.name
        );
        remap = Some(compose(remap, copy_out(l, &crossing)));
    };
    let fs = l.frame_size;
    let Clusters { pinned, clusters } = &layout;
    let pinned = *pinned;
    let in_cluster = |x: Off| {
        let i = clusters.partition_point(|&(s, _)| s <= x);
        i > 0 && x < clusters[i - 1].1
    };
    // Each movable cluster with the offsets, modulo the window, it may start at.
    let mut moving: Vec<(Off, u32, u32)> = (layout.movable(&blocks))
        .map(|((s, e), inner)| {
            let mask = (0..w)
                .filter(|&r| inner.iter().all(|b| fits(r + b.x - s, b.n)))
                .fold(0u32, |m, r| m | 1 << r);
            assert!(
                mask != 0,
                "{}: no offset suits the KECCAK blocks of cells {s}..{e}",
                l.name
            );
            (s, e - s, mask)
        })
        .collect();
    // The constrained first, fewest offsets then longest; then the rest, longest first. Each at the first offset
    // that suits it, then the single cells in the gaps, in order.
    moving.sort_by_key(|&(s, n, mask)| (mask.count_ones(), std::cmp::Reverse(n), s));
    let mut used: Vec<bool> = vec![true; pinned as usize];
    let free = |used: &Vec<bool>, p: u32, n: u32| (p..p + n).all(|q| !used.get(q as usize).copied().unwrap_or(false));
    let mut map: Vec<Off> = (0..fs).collect();
    for &(s, n, mask) in &moving {
        let p = (pinned..)
            .find(|&p| mask >> (p % w) & 1 == 1 && free(&used, p, n))
            .expect("a frame offset");
        if used.len() < (p + n) as usize {
            used.resize((p + n) as usize, false);
        }
        used[p as usize..(p + n) as usize].fill(true);
        for k in 0..n {
            map[(s + k) as usize] = p + k;
        }
    }
    let mut hole = pinned;
    for x in (pinned..fs).filter(|&x| !in_cluster(x)) {
        while used.get(hole as usize).copied().unwrap_or(false) {
            hole += 1;
        }
        map[x as usize] = hole;
        hole += 1;
    }
    let mut size = (map.iter().map(|&x| x + 1).max().unwrap_or(0)).max(pinned);
    if l.loop_frame {
        size = size.next_multiple_of(w);
    }
    let rename = |x: &mut Off| *x = if *x < fs { map[*x as usize] } else { size + (*x - fs) };
    for ins in &mut l.code {
        for h in &mut ins.hints {
            visit_hint(h, &mut |x, _| rename(x));
        }
        visit(&mut ins.op, &mut |x, _| rename(x));
    }
    l.frame_size = size;
    (true, remap)
}
