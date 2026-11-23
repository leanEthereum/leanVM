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
