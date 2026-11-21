//! Copies out of the lowered code, then each frame compacted to the cells still in use.
//!
//! The lowering copies a value into a fresh cell (`MUL d = s·1`) wherever a value has to be at a place: an
//! argument, a return cell, a `keccak` input, a loop frame's argument. Two rewrites remove such a copy:
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
//! written, on a `DEREF` row instead of a `MUL` one. A frame is then renumbered past its kept cells (`Lowered::keep`) to the cells still referenced, in order, so
//! a run stays consecutive; a cell of the next frame (a loop's argument) moves with the frame's end.

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

/// Every function but the ones whose frame layout an `addr()` fixes, then the jump tables' `KVal::At` targets
/// moved with the instructions dropped.
pub(crate) fn optimize(lowered: &mut [Lowered], tables: &mut JumpTables) {
    let at_targets = |name: &str, slots: &[KVal]| -> Vec<u32> {
        slots
            .iter()
            .filter_map(|k| match k {
                KVal::At(n, i) if n == name => Some(*i),
                _ => None,
            })
            .collect()
    };
    let mut remaps: HashMap<String, Vec<u32>> = HashMap::new();
    for l in lowered.iter_mut().filter(|l| !l.fixed) {
        let targets = at_targets(&l.name, &tables.slots);
        if let Some(remap) = optimize_fn(l, &targets) {
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
            ins.op = LOp::Mul { a, b, c: fs + c };
        }
    }
    let n = l.code.len();
    let mut dead = vec![false; n];
    loop {
        let mut changed = false;
        // Cells no rewrite may move or drop: in a hint or a run, or kept.
        let mut pinned = vec![false; fs as usize + 1];
        let pin = |pinned: &mut Vec<bool>, x: Off, len: u32| {
            for c in x..x + len.max(1) {
                if (c as usize) < pinned.len() {
                    pinned[c as usize] = true;
                }
            }
        };
        // Per cell: every (instruction, role) naming it.
        let mut refs: HashMap<Off, Vec<(usize, Role)>> = HashMap::new();
        let mut ones: Vec<bool> = vec![false; fs as usize + 1];
        for (i, ins) in l.code.iter_mut().enumerate() {
            if dead[i] {
                continue;
            }
            for h in &mut ins.hints {
                visit_hint(h, &mut |x, len| pin(&mut pinned, *x, len));
            }
            visit(&mut ins.op, &mut |x, role| {
                refs.entry(*x).or_default().push((i, role));
                if let Role::Run(len) | Role::OutRun(len) = role {
                    pin(&mut pinned, *x, len);
                }
            });
            if let LOp::Set { o, k: KVal::Const(c) } = &ins.op
                && *c == F128::ONE
                && (*o as usize) < ones.len()
            {
                ones[*o as usize] = true;
            }
        }
        // The cells written more than once (a join's), in no rewrite either.
        let one_writer = |x: Off| {
            refs.get(&x).is_some_and(|r| {
                r.iter()
                    .filter(|(_, role)| matches!(role, Role::Dest | Role::OutRun(_)))
                    .count()
                    == 1
            })
        };
        let is_pinned = |x: Off| x < l.keep || pinned.get(x as usize).copied().unwrap_or(false);
        let blocks = block_starts(&l.code, &dead, at_targets);
        // The cells this pass renamed: their references above are stale, so a copy naming one waits for the next.
        let mut touched: HashSet<Off> = HashSet::new();
        for i in 0..n {
            if dead[i] || !l.code[i].hints.is_empty() {
                continue;
            }
            let LOp::Mul { a, b, c: d } = l.code[i].op else {
                continue;
            };
            if [a, b, d].iter().any(|x| touched.contains(x)) {
                continue;
            }
            let one = |x: Off| ones.get(x as usize).copied().unwrap_or(false);
            let s = if one(b) {
                a
            } else if one(a) {
                b
            } else {
                continue;
            };
            if s == d || !one_writer(d) {
                continue;
            }
            let d_refs = &refs[&d];
            // Propagate: d a temporary, read after the copy in its block only.
            if !is_pinned(d) && d < fs {
                let block = blocks.partition_point(|&start| start <= i);
                let end = blocks.get(block).copied().unwrap_or(n);
                let ok = d_refs
                    .iter()
                    .all(|&(j, role)| j == i || (j > i && j < end && matches!(role, Role::Use | Role::DerefVal)));
                if ok {
                    let uses: Vec<usize> = d_refs.iter().map(|&(j, _)| j).filter(|&j| j != i).collect();
                    for j in uses {
                        visit(&mut l.code[j].op, &mut |x, _| {
                            if *x == d {
                                *x = s;
                            }
                        });
                    }
                    dead[i] = true;
                    touched.extend([s, d]);
                    changed = true;
                    continue;
                }
            }
            // Retarget: d named by the copy alone, s a temporary out of every run and hint.
            if d_refs.len() == 1
                && !is_pinned(s)
                && s < fs
                && !refs[&s]
                    .iter()
                    .any(|&(_, r)| matches!(r, Role::Run(_) | Role::OutRun(_)))
            {
                let uses: Vec<usize> = refs[&s].iter().map(|&(j, _)| j).filter(|&j| j != i).collect();
                for j in uses {
                    visit(&mut l.code[j].op, &mut |x, _| {
                        if *x == s {
                            *x = d;
                        }
                    });
                }
                dead[i] = true;
                touched.extend([s, d]);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    while retarget_in_block(l, &mut dead, at_targets) {}
    // A copy left into the next loop frame stores through the next frame's pointer, the operand of the `JUMP` into
    // it: one `DEREF` row in place of one `MUL` row.
    let one_cells: Vec<Off> = (l.code.iter())
        .filter_map(|ins| match &ins.op {
            LOp::Set { o, k: KVal::Const(c) } if *c == F128::ONE => Some(*o),
            _ => None,
        })
        .collect();
    for i in 0..n {
        let LOp::Mul { a, b, c } = l.code[i].op else { continue };
        if dead[i] || c < fs {
            continue;
        }
        let s = if one_cells.contains(&b) {
            a
        } else if one_cells.contains(&a) {
            b
        } else {
            continue;
        };
        // Only the tail call's own copies between it and its `JUMP`.
        let jump = (i + 1..n).find(|&j| !dead[j] && !matches!(l.code[j].op, LOp::Mul { c, .. } if c >= fs));
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
    let mut mark = |x: Off, len: u32| {
        for c in x..x + len.max(1) {
            if c < fs {
                used[c as usize] = true;
            }
        }
    };
    for ins in &mut l.code {
        for h in &mut ins.hints {
            visit_hint(h, &mut |x, len| mark(*x, len));
        }
        visit(&mut ins.op, &mut |x, role| match role {
            Role::Run(len) | Role::OutRun(len) => mark(*x, len),
            _ => mark(*x, 1),
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

/// The blocks, each its first instruction, and per block the blocks reachable from it (itself excluded). A `JUMP`
/// to a `SET` local target goes there; any other `JUMP` (a call, a return, a dispatch) is taken to reach every later
/// block, which over-approximates the paths.
struct Cfg {
    starts: Vec<usize>,
    /// Bit `c` of row `b`: block `c` is reachable from block `b`.
    reach: Vec<Vec<u64>>,
}

impl Cfg {
    fn new(code: &[LInstr], dead: &[bool], at_targets: &[u32]) -> Option<Self> {
        let starts = block_starts(code, dead, at_targets);
        let n = code.len();
        let block_of = |i: usize| starts.partition_point(|&s| s <= i) - 1;
        let mut locals: HashMap<Off, usize> = HashMap::new();
        let mut ones: Vec<Off> = Vec::new();
        for (i, ins) in code.iter().enumerate() {
            match &ins.op {
                LOp::Set { o, k: KVal::Local(t) } if !dead[i] => {
                    locals.insert(*o, *t as usize);
                }
                LOp::Set { o, k: KVal::Const(c) } if !dead[i] && *c == F128::ONE => ones.push(*o),
                _ => {}
            }
        }
        let nb = starts.len();
        let mut succ: Vec<Vec<usize>> = vec![Vec::new(); nb];
        // Every later block, a reach no successor's row can widen.
        let mut all_later = vec![false; nb];
        for b in 0..nb {
            let end = starts.get(b + 1).copied().unwrap_or(n);
            let last = (starts[b]..end).rev().find(|&i| !dead[i]);
            let fall = (b + 1 < nb).then_some(b + 1);
            match last.map(|i| &code[i].op) {
                Some(LOp::Jump { oc, od, .. }) => {
                    let conditional = !ones.contains(oc);
                    match locals.get(od) {
                        Some(&t) if t > starts[b] => {
                            succ[b].push(block_of(t.min(n.saturating_sub(1))));
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
                for c in b + 1..nb {
                    reach[b][c / 64] |= 1 << (c % 64);
                }
                continue;
            }
            for k in 0..succ[b].len() {
                let s = succ[b][k];
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
        Some(Self { starts, reach })
    }

    fn block_of(&self, i: usize) -> usize {
        self.starts.partition_point(|&s| s <= i) - 1
    }

    fn reaches(&self, b: usize, c: usize) -> bool {
        self.reach[b][c / 64] >> (c % 64) & 1 == 1
    }
}

/// One copy whose source dies in its block renamed to the copy's target there: the target is then written where
/// the source was, and the copy goes. A source in a `KECCAK` output moves with its whole run, which needs a copy of
/// each of its cells to consecutive targets. Whether one was done.
fn retarget_in_block(l: &mut Lowered, dead: &mut [bool], at_targets: &[u32]) -> bool {
    let fs = l.frame_size;
    let n = l.code.len();
    let Some(cfg) = Cfg::new(&l.code, dead, at_targets) else {
        return false;
    };
    let mut hinted = vec![false; fs as usize + 1];
    let mut refs: HashMap<Off, Vec<(usize, Role)>> = HashMap::new();
    let mut runs: Vec<(usize, Off, u32, bool)> = Vec::new();
    let mut ones: HashSet<Off> = HashSet::new();
    for (i, ins) in l.code.iter_mut().enumerate() {
        if dead[i] {
            continue;
        }
        for h in &mut ins.hints {
            visit_hint(h, &mut |x, len| {
                for c in *x..*x + len.max(1) {
                    if (c as usize) < hinted.len() {
                        hinted[c as usize] = true;
                    }
                }
            });
        }
        visit(&mut ins.op, &mut |x, role| {
            match role {
                Role::Run(len) => {
                    runs.push((i, *x, len, false));
                    for c in *x..*x + len {
                        refs.entry(c).or_default().push((i, role));
                    }
                }
                Role::OutRun(len) => {
                    runs.push((i, *x, len, true));
                    for c in *x..*x + len {
                        refs.entry(c).or_default().push((i, role));
                    }
                }
                _ => refs.entry(*x).or_default().push((i, role)),
            };
        });
        if let LOp::Set { o, k: KVal::Const(c) } = &ins.op
            && *c == F128::ONE
        {
            ones.insert(*o);
        }
    }
    let copy_of = |i: usize| -> Option<(Off, Off)> {
        let LOp::Mul { a, b, c } = l.code[i].op else {
            return None;
        };
        if dead[i] || !l.code[i].hints.is_empty() {
            return None;
        }
        if ones.contains(&b) && a != c {
            Some((a, c))
        } else if ones.contains(&a) && b != c {
            Some((b, c))
        } else {
            None
        }
    };
    let free = |x: Off| x >= l.keep && x < fs && !hinted[x as usize];
    // Rewrites planned on the code as it was, applied together at the end. A rewrite changes the references of its
    // cells in its block alone, which another block reads only for its source dying: per cell, the blocks it changed.
    let mut planned: Vec<(usize, usize, Off, u32, Off, Vec<usize>)> = Vec::new();
    let mut touched: HashMap<Off, Vec<usize>> = HashMap::new();
    for i in 0..n {
        let Some((s, d)) = copy_of(i) else { continue };
        if !free(s) || hinted.get(d as usize).copied().unwrap_or(false) {
            continue;
        }
        let blk = cfg.block_of(i);
        let (bs, be) = (cfg.starts[blk], cfg.starts.get(blk + 1).copied().unwrap_or(n));
        // The source run: the output run in this block holding s, or s alone.
        let (base, len, writer) = match runs
            .iter()
            .find(|&&(k, x, len, out)| out && k >= bs && k < i && (x..x + len).contains(&s))
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
            if !free(src) || in_run(dst) || hinted.get(dst as usize).copied().unwrap_or(false) {
                return false;
            }
            let src_refs = &refs[&src];
            // Born in the block: its first reference there writes it, and nothing after the block reads it.
            let first = src_refs
                .iter()
                .filter(|&&(k, _)| k >= bs && k < be)
                .map(|&(k, r)| (k, r))
                .min_by_key(|&(k, _)| k);
            let born =
                matches!(first, Some((k, Role::Dest | Role::OutRun(_))) if Some(k) == writer || writer.is_none());
            let dies = src_refs
                .iter()
                .all(|&(k, _)| (k >= bs && k < be) || !cfg.reaches(blk, cfg.block_of(k)));
            // The target named in the block by its copy alone.
            let alone = refs
                .get(&dst)
                .is_none_or(|r| r.iter().all(|&(k, _)| k < bs || k >= be || copies.contains(&k)));
            born && dies && alone
        });
        // Every run read in the block that meets the source run lies inside it.
        let runs_ok = runs.iter().all(|&(k, x, rl, _)| {
            k < bs || k >= be || x + rl <= base || x >= base + len || (x >= base && x + rl <= base + len)
        });
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
