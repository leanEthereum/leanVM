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

/// Cells `x..x + len` marked, at least `x`, those past `cells` ignored.
fn mark(cells: &mut [bool], x: Off, len: u32) {
    for c in x..x + len.max(1) {
        if let Some(cell) = cells.get_mut(c as usize) {
            *cell = true;
        }
    }
}

/// The blocks and which dominate which, over a superset of the edges a run can take. A `JUMP` falls through to the
/// next block unless its condition holds 1, and goes: where its own block sets its target; nowhere in the function for
/// a call, which returns to the next block (its return address stored by a `Pc` `DEREF` just before), a tail call or
/// halt (its target a function entry or the sentinel), or a return (through cell 0); to a match table's slots, or a
/// join its block sets, for a dispatch (its target read by a `Slot`); nowhere when its condition holds 0; to the
/// labels its target cell's `SET`s write, when only they write it; and anywhere else to any label the function sets
/// or any match table slot. The control flow is fixed while copies are removed:
/// the pass kills and rewrites `MUL`s only.
struct Flow {
    starts: Vec<usize>,
    /// Each block's entry and exit times in a walk of the dominator tree (Cooper, Harvey and Kennedy's immediate
    /// dominators over reverse postorder); `None` for a block no path from the entry reaches.
    span: Vec<Option<(u32, u32)>>,
}

impl Flow {
    fn new(code: &[LInstr], dead: &[bool], at_targets: &[u32]) -> Self {
        let starts = block_starts(code, dead, at_targets);
        let (n, nb) = (code.len(), starts.len());
        let block = |t: usize| block_of(&starts, t.min(n.saturating_sub(1)));
        let ones = Holds::new(F128::ONE, code, dead, &starts, None);
        let zeros = Holds::new(F128::ZERO, code, dead, &starts, None);
        let tables: Vec<usize> = at_targets.iter().map(|&t| block(t as usize)).collect();
        let mut set_labels: HashMap<Off, Vec<usize>> = HashMap::new();
        let mut other_writers: HashSet<Off> = HashSet::new();
        for (ins, _) in code.iter().zip(dead).filter(|(_, d)| !**d) {
            for h in &ins.hints {
                visit_hint(&mut h.clone(), &mut |x, len| other_writers.extend(*x..*x + len.max(1)));
            }
            if let LOp::Set { o, k: KVal::Local(t) } = &ins.op {
                set_labels.entry(*o).or_default().push(block(*t as usize));
                continue;
            }
            visit(&mut ins.op.clone(), &mut |x, role| match role {
                Role::Dest | Role::DerefVal => {
                    other_writers.insert(*x);
                }
                Role::OutRun(len) => other_writers.extend(*x..*x + len),
                Role::Use | Role::Run(_) => {}
            });
        }
        let labels: Vec<usize> = (code.iter().zip(dead))
            .filter_map(|(ins, &dead)| match &ins.op {
                LOp::Set { k: KVal::Local(t), .. } if !dead => Some(block(*t as usize)),
                _ => None,
            })
            .chain(at_targets.iter().map(|&t| block(t as usize)))
            .collect();
        // Hubs past the blocks, one per set of targets a jump may take (any label, the tables, a cell's labels): a
        // jump goes to its hub and the hub to each target, which keeps the edges linear and the dominators the same.
        let (any, table) = (nb, nb + 1);
        let mut succs: Vec<Vec<usize>> = vec![Vec::new(); nb];
        succs.extend([labels, tables]);
        let mut cell_hub: HashMap<Off, usize> = HashMap::new();
        for b in 0..nb {
            let end = starts.get(b + 1).copied().unwrap_or(n);
            let mut live = (starts[b]..end).rev().filter(|&i| !dead[i]);
            let fall = (b + 1 < nb).then_some(b + 1);
            let mut succ: Vec<usize> = Vec::new();
            match live.next().map(|j| (j, &code[j].op)) {
                Some((j, LOp::Jump { oc, od, of })) => {
                    // The instruction of this block that writes the target cell, if any.
                    let writer = (starts[b]..j).rev().find(|&i| {
                        !dead[i] && matches!(&code[i].op, LOp::Set { o, .. } | LOp::Slot { dst: o, .. } if o == od)
                    });
                    let call = live.next().is_some_and(|i| {
                        matches!(
                            code[i].op,
                            LOp::Deref {
                                mode: DerefMode::Pc,
                                ..
                            }
                        )
                    });
                    if !ones.at(*oc, j) {
                        succ.extend(fall);
                    }
                    match writer.map(|i| &code[i].op) {
                        _ if zeros.at(*oc, j) => {}
                        Some(LOp::Set { k: KVal::Local(t), .. }) => succ.push(block(*t as usize)),
                        _ if call => succ.extend(fall),
                        Some(LOp::Set {
                            k: KVal::Entry(_) | KVal::EndSentinel,
                            ..
                        }) => {}
                        _ if *od == 0 && *of == 1 => {}
                        Some(LOp::Slot { .. }) => {
                            let joins = (starts[b]..j).filter_map(|i| match &code[i].op {
                                LOp::Set { k: KVal::Local(t), .. } if !dead[i] => Some(block(*t as usize)),
                                _ => None,
                            });
                            succ.push(table);
                            succ.extend(joins);
                        }
                        // Set elsewhere: one of the labels the cell's SETs write, when nothing else writes it (the
                        // bytecode never jumps through a cell no instruction wrote).
                        _ => match set_labels.get(od) {
                            Some(at) if !other_writers.contains(od) => {
                                succ.push(*cell_hub.entry(*od).or_insert_with(|| {
                                    succs.push(at.clone());
                                    succs.len() - 1
                                }));
                            }
                            _ => succ.push(any),
                        },
                    }
                }
                _ => succ.extend(fall),
            }
            succ.sort_unstable();
            succ.dedup();
            succs[b] = succ;
        }
        let blocks = nb;
        let nb = succs.len();
        // Reverse postorder from the entry.
        let mut order: Vec<usize> = Vec::with_capacity(nb);
        let mut seen = vec![false; nb];
        let mut stack: Vec<(usize, usize)> = vec![(0, 0)];
        seen[0] = true;
        while let Some(&mut (b, ref mut next)) = stack.last_mut() {
            if let Some(&s) = succs[b].get(*next) {
                *next += 1;
                if !seen[s] {
                    seen[s] = true;
                    stack.push((s, 0));
                }
            } else {
                order.push(b);
                stack.pop();
            }
        }
        order.reverse();
        let mut rank = vec![usize::MAX; nb];
        for (r, &b) in order.iter().enumerate() {
            rank[b] = r;
        }
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); nb];
        for (b, succ) in succs.iter().enumerate().filter(|&(b, _)| seen[b]) {
            for &s in succ {
                preds[s].push(b);
            }
        }
        let mut idom = vec![usize::MAX; nb];
        idom[0] = 0;
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &order[1..] {
                let mut new = usize::MAX;
                for &p in preds[b].iter().filter(|&&p| idom[p] != usize::MAX) {
                    new = if new == usize::MAX {
                        p
                    } else {
                        let (mut x, mut y) = (p, new);
                        while x != y {
                            while rank[x] > rank[y] {
                                x = idom[x];
                            }
                            while rank[y] > rank[x] {
                                y = idom[y];
                            }
                        }
                        x
                    };
                }
                if idom[b] != new {
                    idom[b] = new;
                    changed = true;
                }
            }
        }
        // Entry and exit times in the dominator tree: `d` dominates `b` when `b`'s span lies within `d`'s.
        let mut kids: Vec<Vec<usize>> = vec![Vec::new(); nb];
        for &b in &order[1..] {
            kids[idom[b]].push(b);
        }
        let mut span = vec![None; nb];
        let mut clock = 0u32;
        let mut walk: Vec<(usize, usize)> = vec![(0, 0)];
        let mut enter = vec![0u32; nb];
        while let Some(&mut (b, ref mut next)) = walk.last_mut() {
            if *next == 0 {
                enter[b] = clock;
                clock += 1;
            }
            if let Some(&k) = kids[b].get(*next) {
                *next += 1;
                walk.push((k, 0));
            } else {
                span[b] = Some((enter[b], clock));
                walk.pop();
            }
        }
        span.truncate(blocks);
        Self { starts, span }
    }

    /// Whether every path from the entry to block `b` passes block `d`.
    fn dominates(&self, d: usize, b: usize) -> bool {
        match (self.span[d], self.span[b]) {
            (Some((din, dout)), Some((bin, bout))) => din <= bin && bout <= dout,
            _ => false,
        }
    }
}

/// Where a cell holds a constant (1 makes a `MUL` by it a copy, 0 a `JUMP` on it never taken). On every path when
/// each of its writers is a live `SET` of it and no hint names it; else after a live `SET` of it earlier in the same
/// block or in a block that dominates, which write-once memory keeps. Match arms share their cells, and a join's cell
/// has a writer per path, so a `SET` on some other path says nothing.
struct Holds<'f> {
    value: F128,
    every: HashSet<Off>,
    starts: &'f [usize],
    flow: Option<&'f Flow>,
    /// Per cell, the blocks with a `SET` of 1 to it, each with its first such instruction.
    sets: HashMap<Off, Vec<(usize, usize)>>,
}

impl<'f> Holds<'f> {
    fn new(value: F128, code: &[LInstr], dead: &[bool], starts: &'f [usize], flow: Option<&'f Flow>) -> Self {
        let mut every: HashSet<Off> = HashSet::new();
        let mut other: HashSet<Off> = HashSet::new();
        let mut sets: HashMap<Off, Vec<(usize, usize)>> = HashMap::new();
        for (i, ins) in code.iter().enumerate().filter(|&(i, _)| !dead[i]) {
            for h in &ins.hints {
                visit_hint(&mut h.clone(), &mut |x, len| other.extend(*x..*x + len.max(1)));
            }
            if let LOp::Set { o, k: KVal::Const(c) } = &ins.op
                && *c == value
            {
                every.insert(*o);
                let b = block_of(starts, i);
                let at = sets.entry(*o).or_default();
                if at.last().is_none_or(|&(last, _)| last != b) {
                    at.push((b, i));
                }
                continue;
            }
            visit(&mut ins.op.clone(), &mut |x, role| match role {
                Role::Dest | Role::DerefVal => {
                    other.insert(*x);
                }
                Role::OutRun(len) => other.extend(*x..*x + len),
                Role::Use | Role::Run(_) => {}
            });
        }
        every.retain(|o| !other.contains(o));
        Self {
            value,
            every,
            starts,
            flow,
            sets,
        }
    }

    /// Whether cell `x` holds the value at instruction `i`.
    fn at(&self, x: Off, i: usize) -> bool {
        if self.every.contains(&x) {
            return true;
        }
        let b = block_of(self.starts, i);
        (self.sets.get(&x).into_iter().flatten())
            .any(|&(d, k)| (d == b && k < i) || (d != b && self.flow.is_some_and(|f| f.dominates(d, b))))
    }

    /// The source of a copy `MUL c = a·b` at instruction `i`, one of its operands holding 1 there.
    fn copy_source(&self, a: Off, b: Off, i: usize) -> Option<Off> {
        debug_assert!(self.value == F128::ONE);
        if self.at(b, i) {
            Some(a)
        } else if self.at(a, i) {
            Some(b)
        } else {
            None
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
            ins.op = LOp::Mul { a, b, c: fs + c };
        }
    }
    let n = l.code.len();
    let mut dead = vec![false; n];
    let flow = Flow::new(&l.code, &dead, at_targets);
    loop {
        let mut changed = false;
        // Cells no rewrite may move or drop: in a hint or a run, or kept.
        let mut pinned = vec![false; fs as usize + 1];
        // Per cell: every (instruction, role) naming it.
        let mut refs: HashMap<Off, Vec<(usize, Role)>> = HashMap::new();
        for (i, ins) in l.code.iter_mut().enumerate() {
            if dead[i] {
                continue;
            }
            for h in &mut ins.hints {
                visit_hint(h, &mut |x, len| mark(&mut pinned, *x, len));
            }
            visit(&mut ins.op, &mut |x, role| {
                refs.entry(*x).or_default().push((i, role));
                if let Role::Run(len) | Role::OutRun(len) = role {
                    mark(&mut pinned, *x, len);
                }
            });
        }
        let blocks = &flow.starts;
        let ones = Holds::new(F128::ONE, &l.code, &dead, blocks, Some(&flow));
        // The cells written more than once (a join's), in no rewrite either.
        let one_writer = |x: Off| {
            refs.get(&x).is_some_and(|r| {
                r.iter()
                    .filter(|(_, role)| matches!(role, Role::Dest | Role::OutRun(_)))
                    .count()
                    == 1
            })
        };
        // Every writer, a `DEREF`'s frame side counted: arms reuse cells, so a cell written twice is two values.
        let writers = |x: Off| {
            refs.get(&x).map_or(0, |r| {
                (r.iter())
                    .filter(|(_, role)| matches!(role, Role::Dest | Role::OutRun(_) | Role::DerefVal))
                    .count()
            })
        };
        let is_pinned = |x: Off| x < l.keep || pinned.get(x as usize).copied().unwrap_or(false);
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
            let Some(s) = ones.copy_source(a, b, i) else {
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
                    rename(&mut l.code, uses, d, s);
                    dead[i] = true;
                    touched.extend([s, d]);
                    changed = true;
                    continue;
                }
            }
            // Retarget: d named by the copy alone, s a temporary of one writer out of every run and hint.
            if d_refs.len() == 1
                && writers(s) == 1
                && !is_pinned(s)
                && s < fs
                && !refs[&s]
                    .iter()
                    .any(|&(_, r)| matches!(r, Role::Run(_) | Role::OutRun(_)))
            {
                let uses: Vec<usize> = refs[&s].iter().map(|&(j, _)| j).filter(|&j| j != i).collect();
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
    while retarget_in_block(l, &mut dead, at_targets, &flow) {}
    // A copy left into the next loop frame stores through the next frame's pointer, the operand of the `JUMP` into
    // it: one `DEREF` row in place of one `MUL` row.
    let ones = Holds::new(F128::ONE, &l.code, &dead, &flow.starts, Some(&flow));
    for i in 0..n {
        let LOp::Mul { a, b, c } = l.code[i].op else { continue };
        if dead[i] || c < fs {
            continue;
        }
        let Some(s) = ones.copy_source(a, b, i) else {
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
        let ones = Holds::new(F128::ONE, code, dead, &starts, None);
        let nb = starts.len();
        let mut succ: Vec<Vec<usize>> = vec![Vec::new(); nb];
        // Every later block, a reach no successor's row can widen.
        let mut all_later = vec![false; nb];
        for b in 0..nb {
            let end = starts.get(b + 1).copied().unwrap_or(n);
            let last = (starts[b]..end).rev().find(|&i| !dead[i]);
            let fall = (b + 1 < nb).then_some(b + 1);
            match last.map(|i| (i, &code[i].op)) {
                Some((j, LOp::Jump { oc, od, .. })) => {
                    let conditional = !ones.at(*oc, j);
                    // The target its own block sets: match arms reuse the target cells, so a SET elsewhere may be
                    // another path's. Without one the target is unknown, reaching every later block.
                    let local = (starts[b]..j).rev().find_map(|i| match &code[i].op {
                        LOp::Set { o, k: KVal::Local(t) } if !dead[i] && o == od => Some(*t as usize),
                        _ => None,
                    });
                    match local.as_ref() {
                        Some(&t) if t > starts[b] => {
                            succ[b].push(block_of(&starts, t.min(n.saturating_sub(1))));
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
        block_of(&self.starts, i)
    }

    fn reaches(&self, b: usize, c: usize) -> bool {
        self.reach[b][c / 64] >> (c % 64) & 1 == 1
    }
}

/// One copy whose source dies in its block renamed to the copy's target there: the target is then written where
/// the source was, and the copy goes. A source in a `KECCAK` output moves with its whole run, which needs a copy of
/// each of its cells to consecutive targets. Whether one was done.
fn retarget_in_block(l: &mut Lowered, dead: &mut [bool], at_targets: &[u32], flow: &Flow) -> bool {
    let fs = l.frame_size;
    let n = l.code.len();
    let Some(cfg) = Cfg::new(&l.code, dead, at_targets) else {
        return false;
    };
    let mut hinted = vec![false; fs as usize + 1];
    let mut refs: HashMap<Off, Vec<(usize, Role)>> = HashMap::new();
    let mut runs: Vec<(usize, Off, u32, bool)> = Vec::new();
    for (i, ins) in l.code.iter_mut().enumerate() {
        if dead[i] {
            continue;
        }
        for h in &mut ins.hints {
            visit_hint(h, &mut |x, len| mark(&mut hinted, *x, len));
        }
        visit(&mut ins.op, &mut |x, role| match role {
            Role::Run(len) | Role::OutRun(len) => {
                runs.push((i, *x, len, matches!(role, Role::OutRun(_))));
                for c in *x..*x + len {
                    refs.entry(c).or_default().push((i, role));
                }
            }
            _ => refs.entry(*x).or_default().push((i, role)),
        });
    }
    let ones = Holds::new(F128::ONE, &l.code, dead, &flow.starts, Some(flow));
    // `runs` is in instruction order: the runs of the instructions in `lo..hi`.
    let runs_in = |lo: usize, hi: usize| {
        let from = runs.partition_point(|r| r.0 < lo);
        &runs[from..from + runs[from..].partition_point(|r| r.0 < hi)]
    };
    let copy_of = |i: usize| -> Option<(Off, Off)> {
        let LOp::Mul { a, b, c } = l.code[i].op else {
            return None;
        };
        if dead[i] || !l.code[i].hints.is_empty() {
            return None;
        }
        if ones.at(b, i) && a != c {
            Some((a, c))
        } else if ones.at(a, i) && b != c {
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
            if !free(src) || in_run(dst) || hinted.get(dst as usize).copied().unwrap_or(false) {
                return false;
            }
            let src_refs = &refs[&src];
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
                let other = cfg.block_of(k);
                (k >= bs && k < be) || (!cfg.reaches(blk, other) && !cfg.reaches(other, blk))
            });
            // The target named in the block by its copy alone.
            let alone = refs
                .get(&dst)
                .is_none_or(|r| r.iter().all(|&(k, _)| k < bs || k >= be || copies.contains(&k)));
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
