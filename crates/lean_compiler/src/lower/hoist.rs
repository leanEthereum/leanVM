//! A run's reservations in the order of the proof's memory model
//! (`formal/lean_vm/LeanVM/Guest/Memory/Alloc.lean`): each call instance's frame, then its
//! `HeapBuf`s in the order it allocates them, then its callees' subtrees. The interpreter
//! reserves in execution order, so a `HeapBuf` a function allocates after a call would land past
//! that callee's subtree. Here its hint moves to just before the function's first call, which
//! changes no instruction: every `HeapBuf` pointer is a fresh cell only its hint writes.

use super::*;
use std::collections::HashSet;

/// Where a frame or `HeapBuf` reservation was queued ([`FnLower::reserve`]). The arms of a
/// `match` share cells, so two reservations may share a pointer cell, but then also their site.
#[derive(Clone, Copy)]
pub(super) struct Site {
    depth: u32,
    /// Where the statement at depth `0` holding it starts.
    stmt_start: usize,
}

impl FnLower<'_> {
    /// Queue a reservation.
    pub(super) fn reserve(&mut self, hint: Hint) {
        let site = Site {
            depth: self.depth,
            stmt_start: self.stmt_start,
        };
        let (ptr, _) = reservation(&hint).expect("a frame or `HeapBuf` reservation");
        self.reservations.insert(ptr, site);
        self.pending.push(hint);
    }

    /// [`Self::hoist`], then whether a `HeapBuf` reservation still follows a callee's frame.
    pub(super) fn hoist_heap_bufs(&mut self) -> bool {
        self.hoist();
        let mut frames = (self.code.iter().flat_map(|ins| &ins.hints)).filter_map(|h| Some(reservation(h)?.1));
        frames.any(|frame| frame) && frames.any(|frame| !frame)
    }

    /// Move the `HeapBuf` reservations that follow this function's first call to just before it,
    /// keeping their order, as far as that leaves the paths each runs on unchanged: until the
    /// first one in a branch, past a `return`, or whose size is not written before that point.
    fn hoist(&mut self) {
        // Each reservation in code order: where it is, whether a callee's frame, its site.
        let sites: Vec<(usize, usize, bool, Site)> = (self.code.iter().enumerate())
            .flat_map(|(i, ins)| ins.hints.iter().enumerate().map(move |(j, h)| (i, j, h)))
            .filter_map(|(i, j, h)| reservation(h).map(|(ptr, frame)| (i, j, frame, self.reservations[&ptr])))
            .collect();
        let Some(&(i, j, _, first)) = sites.iter().find(|s| s.2) else {
            return;
        };
        // The first call's reservation, or the start of the statement whose branch holds it.
        let at = if first.depth == 0 {
            (i, j)
        } else {
            (first.stmt_start, 0)
        };
        if self.code_depth.get(at.0) != Some(&0) {
            return;
        }
        // The cells every run reaching `at` has written: the arguments, and what the
        // instructions before it at depth `0` touch.
        let mut written: HashSet<Off> = (2..2 + self.arg_cells).collect();
        for (ins, _) in self.code[..at.0].iter().zip(&self.code_depth).filter(|(_, d)| **d == 0) {
            written.extend(ins.hints.iter().flat_map(hint_writes));
            written.extend(touched(&ins.op));
        }
        written.extend(self.code[at.0].hints[..at.1].iter().flat_map(hint_writes));
        let mut moved = Vec::new();
        for &(i, j, _, site) in sites.iter().filter(|s| !s.2 && (s.0, s.1) >= at) {
            if site.depth != 0 || self.returns.iter().any(|&r| at.0 <= r && r < i) {
                break;
            }
            // A runtime size must be written before `at`, or be a constant `g^k`.
            if let Hint::AllocBufferDyn { ptr, size } = self.code[i].hints[j]
                && !written.contains(&size)
            {
                let Some(k) = self.constant_exponent(size, i) else {
                    break;
                };
                self.code[i].hints[j] = Hint::AllocBuffer { ptr, size: k };
            }
            moved.push((i, j));
        }
        let hints: Vec<Hint> = moved.iter().rev().map(|&(i, j)| self.code[i].hints.remove(j)).collect();
        let into = &mut self.code[at.0].hints;
        for h in hints {
            into.insert(at.1, h);
        }
    }

    /// The `k` with `g^k` in `cell` by a `SET` at depth `0` before instruction `before`.
    fn constant_exponent(&self, cell: Off, before: usize) -> Option<u32> {
        let set = (self.code[..before].iter().zip(&self.code_depth)).find_map(|(ins, &d)| match &ins.op {
            LOp::Set { o, k: KVal::Const(v) } if *o == cell && d == 0 => Some(*v),
            _ => None,
        })?;
        u32::try_from(super::eval::small_gpow(set)?).ok()
    }
}

/// A reservation's pointer cell, and whether it is a callee's frame rather than a `HeapBuf`.
fn reservation(h: &Hint) -> Option<(Off, bool)> {
    match *h {
        Hint::AllocFrame { ptr, .. } | Hint::AllocLoopFrames { ptr, .. } | Hint::AllocArm { ptr, .. } => {
            Some((ptr, true))
        }
        Hint::AllocBuffer { ptr, .. } | Hint::AllocBufferDyn { ptr, .. } => Some((ptr, false)),
        _ => None,
    }
}

/// The frame cells a hint writes, of those a `HeapBuf` size may be.
fn hint_writes(h: &Hint) -> Vec<Off> {
    match *h {
        Hint::Resolved(RHint::WitnessStack { base, len, .. } | RHint::FieldLimbs { base, len, .. }) => {
            (base..base + len).collect()
        }
        Hint::Resolved(RHint::Log2Ceil { dst, .. } | RHint::Inverse { dst, .. }) => vec![dst],
        _ => Vec::new(),
    }
}

/// The frame cells an instruction reads or writes: each is written once it has run.
fn touched(op: &LOp) -> Vec<Off> {
    match *op {
        LOp::Set { o, .. } => vec![o],
        LOp::Xor { a, b, c } | LOp::Mul { a, b, c } => vec![a, b, c],
        LOp::MulNextFrame { a, b, .. } => vec![a, b],
        LOp::Deref { o1, o3, mode, .. } => match mode {
            DerefMode::Cell => vec![o1, o3],
            DerefMode::Fp | DerefMode::Pc => vec![o1],
        },
        LOp::Jump { oc, od, of } => vec![oc, od, of],
        LOp::Slot { x, dst, .. } => vec![x, dst],
        LOp::Keccak { .. } => Vec::new(),
    }
}
