//! A run's reservations in the order of the proof's memory model
//! (`formal/lean_vm/LeanVM/Guest/Memory/Alloc.lean`): each call instance's frame, then its
//! `HeapBuf`s in the order it allocates them, then its callees' subtrees. The interpreter
//! reserves in execution order, so a `HeapBuf` a function allocates after a call would land past
//! that callee's subtree. Here its hint moves to just before the function's first call, which
//! changes no instruction: every `HeapBuf` pointer is a fresh cell only its hint writes. A buffer
//! whose size is not known there, or that not every run reaches, is reserved there from advice
//! ([`RHint::AllocAdvice`] on [`HEAP_SIZE_STREAM`](crate::HEAP_SIZE_STREAM)), its own hint then
//! marked late ([`RHint::AllocLate`]), finding its pointer written.

use super::*;
use std::collections::HashSet;

/// Where a frame or `HeapBuf` reservation was queued ([`FnLower::reserve`]). The arms of a
/// `match` share cells, so two reservations may share a pointer cell, but then also their site.
#[derive(Clone, Copy)]
pub(super) struct Site {
    depth: u32,
    /// Where the statement at depth `0` holding it starts.
    stmt_start: usize,
    /// The source line of its statement.
    line: u32,
}

impl FnLower<'_> {
    /// Queue a reservation.
    pub(super) fn reserve(&mut self, hint: Hint) {
        let site = Site {
            depth: self.depth,
            stmt_start: self.stmt_start,
            line: self.cur_line,
        };
        let (ptr, _) = reservation(&hint).expect("a frame or `HeapBuf` reservation");
        self.reservations.insert(ptr, site);
        self.pending.push(hint);
    }

    /// Move the `HeapBuf` reservations that follow this function's first call to just before it,
    /// keeping their order. One that cannot move, being in a branch, past a `return`, or sized by a
    /// cell not written by then, is reserved there from advice instead, once per pointer cell.
    /// The source lines of those, in order.
    pub(super) fn hoist_heap_bufs(&mut self) -> Vec<u32> {
        // Each reservation in code order: where it is, whether a callee's frame, its site.
        let sites: Vec<(usize, usize, bool, Site)> = (self.code.iter().enumerate())
            .flat_map(|(i, ins)| ins.hints.iter().enumerate().map(move |(j, h)| (i, j, h)))
            .filter_map(|(i, j, h)| reservation(h).map(|(ptr, frame)| (i, j, frame, self.reservations[&ptr])))
            .collect();
        let Some(&(i, j, _, first)) = sites.iter().find(|s| s.2) else {
            return Vec::new();
        };
        // The first call's reservation, or the start of the statement whose branch holds it.
        let at = if first.depth == 0 {
            (i, j)
        } else {
            (first.stmt_start, 0)
        };
        assert_eq!(self.code_depth[at.0], 0, "a statement at depth 0 starts at depth 0");
        // The cells every run reaching `at` has written: the arguments, what the hints before it
        // at depth `0` write, and what the instructions there surely write or read.
        let mut written: HashSet<Off> = (2..2 + self.arg_cells).collect();
        for (ins, _) in self.code[..at.0].iter().zip(&self.code_depth).filter(|(_, d)| **d == 0) {
            written.extend(ins.hints.iter().flat_map(hint_writes));
            written.extend(touched(&ins.op));
        }
        written.extend(self.code[at.0].hints[..at.1].iter().flat_map(hint_writes));
        // The hints that go to `at`, in order: a moved one by where it was, or advice.
        let mut hoisted: Vec<Result<(usize, usize), Off>> = Vec::new();
        let mut advised = Vec::new();
        for &(i, j, _, site) in sites.iter().filter(|s| !s.2 && (s.0, s.1) >= at) {
            let (ptr, _) = reservation(&self.code[i].hints[j]).expect("a reservation");
            let reached = site.depth == 0 && !self.returns.iter().any(|&r| at.0 <= r && r < i);
            // A runtime size must be written before `at`, or be a constant `g^k`.
            let sized = match self.code[i].hints[j] {
                Hint::AllocBufferDyn { size, .. } if !written.contains(&size) => self
                    .constant_exponent(size, i)
                    .map(|k| Hint::AllocBuffer { ptr, size: k }),
                ref h => Some(h.clone()),
            };
            match sized {
                Some(h) if reached => {
                    self.code[i].hints[j] = h;
                    hoisted.push(Ok((i, j)));
                }
                _ => {
                    // Its own hint stays, marked late: it finds its pointer written.
                    self.code[i].hints[j] = late(&self.code[i].hints[j]);
                    if !hoisted.contains(&Err(ptr)) {
                        hoisted.push(Err(ptr));
                        advised.push(site.line);
                    }
                }
            }
        }
        let moved_ptrs: HashSet<Off> = (hoisted.iter().filter_map(|h| h.ok()))
            .filter_map(|(i, j)| reservation(&self.code[i].hints[j]).map(|(ptr, _)| ptr))
            .collect();
        assert!(
            hoisted
                .iter()
                .all(|h| h.err().is_none_or(|ptr| !moved_ptrs.contains(&ptr))),
            "a `HeapBuf` pointer both moved and reserved from advice"
        );
        // Removed last first, so that `pop` yields them in order.
        let moved = hoisted.iter().filter_map(|h| h.ok());
        let mut taken: Vec<Hint> = moved.rev().map(|(i, j)| self.code[i].hints.remove(j)).collect();
        let hints = hoisted.into_iter().map(|h| match h {
            Ok(_) => taken.pop().expect("a moved hint"),
            Err(ptr) => Hint::Resolved(RHint::AllocAdvice {
                ptr,
                stream: crate::HEAP_SIZE_STREAM.to_string(),
            }),
        });
        let hints: Vec<Hint> = hints.collect();
        self.code[at.0].hints.splice(at.1..at.1, hints);
        advised
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

/// A `HeapBuf` reservation's late form ([`RHint::AllocLate`]).
fn late(h: &Hint) -> Hint {
    let (ptr, size) = match *h {
        Hint::AllocBuffer { ptr, size } => (ptr, BufSize::Cells(size)),
        Hint::AllocBufferDyn { ptr, size } => (ptr, BufSize::Exp(size)),
        _ => unreachable!("a `HeapBuf` reservation"),
    };
    Hint::Resolved(RHint::AllocLate { ptr, size })
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

/// The frame cells written once an instruction has run: those it writes on every run, and those it
/// reads, which both executors require written (an unwritten read fails in the Lean executor, and
/// in the Rust one is a read of zero that writes it). A `MUL` back-solves at most one operand, so its
/// three cells are written; a `JUMP` reads its three cells, taken or not. A `DEREF` of mode `Cell`
/// writes its frame cell only if its other side is written, and a slot's destination is not counted
/// for the same reason.
fn touched(op: &LOp) -> Vec<Off> {
    match *op {
        LOp::Set { o, .. } => vec![o],
        LOp::Xor { a, b, c } | LOp::Mul { a, b, c } => vec![a, b, c],
        LOp::MulNextFrame { a, b, .. } => vec![a, b],
        LOp::Deref { o1, .. } => vec![o1],
        LOp::Jump { oc, od, of } => vec![oc, od, of],
        LOp::Slot { x, .. } => vec![x],
        LOp::Keccak { .. } => Vec::new(),
    }
}
