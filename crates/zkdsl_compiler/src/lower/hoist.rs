//! A run's reservations in the order of the proof's memory model
//! (`formal/lean_vm/LeanVM/Guest/Memory/Alloc.lean`): each call instance's frame, then its
//! `HeapBuf`s in the order it allocates them, then its callees' subtrees. The interpreter
//! reserves in execution order, so a `HeapBuf` some run allocates after a call would land past
//! that callee's subtree. Here its hint moves to just before the function's first call, which
//! changes no instruction: every `HeapBuf` pointer is a fresh cell only its hint writes. A buffer
//! whose size is not known there, that not every run reaches, or that would pass one some run
//! allocates before it (in the branch holding the call), is a compile error.
//!
//! Control flow inside a function only runs forward (a loop is a function of its own), so code
//! order is execution order, and two instructions in different arms of one branch never run together.

use super::*;
use std::collections::{HashMap, HashSet};
use std::ops::Range;

/// Where a frame or `HeapBuf` reservation was queued ([`FnLower::reserve`]). The arms of a
/// `match` share cells, so two reservations may share a pointer cell, but then also their site.
#[derive(Clone)]
pub(super) struct Site {
    /// Where the statement at depth `0` holding it starts.
    stmt_start: usize,
    /// The source line of its statement.
    line: u32,
    /// The name its statement binds.
    name: Option<String>,
}

impl FnLower<'_> {
    /// Queue a reservation.
    pub(super) fn reserve(&mut self, hint: Hint) {
        let site = Site {
            stmt_start: self.stmt_start,
            line: self.cur_line,
            name: self.let_name.clone(),
        };
        let (ptr, _) = reservation(&hint).expect("a frame or `HeapBuf` reservation");
        self.reservations.insert(ptr, site);
        self.pending.push(hint);
    }

    /// Move the `HeapBuf` reservations that some run reaches after a call to just before this
    /// function's first call, keeping their order. `Err` names one that cannot move, being in a
    /// branch, past a `return`, sized by a cell not written by then, or passing one that stays.
    pub(super) fn hoist_heap_bufs(&mut self) -> Result<(), String> {
        // Each reservation in code order: where it is, whether a callee's frame, its site.
        let sites: Vec<(usize, usize, bool, Site)> = (self.reservation_hints())
            .map(|(i, j, ptr, frame)| (i, j, frame, self.reservations[&ptr].clone()))
            .collect();
        let frames: Vec<(usize, usize)> = sites.iter().filter(|s| s.2).map(|s| (s.0, s.1)).collect();
        let late: Vec<&(usize, usize, bool, Site)> = (sites.iter())
            .filter(|&&(i, j, frame, _)| !frame && frames.iter().any(|&f| f < (i, j) && self.runs_on_to(f.0, i)))
            .collect();
        if late.is_empty() {
            return Ok(());
        }
        let (i, j, _, first) = sites
            .iter()
            .find(|s| s.2)
            .cloned()
            .expect("a call precedes a late `HeapBuf`");
        // The first call's reservation, or the start of the statement whose branch holds it.
        let at = if self.code_path[i].is_empty() {
            (i, j)
        } else {
            (first.stmt_start, 0)
        };
        assert!(
            self.code_path[at.0].is_empty(),
            "a statement at depth 0 starts at depth 0"
        );
        // A `HeapBuf` that stays between `at` and one that moves would follow it on a run reaching both.
        for &&(i, j, _, ref site) in &late {
            let stays = |&&(k, l, frame, _): &&(usize, usize, bool, Site)| {
                !frame && at <= (k, l) && (k, l) < (i, j) && !late.iter().any(|m| (m.0, m.1) == (k, l))
            };
            if let Some((_, _, _, stay)) = sites.iter().filter(stays).find(|s| self.runs_on_to(s.0, i)) {
                return Err(format!(
                    "line {}: `HeapBuf` `{}` in `{}` follows the function's first call (line {}), so it is \
                     allocated before the statement holding that call, which would put it ahead of `HeapBuf` `{}` \
                     (line {}): allocate `{}` before that statement, or move the code from it on into a function \
                     of its own",
                    site.line,
                    site.name.as_deref().unwrap_or("?"),
                    self.fn_name,
                    first.line,
                    stay.name.as_deref().unwrap_or("?"),
                    stay.line,
                    stay.name.as_deref().unwrap_or("?"),
                ));
            }
        }
        // The cells every run reaching `at` has written: the arguments, then what the code before it
        // surely writes.
        let mut written = self.written_in(0..at.0, 0);
        written.extend(2..2 + self.arg_cells);
        written.extend(self.code[at.0].hints[..at.1].iter().flat_map(hint_writes));
        let mut moved = Vec::new();
        for &&(i, j, _, ref site) in &late {
            let reached = self.code_path[i].is_empty() && !self.returns.iter().any(|&r| at.0 <= r && r < i);
            let Some(sized) = self.sized_by(i, j, &written).filter(|_| reached) else {
                return Err(format!(
                    "line {}: `HeapBuf` `{}` in `{}` follows the function's first call (line {}): it must be \
                     allocated on every path, its size computed before that call",
                    site.line,
                    site.name.as_deref().unwrap_or("?"),
                    self.fn_name,
                    first.line
                ));
            };
            moved.push((i, j, sized));
        }
        self.move_hints(moved, at);
        Ok(())
    }

    /// Move the `HeapBuf` reservations at depth 0 past the function's first branch to just before its jump,
    /// keeping their order, where their size is known there and they pass no `HeapBuf` that stays: then every
    /// jump before them is a forward jump in the frame, as the proof's bump pointer check asks. Best effort:
    /// one that cannot move stays.
    pub(super) fn hoist_past_first_branch(&mut self) {
        let Some(k) = self.code_path.iter().position(|p| !p.is_empty()) else {
            return;
        };
        let Some(b) = (0..k).rev().find(|&x| matches!(self.code[x].op, LOp::Jump { .. })) else {
            return;
        };
        let mut written = self.written_in(0..b, 0);
        written.extend(2..2 + self.arg_cells);
        let mut moved = Vec::new();
        for (i, j, ..) in self.reservation_hints().filter(|&(i, _, _, frame)| i > b && !frame) {
            if !self.code_path[i].is_empty() || self.returns.iter().any(|&r| b <= r && r < i) {
                break;
            }
            let Some(sized) = self.sized_by(i, j, &written) else {
                break;
            };
            moved.push((i, j, sized));
        }
        self.move_hints(moved, (b, 0));
    }

    /// Every frame or `HeapBuf` reservation in code order: its instruction, its place among the hints, its pointer
    /// cell, whether a callee's frame.
    fn reservation_hints(&self) -> impl Iterator<Item = (usize, usize, Off, bool)> {
        (self.code.iter().enumerate())
            .flat_map(|(i, ins)| ins.hints.iter().enumerate().map(move |(j, h)| (i, j, h)))
            .filter_map(|(i, j, h)| reservation(h).map(|(ptr, frame)| (i, j, ptr, frame)))
    }

    /// Hint `j` of instruction `i`, sized where the cells `written` are: a runtime size must be one of them, or
    /// a constant `g^k`, which takes its place.
    fn sized_by(&self, i: usize, j: usize, written: &HashSet<Off>) -> Option<Hint> {
        match self.code[i].hints[j] {
            Hint::AllocBufferDyn { ptr, size } if !written.contains(&size) => {
                (self.constant_exponent(size, i)).map(|k| Hint::AllocBuffer { ptr, size: k })
            }
            ref h => Some(h.clone()),
        }
    }

    /// Each hint `(i, j, h)` of `moved`, in code order and past `at`, replaced by `h` at `at`, in that order.
    fn move_hints(&mut self, moved: Vec<(usize, usize, Hint)>, at: (usize, usize)) {
        // Removed last first, so that the earlier positions stay valid.
        for &(i, j, _) in moved.iter().rev() {
            self.code[i].hints.remove(j);
        }
        let hints = moved.into_iter().map(|(_, _, h)| h);
        self.code[at.0].hints.splice(at.1..at.1, hints);
    }

    /// Whether some run executes instruction `a`, then goes on to instruction `b`, from `a` on: they
    /// are in no two arms of one branch, and no `return` that every run through `a` takes lies
    /// between them.
    fn runs_on_to(&self, a: usize, b: usize) -> bool {
        let (pa, pb) = (&self.code_path[a], &self.code_path[b]);
        let apart = pa.iter().zip(pb).find(|(x, y)| x != y).is_some_and(|(x, y)| x.0 == y.0);
        !apart && !(self.returns.iter()).any(|&r| a <= r && r < b && pa.starts_with(&self.code_path[r]))
    }

    /// The cells written on every run through `code[range]`, whose instructions all lie in the
    /// arms of the path of length `level` they share: what the instructions at that level write or
    /// read ([`touched`], [`hint_writes`]), and what every arm of a branch there does. A run that
    /// returns inside the range never leaves it, so the writes of an arm that returns count.
    fn written_in(&self, range: Range<usize>, level: usize) -> HashSet<Off> {
        let mut written = HashSet::new();
        // Each branch at this level, what each of its arms writes.
        let mut arms: HashMap<u32, Vec<Option<HashSet<Off>>>> = HashMap::new();
        let mut k = range.start;
        while k < range.end {
            let Some(&(branch, arm)) = self.code_path[k].get(level) else {
                let ins = &self.code[k];
                written.extend(ins.hints.iter().flat_map(hint_writes).chain(touched(&ins.op)));
                k += 1;
                continue;
            };
            let end = (k..range.end)
                .find(|&e| self.code_path[e].get(level) != Some(&(branch, arm)))
                .unwrap_or(range.end);
            let n = self.branches[branch as usize] as usize;
            arms.entry(branch).or_insert_with(|| vec![None; n])[arm as usize] =
                Some(self.written_in(k..end, level + 1));
            k = end;
        }
        for each in arms.into_values() {
            let every: Option<Vec<HashSet<Off>>> = each.into_iter().collect();
            if let Some((one, rest)) = every.as_deref().and_then(<[_]>::split_first) {
                written.extend(one.iter().filter(|o| rest.iter().all(|w| w.contains(o))));
            }
        }
        written
    }

    /// The `k` with `g^k` in `cell` by a `SET` at depth `0` before instruction `before`.
    fn constant_exponent(&self, cell: Off, before: usize) -> Option<u32> {
        let set = (self.code[..before].iter().zip(&self.code_path)).find_map(|(ins, p)| match &ins.op {
            LOp::Set { o, k: KVal::Const(v) } if *o == cell && p.is_empty() => Some(*v),
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
    let Hint::Resolved(h) = h else { return Vec::new() };
    let (base, len) = match *h {
        RHint::WitnessStack { base, len, .. } | RHint::FieldLimbs { base, len, .. } => (base, len),
        RHint::Log2Ceil { dst, .. } | RHint::Inverse { dst, .. } => (dst, 1),
        RHint::BitDecompose {
            bits: BitsDest::Stack(base),
            nbits,
            ..
        }
        | RHint::BitDecomposeExp {
            bits: BitsDest::Stack(base),
            nbits,
            ..
        } => (base, nbits),
        RHint::DigitDecomposeExp {
            dst: BitsDest::Stack(base),
            ndigits,
            ..
        } => (base, ndigits),
        RHint::WindowsExp {
            dest: BitsDest::Stack(base),
            at,
            count,
            ..
        } => (base + at, count),
        _ => return Vec::new(),
    };
    (base..base + len).collect()
}

/// The frame cells written once an instruction has run: those it writes on every run, and those it
/// reads, which both executors require written (an unwritten read fails in the Lean executor, and
/// in the Rust one is a read of zero that writes it). A `MUL` back-solves at most one operand, so its
/// three cells are written. A `DEREF` of mode `Cell` writes its frame cell only if its other side is
/// written, and a slot's destination is not counted for the same reason. A `JUMP` at depth `0` may be
/// a branch's exit, which not every run reaches, so its cells are not counted; they are written
/// before it anyway, by the instructions that computed them.
fn touched(op: &LOp) -> Vec<Off> {
    match *op {
        LOp::Set { o, .. } => vec![o],
        LOp::Xor { a, b, c }
        | LOp::Mul { a, b, c }
        | LOp::Solve { x: a, b, c }
        | LOp::Copy { src: a, one: b, dst: c } => vec![a, b, c],
        LOp::Deref { o1, .. } => vec![o1],
        LOp::Jump { .. } => Vec::new(),
        LOp::Slot { x, .. } => vec![x],
        LOp::Keccak { .. } => Vec::new(),
    }
}
