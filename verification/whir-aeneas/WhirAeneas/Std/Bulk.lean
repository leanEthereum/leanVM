module
public import Aeneas
import all Aeneas.Std.VecIter
@[expose] public section
open Aeneas Aeneas.Std Result Error

/- These operations relate logical content only. Aeneas Vec erases capacity and
   allocator state. Truncation is used only for Rust Copy elements. Extension's
   correspondence below is for the canonical owned-Vec IntoIterator dictionary,
   not arbitrary iterators with observable size_hint or unwinding effects. -/

@[expose, rust_fun "core::slice::{[@T]}::rotate_left"]
def core.slice.Slice.rotate_left {T : Type} (s : Aeneas.Std.Slice T)
    (mid : Usize) : Result (Aeneas.Std.Slice T) :=
  if mid.val ≤ s.val.length then
    .ok (.from (s.val.drop mid.val ++ s.val.take mid.val) (by
      have := s.property
      simp only [List.length_append, List.length_drop, List.length_take]
      omega))
  else .fail .panic

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::truncate"]
def alloc.vec.Vec.truncate {T : Type} (_A : Type) (v : Aeneas.Std.alloc.vec.Vec T)
    (len : Usize) : Result (Aeneas.Std.alloc.vec.Vec T) :=
  if len.val > v.val.length then .ok v
  else .ok (.from (v.val.take len.val) (by
    have := v.property
    simp only [List.length_take]
    omega))

@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::Extend<alloc::vec::Vec<@T>, @T>}::extend"]
def alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend
    {T : Type} (_A : Type) {I : Type} {IntoIter : Type}
    (inst : Aeneas.Std.core.iter.traits.collect.IntoIterator I T IntoIter)
    (v : Aeneas.Std.alloc.vec.Vec T) (input : I) :
    Result (Aeneas.Std.alloc.vec.Vec T) := do
  let iter ← inst.into_iter input
  let tail ← Aeneas.Std.alloc.vec.FromIteratorVec.iterToList inst.iteratorInst iter []
  (if h : v.val.length + tail.length ≤ Usize.max then
    .ok (.from (v.val ++ tail) (by simpa using h))
  else .fail .maximumSizeExceeded)

namespace WhirAeneas.StdBulk

theorem rotate_out_of_bounds {T : Type} (s : Slice T) (mid : Usize)
    (h : s.val.length < mid.val) :
    core.slice.Slice.rotate_left s mid = .fail .panic := by
  simp [core.slice.Slice.rotate_left, Nat.not_le.mpr h]

theorem rotate_zero {T : Type} (s : Slice T) :
    core.slice.Slice.rotate_left s 0#usize = .ok s := by
  simp [core.slice.Slice.rotate_left]

theorem rotate_at_length {T : Type} (s : Slice T) :
    core.slice.Slice.rotate_left s (Slice.len s) = .ok s := by
  simp [core.slice.Slice.rotate_left]

theorem rotate_content {T : Type} (s : Slice T) (mid : Usize)
    (h : mid.val ≤ s.val.length) :
    core.slice.Slice.rotate_left s mid =
      .ok (.from (s.val.drop mid.val ++ s.val.take mid.val) (by
        have := s.property
        simp only [List.length_append, List.length_drop, List.length_take]
        omega)) := by
  simp [core.slice.Slice.rotate_left, h]

theorem truncate_content {T : Type} (A : Type)
    (v : Aeneas.Std.alloc.vec.Vec T) (len : Usize) :
    alloc.vec.Vec.truncate A v len =
      .ok (.from (v.val.take len.val) (by
        have := v.property
        simp only [List.length_take]
        omega)) := by
  unfold alloc.vec.Vec.truncate
  split
  · congr 1
    apply Aeneas.Std.alloc.vec.Vec.ext
    simp [List.take_of_length_le (by omega : v.val.length ≤ len.val)]
  · rfl

theorem truncate_beyond_length {T : Type} (A : Type)
    (v : Aeneas.Std.alloc.vec.Vec T) (len : Usize)
    (h : v.val.length < len.val) :
    alloc.vec.Vec.truncate A v len = .ok v := by
  simp [alloc.vec.Vec.truncate, h]

theorem collect_owned {T : Type} (v : Aeneas.Std.alloc.vec.Vec T) (acc : List T) :
    Aeneas.Std.alloc.vec.FromIteratorVec.iterToList
      (Aeneas.Std.core.iter.traits.iterator.IteratorVecIntoIter T) v acc =
      .ok (acc.reverse ++ v.val) := by
  generalize hv : v.val = xs
  induction xs generalizing v acc with
  | nil =>
    rw [Aeneas.Std.alloc.vec.FromIteratorVec.iterToList.eq_1]
    simp only [Aeneas.Std.core.iter.traits.iterator.IteratorVecIntoIter,
      Aeneas.Std.alloc.vec.into_iter.IteratorIntoIter.next]
    split <;> simp_all
  | cons x xs ih =>
    rw [Aeneas.Std.alloc.vec.FromIteratorVec.iterToList.eq_1]
    simp only [Aeneas.Std.core.iter.traits.iterator.IteratorVecIntoIter,
      Aeneas.Std.alloc.vec.into_iter.IteratorIntoIter.next]
    split <;> simp_all [List.reverse_cons, List.append_assoc]

theorem extend_owned {T : Type} (A : Type)
    (v tail : Aeneas.Std.alloc.vec.Vec T)
    (h : v.val.length + tail.val.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend A
      (Aeneas.Std.core.iter.traits.collect.IntoIteratorVec T) v tail =
      .ok (.from (v.val ++ tail.val) (by simpa using h)) := by
  simp [alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend,
    Aeneas.Std.core.iter.traits.collect.IntoIteratorVec,
    Aeneas.Std.alloc.vec.IntoIteratorVec.into_iter, collect_owned, h]

end WhirAeneas.StdBulk
