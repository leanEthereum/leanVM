/-
  LeanVM.Guest.B1.Whir.OsSeg

  A buffer's contents from disjoint segments, and the reads of each segment.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC1

/-!
# Buffers from segments

`osSegC size segs`: a buffer of `size` words holding each segment `(off, cells)` at `off` (zero
elsewhere); on a memory holding it, every segment is read at `ptr·g^off` (`os_seg_reads`) when the
segments fit and are pairwise disjoint.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Word `i` of the segments: the first segment's holding it, else `0`. -/
def osSegAt : List (ℕ × List E) → ℕ → E
  | [], _ => 0
  | s :: segs, i => if s.1 ≤ i ∧ i < s.1 + s.2.length then s.2.getD (i - s.1) 0 else osSegAt segs i

/-- A buffer of `size` words from segments. -/
def osSegC (size : ℕ) (segs : List (ℕ × List E)) : List E := (List.range size).map (osSegAt segs)

/-- Pairwise disjoint segments. -/
def OsSegDisj (segs : List (ℕ × List E)) : Prop :=
  segs.Pairwise fun s t => s.1 + s.2.length ≤ t.1 ∨ t.1 + t.2.length ≤ s.1

theorem os_segAt_of : ∀ (segs : List (ℕ × List E)), OsSegDisj segs → ∀ s ∈ segs, ∀ k < s.2.length,
    osSegAt segs (s.1 + k) = s.2.getD k 0
  | [], _, _, h, _, _ => absurd h (by simp)
  | t :: segs, hd, s, hs, k, hk => by
    simp only [OsSegDisj, List.pairwise_cons] at hd
    rcases List.mem_cons.mp hs with rfl | hs'
    · simp only [osSegAt]
      rw [ite_pos' ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    · simp only [osSegAt]
      have := hd.1 s hs'
      rw [ite_neg' (by omega)]
      exact os_segAt_of segs hd.2 s hs' k hk

/-- **A segment is read at its offset.** -/
theorem os_seg_reads {rd : Reader} {ptr : E} {size : ℕ} {segs : List (ℕ × List E)}
    (hr : ReadsAt rd ptr (osSegC size segs)) (hd : OsSegDisj segs) {s : ℕ × List E} (hs : s ∈ segs)
    (hfit : s.1 + s.2.length ≤ size) : ∀ k < s.2.length, LoadHolds rd ptr (s.1 + k) (s.2.getD k 0) := by
  intro k hk
  have := hr (s.1 + k) (by simp [osSegC]; omega)
  simp only [osSegC, List.getElem_map, List.getElem_range] at this
  rwa [os_segAt_of segs hd s hs k hk] at this

theorem os_length_segC (size : ℕ) (segs : List (ℕ × List E)) : (osSegC size segs).length = size := by
  simp [osSegC]

end
end LeanVM.Guest.B1
