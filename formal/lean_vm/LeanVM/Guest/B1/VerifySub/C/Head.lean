/-
  LeanVM.Guest.B1.VerifySub.C.Head

  `verify_sub`'s head (G:3328-3336), honestly: the pool and the lengths allocated, the seed's
  permutation, the stream allocated and hinted, `table_rows` allocated.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Hon
public import LeanVM.Guest.B1.Opening.QueriesComplete2

/-!
# The head, honestly

`vsHeadT_complete`: on the honest valuation, with the statement's and the seed's cells canonical
(arguments `0 .. 3`), every statement of `vsHeadT` (positions `0 .. 10`) holds: the allocations,
the constants and the stream's hint by evaluation alone, the seed's `KECCAK` atom by its
canonical inputs.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **The head holds honestly.** -/
theorem vsHeadT_complete (hl : args.length = 6) (hc : ∀ i < 4, IsCanonical128 (args.getD i 0)) :
    ∀ s ∈ vsHeadT, VSH (coreProgram.Rel rd) rd (vsσ rd w args) s := by
  refine vs_block hl 0 vsHeadT (by decide +kernel)
    [keccakA [.n 2, .n 3, .n 0, .n 1, .n 8, .n 9, .n 10, .n 11, .n 8, .n 8, .n 9, .n 10, .n 11]
      (vsRun 12 13)] (by decide +kernel) ?_
  intro s hs
  rw [List.mem_singleton] at hs
  subst hs
  have hm : keccakA [.n 2, .n 3, .n 0, .n 1, .n 8, .n 9, .n 10, .n 11, .n 8, .n 8, .n 9,
      .n 10, .n 11] (vsRun 12 13) ∈ vsCPre :=
    vs_mem_slice (n := 6) (blk := [_]) (by decide +kernel) List.mem_cons_self
  have hg := vs_goodS (rd := rd) (w := w) hl hm
  -- the constants `0` at `8 .. 11`
  have hz : ∀ i ∈ [8, 9, 10, 11], vsσ rd w args (.n i) = 0 := by
    intro i hi
    have hmc : ∀ i ∈ [8, 9, 10, 11], vsConst i (word 0 0 0) ∈ vsCPre := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact vs_mem_slice (n := 2) (blk := [_]) (by decide +kernel) List.mem_cons_self
      · exact vs_mem_slice (n := 3) (blk := [_]) (by decide +kernel) List.mem_cons_self
      · exact vs_mem_slice (n := 4) (blk := [_]) (by decide +kernel) List.mem_cons_self
      · exact vs_mem_slice (n := 5) (blk := [_]) (by decide +kernel) List.mem_cons_self
    have h := vs_goodS (rd := rd) (w := w) hl (hmc i hi)
    simp only [vsConst, fixNe, GoodS, Good] at h
    rw [h, word_zero]
  have c0 : IsCanonical128 (0 : E) := canonical_zero
  simp only [keccakA, fixNe, GoodS] at hg
  show Atom.Holds rd (vsσ rd w args) (.keccak _ _ false false)
  refine holds_of_good (S := vsSL) (w := w) hg ?_
  have hp : ∀ i < 4, IsCanonical128 (vsσ rd w args (.n i)) := fun i hi ↦ by
    rw [vsC_param hl (by omega)]; exact hc i hi
  have hz' : ∀ i ∈ [8, 9, 10, 11], IsCanonical128 (vsσ rd w args (.n i)) := fun i hi ↦ by
    rw [hz i hi]; exact c0
  intro c
  simp only [List.map_cons, List.map_nil, cells13]
  fin_cases c <;> simp only [List.getD_cons_zero, List.getD_cons_succ]
  · exact hp 2 (by norm_num)
  · exact hp 3 (by norm_num)
  · exact hp 0 (by norm_num)
  · exact hp 1 (by norm_num)
  · exact hz' 8 (by simp)
  · exact hz' 9 (by simp)
  · exact hz' 10 (by simp)
  · exact hz' 11 (by simp)
  · exact hz' 8 (by simp)
  · exact hz' 8 (by simp)
  · exact hz' 9 (by simp)
  · exact hz' 10 (by simp)
  · exact hz' 11 (by simp)

end
end LeanVM.Guest.B1.VerifySub
