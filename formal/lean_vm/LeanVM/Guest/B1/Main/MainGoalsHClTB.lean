/-
  LeanVM.Guest.B1.Main.MainGoalsHClTB

  The walk the honest prover takes for each child's claim lists: the gap walk when the list's slots
  strictly increase (`plan_mono`), else the walk by hinted indices.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHClT
public import LeanVM.Guest.B1.Main.ChildListGoalsTB
public import LeanVM.Guest.B1.Digest.ClaimListsAtM
public import LeanVM.Guest.AcceptableChild

/-!
# The children's claim lists' walks

`plan_mono`: a child's slots strictly increase when its list takes the gap walk (`hMonoX`,
`hMonoS`); `increasing_getD`, `mStart_le_of`: what the gap walk asks of them.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.Coverage (planSlots)
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.Coverage (coveragePlan CoverageRegion)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB Returns bufL)
open LeanVM.Guest.B1.Digest (ccBM mStart mStart_succ MRec)

@[expose] public section

variable {fs : String → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

theorem increasing_getD : ∀ {l : List ℕ}, Hints.increasing l = true → ∀ j, j + 1 < l.length →
    l.getD j 0 < l.getD (j + 1) 0
  | [], _, _, hj => by simp at hj
  | [_], _, _, hj => by simp at hj
  | _ :: _ :: _, h, 0, _ => by
    simp only [Hints.increasing, Bool.and_eq_true, decide_eq_true_eq] at h; simpa using h.1
  | _ :: b :: l, h, j + 1, hj => by
    simp only [Hints.increasing, Bool.and_eq_true] at h
    have := increasing_getD h.2 j (by simp at hj ⊢; omega)
    simpa using this

/-- **A child's slots strictly increase** when its list takes the gap walk: the walk stands at or
before each. -/
theorem plan_mono {α : Type} [BEq α] [LawfulBEq α] (D R : List α) (Cs : List (List α)) {c : ℕ}
    (hc : c < Cs.length)
    (hm : Hints.increasing ((coveragePlan D R Cs).childSlots.getD c []) = true) :
    ∀ j < (Cs[c]).length, mStart (fun j => ((coveragePlan D R Cs).childSlots.getD c []).getD j 0) j ≤
      ((coveragePlan D R Cs).childSlots.getD c []).getD j 0 := by
  intro j hj
  rcases j with _ | j
  · simp [mStart]
  · simp only [mStart_succ]
    obtain ⟨hc', hk', -⟩ := plan_child D R Cs hc hj
    have := increasing_getD hm j (by rw [List.getD_eq_getElem _ _ hc']; exact hk')
    omega

theorem mStart_le_of {o : ℕ → ℕ} {n L : ℕ} (h : ∀ j < n, o j < L) : mStart o n ≤ L := by
  rcases n with _ | n
  · simp [mStart]
  · rw [mStart_succ]; have := h n (by omega); omega

end
end LeanVM.Guest.B1.Main
