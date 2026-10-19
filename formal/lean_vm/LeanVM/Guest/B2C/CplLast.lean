/-
  LeanVM.Guest.B2C.CplLast

  A loop helper the completeness check accepts returns only at its end.
-/

module

public import LeanVM.Guest.B2C.CplRun
public import LeanVM.Guest.B2C.CplWalkZ

/-!
# A loop helper's last statement

The function's last part is a suffix of its body (`part_split`, its `nextPos` the body's end).
A loop helper's body ends with its closing `callIf` and `ret []`, so that suffix, of at least two
statements, ends as a loop helper does (`endsTail`), and the check of the last part then asks that
no statement of the body return but its last. With one window of one part, the part is the body.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

theorem tbl_endsTail (f : String) (c : V) (args : List V) :
    ∀ A : List Stmt, endsTail f (A ++ [.callIf c f args, .ret []]) = true
  | [] => by simp [endsTail]
  | [_] => by simp [endsTail]
  | a :: b :: A => by
    have ih := tbl_endsTail f c args (b :: A)
    rw [List.cons_append] at ih
    rw [List.cons_append, List.cons_append]
    rw [endsTail.eq_3 _ _ _ (by simp)]
    exact ih

/-- **A loop helper the check accepts returns only at its end.** -/
theorem lastBody {j : ℕ} (hok : CplOk j) (hl : (coreOf j).loop = true) : lastOkC (coreOf j).body = true := by
  set n := (certOf j).cuts.length with hn
  set k := nParts j n - 1 with hk
  have hN := one_le_nParts j n
  have hkN : k < nParts j n := by omega
  have hc : ∀ k' < nParts j n, cplWin j n k' = true := fun k' hk' ↦ hok n le_rfl k' hk'
  have hsplit := part_split hkN (fun h ↦ absurd h (lt_irrefl _)) hc
  have h1 : Nat.blt (k + 1) (nParts j n) = false := by
    refine Bool.eq_false_iff.mpr fun h ↦ ?_
    rw [Nat.blt_eq] at h
    omega
  have h2 : Nat.blt n (certOf j).cuts.length = false := by
    refine Bool.eq_false_iff.mpr fun h ↦ ?_
    rw [Nat.blt_eq] at h
    omega
  have hnext : nextPos j n k = (coreOf j).body.length := by
    unfold nextPos
    rw [h1, h2]
    rfl
  rw [hnext, List.drop_length, List.append_nil] at hsplit
  have hw := hc k hkN
  have hlast : lastPart j n k = true := by
    unfold lastPart
    rw [h1, ← hn, h2]
    rfl
  unfold cplWin at hw
  simp only [Bool.and_eq_true] at hw
  obtain ⟨⟨⟨-, -⟩, h3⟩, -⟩ := hw
  rw [hlast, Bool.cond_true] at h3
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h3
  obtain ⟨⟨hP, hlen⟩, hend⟩ := h3
  rcases hlen with ⟨hi0, hk0⟩ | hlen
  · -- one window of one part: the part is the body
    have hi : n = 0 := Nat.eq_of_beq_eq_true hi0
    have hk' : k = 0 := Nat.eq_of_beq_eq_true hk0
    have hp0 : partS j n k = 0 := by
      have hw0 := winOkC_of (hk' ▸ hc k hkN)
      unfold winOkC at hw0
      simp only [Bool.and_eq_true] at hw0
      rw [hk']
      exact Nat.eq_of_beq_eq_true hw0.1.1.2
    have hs0 : ((certOf j).cutAt n).start = 0 := by rw [hi]; rfl
    rw [hs0, hp0, Nat.zero_add, List.drop_zero] at hsplit
    rw [hsplit]
    exact hP
  · -- the part ends as a loop helper
    have hT : endsTail (coreOf j).name (partStmts j n k) = true := by
      obtain ⟨A, c, args, hb⟩ := loop_split hl
      have hl2 := Nat.le_of_ble_eq_true hlen
      rw [← hsplit] at hl2 ⊢
      rw [hb] at hl2 ⊢
      rw [List.length_drop, List.length_append] at hl2
      simp only [List.length_cons, List.length_nil] at hl2
      rw [List.drop_append_of_le_length (by omega)]
      exact tbl_endsTail _ c args _
    rw [hT, Bool.cond_true] at hend
    exact hend

end
end LeanVM.Guest.B2C
