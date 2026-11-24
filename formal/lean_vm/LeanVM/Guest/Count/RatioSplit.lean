/-
  LeanVM.Guest.Count.RatioSplit

  A ratio subtree's closure check of one large function, in pieces of its body: each piece's
  callees by index, checked on its own, the pieces appended.
-/

module

public import LeanVM.Guest.Count.RatioBase

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

@[expose] public section

/-- Function `i`'s body. -/
noncomputable def krBody (i : ℕ) : List Stmt := ((coreProgram[i]?).getD default).body

/-- **The statements `[a, a + n)` of function `i`'s body call the functions of indices `L`**, all
in `J`. -/
noncomputable def krPiece (J : List ℕ) (i a n : ℕ) (L : List ℕ) : Bool :=
  (Stmt.blockCallees (((krBody i).drop a).take n) == L.map krName) &&
    L.all fun k => decide (k ∈ J) && Nat.blt k coreProgram.length

theorem blockCallees_append : ∀ (l l' : List Stmt),
    Stmt.blockCallees (l ++ l') = Stmt.blockCallees l ++ Stmt.blockCallees l'
  | [], _ => by simp [Stmt.blockCallees]
  | s :: l, l' => by
      rw [List.cons_append, Stmt.blockCallees, Stmt.blockCallees, blockCallees_append l l', List.append_assoc]

/-- Two adjacent pieces are one. -/
theorem krPiece_append {J : List ℕ} {i a n m : ℕ} {L L' : List ℕ} (h : krPiece J i a n L = true)
    (h' : krPiece J i (a + n) m L' = true) : krPiece J i a (n + m) (L ++ L') = true := by
  simp only [krPiece, Bool.and_eq_true, beq_iff_eq] at h h' ⊢
  refine ⟨?_, by rw [List.all_append, h.2, h'.2]; rfl⟩
  rw [List.take_add, blockCallees_append, List.drop_drop, h.1, h'.1, List.map_append]

/-- **A function's closure check from one piece of its whole body**, its calls `C i` the piece's. -/
theorem krClosedAt_of_piece {J : List ℕ} {C : ℕ → List ℕ} {i n : ℕ} {L : List ℕ}
    (h : krPiece J i 0 n L = true) (hc : (decide (C i = L) && Nat.ble (krBody i).length n) = true) :
    krClosedAt J C i = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq] at hc
  have hb : ((krBody i).drop 0).take n = krBody i := by rw [List.drop_zero, List.take_of_length_le hc.2]
  simp only [krPiece, hb] at h
  unfold krClosedAt
  rw [hc.1]
  exact h

end
end LeanVM.Guest.Count
