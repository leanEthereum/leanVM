/-
  LeanVM.Guest.B2C.ShareLHome

  What the local sharing check says of a home: its cell, its owner, its place in its cell's
  list, its justification; and of an anchor.
-/

module

public import LeanVM.Guest.B2C.ShareLSpec

/-!
# Homes and anchors, unpacked

`homeOk_spec`, `sharedOk_spec`, `justOk_spec` and `anchorOk_spec` state the Boolean checks of
a home and an anchor as propositions, for the soundness proof (`ShareLSound.lean`).
-/

namespace LeanVM.Guest.B2C.ShareL

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Local LeanVM.Guest.Check LeanVM.Guest.Exec
open LeanVM.Guest.Packed (fld fld_lt)

@[expose] public section

section Home

variable (K : FnK)

theorem band {a b : Bool} : (a && b) = true ↔ a = true ∧ b = true := by simp

theorem blt_false {a b : ℕ} (h : b ≤ a) : Nat.blt a b = false := by
  cases h' : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp h') (by omega)

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases h' : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h') h

/-- **A home**, unfolded. -/
theorem homeOk_spec {st : Stmt} {q i : ℕ} {cx : Ctx} {v x : ℕ} (h : homeOk K st q i cx v x = true) :
    (fld x 0 16 < K.fs ∨ fld x 0 16 ∈ K.nx) ∧ bitN K.fc (fld x 0 16) = false ∧ fld x 0 16 < K.mb ∧
    (fld x 0 16 < 2 → vSh x = 0) ∧
    (2 ≤ fld x 0 16 → vSh x = 0 → tget wO 8 5 K.T.ot (fld x 0 16) = 4 * v + 1) ∧
    (2 ≤ fld x 0 16 → vSh x ≠ 0 → vHp x = q ∧ vHj x = i ∧ vSe x = cx.e ∧
      sharedOk K st q i cx v (fld x 0 16) (vSh x) (tget wO 8 5 K.T.ot (fld x 0 16)) = true) := by
  unfold homeOk at h
  dsimp only at h
  simp only [band, Bool.or_eq_true, Nat.blt_eq, Bool.not_eq_true', anyR_eq, List.any_eq_true, nbeq_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1.imp id fun ⟨c, hc, he⟩ ↦ he ▸ hc, h2, h3, fun hc ↦ ?_, fun hc hs ↦ ?_, fun hc hs ↦ ?_⟩
  · rw [show Nat.blt (fld x 0 16) 2 = true from Nat.blt_eq.mpr hc] at h4
    simpa using h4
  · rw [blt_false hc] at h4
    simp only [Bool.cond_false, show Nat.beq (vSh x) 0 = true from nbeq_iff.mpr hs, Bool.cond_true,
      nbeq_iff] at h4
    exact h4
  · rw [blt_false hc] at h4
    have : Nat.beq (vSh x) 0 = false := beq_false hs
    simp only [Bool.cond_false, this, band, nbeq_iff] at h4
    exact ⟨h4.1.1.1, h4.1.1.2, h4.1.2, h4.2⟩

/-- **A shared home's place in its cell's list**, unfolded. -/
theorem sharedOk_spec {st : Stmt} {q i : ℕ} {cx : Ctx} {v c si o : ℕ} (h : sharedOk K st q i cx v c si o = true) :
    sCell (tget wS 6 5 K.T.sl (si - 1)) = c ∧ sHp (tget wS 6 5 K.T.sl (si - 1)) = q ∧
    sHj (tget wS 6 5 K.T.sl (si - 1)) = i ∧ 2 ≤ o % 4 ∧
    (sPrev (tget wS 6 5 K.T.sl (si - 1)) = 0 → o >>> 2 = v + 1 ∧ sHead (tget wS 6 5 K.T.sl (si - 1)) = q) ∧
    (sPrev (tget wS 6 5 K.T.sl (si - 1)) ≠ 0 →
      sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1 < K.T.nv ∧
      vSh (vlane K (sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1)) ≠ 0 ∧
      sCell (tget wS 6 5 K.T.sl (vSh (vlane K (sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1)) - 1)) = c ∧
      sNext (tget wS 6 5 K.T.sl (vSh (vlane K (sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1)) - 1)) = v + 1 ∧
      sHead (tget wS 6 5 K.T.sl (vSh (vlane K (sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1)) - 1)) =
        sHead (tget wS 6 5 K.T.sl (si - 1)) ∧
      (sHp (tget wS 6 5 K.T.sl (vSh (vlane K (sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1)) - 1)) < q ∨
        sHp (tget wS 6 5 K.T.sl (vSh (vlane K (sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1)) - 1)) = q ∧
        sHj (tget wS 6 5 K.T.sl (vSh (vlane K (sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1)) - 1)) < i) ∧
      (sKind (tget wS 6 5 K.T.sl (si - 1)) = kRoot → cx.t + 1 ≤ sHead (tget wS 6 5 K.T.sl (si - 1)) ∧
        sHp (tget wS 6 5 K.T.sl (vSh (vlane K (sPrev (tget wS 6 5 K.T.sl (si - 1)) - 1)) - 1)) < cx.a)) ∧
    justOk K st q i c (tget wS 6 5 K.T.sl (si - 1)) o = true := by
  unfold sharedOk at h
  simp only [band, nbeq_iff, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h5, fun hp ↦ ?_, fun hp ↦ ?_, h7⟩
  · rw [show Nat.beq (sPrev (tget wS 6 5 K.T.sl (si - 1))) 0 = true from nbeq_iff.mpr hp] at h6
    simpa [band] using h6
  · rw [beq_false hp] at h6
    simp only [Bool.cond_false, band, Nat.blt_eq, Bool.not_eq_true', nbeq_iff, Bool.or_eq_true] at h6
    obtain ⟨⟨⟨⟨⟨⟨h61, h62⟩, h63⟩, h64⟩, h65⟩, h66⟩, h67⟩ := h6
    refine ⟨h61, ?_, h63, h64, h65, h66, fun hk ↦ ?_⟩
    · intro h0; rw [h0] at h62; cases h62
    rw [show Nat.beq (sKind (tget wS 6 5 K.T.sl (si - 1))) kRoot = true from nbeq_iff.mpr hk] at h67
    simpa [band, Nat.ble_eq, Nat.blt_eq] using h67

/-- **An input known**, unfolded. -/
theorem known_spec {q i w : ℕ} (h : known K q i w = true) :
    (vSh (vlane K w) = 0 ∧ 2 ≤ cellOf K w) ∨
    (vSh (vlane K w) ≠ 0 ∧ 2 ≤ sCell (tget wS 6 5 K.T.sl (vSh (vlane K w) - 1)) ∧
      (sHp (tget wS 6 5 K.T.sl (vSh (vlane K w) - 1)) < q ∨
        (sHp (tget wS 6 5 K.T.sl (vSh (vlane K w) - 1)) = q ∧
          (sKind (tget wS 6 5 K.T.sl (vSh (vlane K w) - 1)) = kRoot ∨
            sHj (tget wS 6 5 K.T.sl (vSh (vlane K w) - 1)) < i)))) := by
  unfold known at h
  dsimp only at h
  by_cases hs : vSh (vlane K w) = 0
  · rw [show Nat.beq (vSh (vlane K w)) 0 = true from nbeq_iff.mpr hs] at h
    simp only [Bool.cond_true, Nat.ble_eq] at h
    exact .inl ⟨hs, h⟩
  · rw [beq_false hs] at h
    simp only [Bool.cond_false, band, Nat.ble_eq, Bool.or_eq_true, Nat.blt_eq, nbeq_iff] at h
    exact .inr ⟨hs, h.1, h.2⟩

/-- **A justification**, unfolded. -/
theorem justOk_spec {st : Stmt} {q i c s o : ℕ} (h : justOk K st q i c s o = true) :
    (sKind s = kRoot → o % 4 ≠ 3) ∧
    (sKind s ≠ kRoot → ∃ a, st = .atom a ∧
      ((sKind s = kEq ∧ ∃ u, eqAt a i = some u ∧ vSh (vlane K u.idx) ≠ 0 ∧ cellOf K u.idx = c ∧
          known K q i u.idx = true) ∨
       (sKind s = kConstK ∧ ∃ y, constAt a i = some y ∧ sAux s < K.T.nst ∧
          tO (tget wT 6 5 K.T.st (sAux s)) = c ∧ tK0 (tget wT 6 5 K.T.st (sAux s)) = y.1 ∧
          tK1 (tget wT 6 5 K.T.st (sAux s)) = y.2) ∨
       (sKind s = kConstA ∧ ∃ y, constAt a i = some y ∧ sAux s < K.T.nat ∧
          aConst (tget wA 4 5 K.T.an (sAux s)) = 1 ∧ aCell (tget wA 4 5 K.T.an (sAux s)) = c ∧
          aK0 (tget wA 4 5 K.T.an (sAux s)) = y.1 ∧ aK1 (tget wA 4 5 K.T.an (sAux s)) = y.2 ∧
          aP (tget wA 4 5 K.T.an (sAux s)) < q ∧ q < aE (tget wA 4 5 K.T.an (sAux s))) ∨
       (sKind s = kKey ∧ ∃ op ins, keyAt a i = some (op, ins) ∧ sAux s < K.T.nat ∧
          aConst (tget wA 4 5 K.T.an (sAux s)) = 0 ∧ aCell (tget wA 4 5 K.T.an (sAux s)) = c ∧
          aOp (tget wA 4 5 K.T.an (sAux s)) = op ∧ aIns (tget wA 4 5 K.T.an (sAux s)) = keyPack K op ins ∧
          aP (tget wA 4 5 K.T.an (sAux s)) < q ∧ q < aE (tget wA 4 5 K.T.an (sAux s)) ∧
          ∀ w ∈ ins, known K q i w.idx = true))) := by
  unfold justOk at h
  dsimp only at h
  by_cases hr : sKind s = kRoot
  · rw [show Nat.beq (sKind s) kRoot = true from nbeq_iff.mpr hr] at h
    simp only [Bool.cond_true, Bool.not_eq_true', ] at h
    refine ⟨fun _ h3 ↦ ?_, fun h' ↦ absurd hr h'⟩
    have : Nat.mod o 4 = 3 := h3
    rw [this] at h; cases h
  rw [beq_false hr] at h
  simp only [Bool.cond_false] at h
  refine ⟨fun h' ↦ absurd h' hr, fun _ ↦ ?_⟩
  cases st with
  | atom a =>
    refine ⟨a, rfl, ?_⟩
    simp only at h
    by_cases h1 : sKind s = kEq
    · rw [show Nat.beq (sKind s) kEq = true from nbeq_iff.mpr h1] at h
      simp only [Bool.cond_true] at h
      left
      refine ⟨h1, ?_⟩
      split at h
      · rename_i u hu
        simp only [band, Bool.not_eq_true', nbeq_iff] at h
        exact ⟨u, hu, fun h0 ↦ by rw [h0] at h; simp at h, h.1.2, h.2⟩
      · cases h
    rw [beq_false h1] at h
    simp only [Bool.cond_false] at h
    by_cases h2 : sKind s = kConstK
    · rw [show Nat.beq (sKind s) kConstK = true from nbeq_iff.mpr h2] at h
      simp only [Bool.cond_true] at h
      right; left
      refine ⟨h2, ?_⟩
      split at h
      · rename_i y hy
        simp only [band, Nat.blt_eq, nbeq_iff] at h
        exact ⟨y, hy, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
      · cases h
    rw [beq_false h2] at h
    simp only [Bool.cond_false] at h
    by_cases h3 : sKind s = kConstA
    · rw [show Nat.beq (sKind s) kConstA = true from nbeq_iff.mpr h3] at h
      simp only [Bool.cond_true] at h
      right; right; left
      refine ⟨h3, ?_⟩
      split at h
      · rename_i y hy
        simp only [band, Nat.blt_eq, nbeq_iff] at h
        exact ⟨y, hy, h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
      · cases h
    rw [beq_false h3] at h
    simp only [Bool.cond_false] at h
    by_cases h4 : sKind s = kKey
    · rw [show Nat.beq (sKind s) kKey = true from nbeq_iff.mpr h4] at h
      simp only [Bool.cond_true] at h
      right; right; right
      refine ⟨h4, ?_⟩
      split at h
      · rename_i op ins hk
        simp only [band, Nat.blt_eq, nbeq_iff, allR_eq, List.all_eq_true] at h
        exact ⟨op, ins, hk, h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
          h.1.2, h.2⟩
      · cases h
    rw [beq_false h4] at h
    cases h
  | _ => cases h

/-- **An anchor**, unfolded. -/
theorem anchorOk_spec {st : Stmt} {cx : Ctx} {an : ℕ} (h : anchorOk K st cx an = true) :
    ∃ a, st = .atom a ∧ aE an = cx.e ∧ 2 ≤ aCell an ∧ ∃ w, (atomVals a)[aJ an]? = some w ∧
      cellOf K w.idx = aCell an ∧
      ((aConst an = 1 ∧ constAt a (aJ an) = some (aK0 an, aK1 an)) ∨
       (aConst an ≠ 1 ∧ ∃ op ins, keyAt a (aJ an) = some (op, ins) ∧ aOp an = op ∧
          aIns an = keyPack K op ins ∧ ∀ x ∈ ins, 2 ≤ cellOf K x.idx)) := by
  cases st with
  | atom a =>
    refine ⟨a, rfl, ?_⟩
    unfold anchorOk at h
    simp only [band, nbeq_iff, Nat.ble_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    split at h3
    · rename_i w hw
      refine ⟨h1, h2, w, hw, nbeq_iff.mp h3, ?_⟩
      by_cases hc : aConst an = 1
      · rw [show Nat.beq (aConst an) 1 = true from nbeq_iff.mpr hc] at h4
        simp only [Bool.cond_true] at h4
        split at h4
        · rename_i y hy
          simp only [band, nbeq_iff] at h4
          left; refine ⟨hc, ?_⟩; rw [hy, h4.1, h4.2]
        · cases h4
      · rw [beq_false hc] at h4
        simp only [Bool.cond_false] at h4
        split at h4
        · rename_i op ins hk
          simp only [band, nbeq_iff, allR_eq, List.all_eq_true, Nat.ble_eq] at h4
          exact .inr ⟨hc, op, ins, hk, h4.1.1, h4.1.2, h4.2⟩
        · cases h4
    · cases h3
  | _ => simp [anchorOk] at h

end Home

end
end LeanVM.Guest.B2C.ShareL
