/-
  LeanVM.Guest.B1.VerifySub.C.Sqz

  A squeeze of `verify_sub` (`vsSqzT`), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Fpw

/-!
# A squeeze, honestly

`vsSqzT_complete`: with the zero cells `10 .. 13` zero and the capacity cells `capb .. capb + 4`
canonical, the squeeze's `KECCAK` atom and `challenge_from_state` hold on the honest valuation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

theorem vsSqzT_noNe (capb o : ℕ) : (vsSqzT capb o).all noNeB = true := by
  simp [vsSqzT, keccakA, challengeT, noNeB]

variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
/-- **A squeeze, honestly.** -/
theorem vsSqzT_complete (hl : args.length = 6) {capb o : ℕ}
    (hmem : ∀ s ∈ vsSqzT capb o, s ∈ vsCPre)
    (hz : ∀ i ∈ [8, 9, 10, 11], vsσ rd w args (.n i) = 0)
    (hcap : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (capb + i))))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd (vsσ rd w args) (vsSqzT capb o) next kret := by
  have hG : ∀ s ∈ vsSqzT capb o, GoodS rd vsSL w (vsσ rd w args) s := fun s hs ↦ by
    have h := vs_goodS (rd := rd) (w := w) hl (hmem s hs)
    rwa [fixNe_of_noNe (List.all_eq_true.mp (vsSqzT_noNe capb o) s hs)] at h
  have c0 : IsCanonical128 (0 : E) := canonical_zero
  have hk : Good rd vsSL w (vsσ rd w args)
      (.keccak ([V.n 8, V.n 8, V.n 8, V.n 8, V.n 8, V.n 9, V.n 10, V.n 11] ++ vsRun capb 5)
        (vsRun o 13) false false) :=
    hG (keccakA ([V.n 8, V.n 8, V.n 8, V.n 8, V.n 8, V.n 9, V.n 10, V.n 11] ++ vsRun capb 5)
      (vsRun o 13)) (by simp [vsSqzT])
  have hcan : AllCanonical
      (([V.n 8, V.n 8, V.n 8, V.n 8, V.n 8, V.n 9, V.n 10, V.n 11] ++ vsRun capb 5).map
        (vsσ rd w args)) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    simp only [vsRun, List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
      List.mem_range] at hv
    have hz' : ∀ i ∈ [8, 9, 10, 11], IsCanonical128 (vsσ rd w args (.n i)) :=
      fun i hi ↦ by rw [hz i hi]; exact c0
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩
    · exact hz' 8 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 9 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 11 (by simp)
    · exact hcap i hi
  have hK := keccakA_complete hk hcan
  have h1 : IsCanonical128 (vsσ rd w args (.n (o + 1))) := by
    have := (good_keccak13 hk (by simp [vsRun])).2.2 ⟨1, by norm_num⟩
    simp [cells13, vsRun] at this
    rw [this]
    exact canon_cellsOfState _ _ _
  have hch := challenge_complete (C := C)
    (fun s hs ↦ hG s (List.mem_cons_of_mem _ hs)) h1
  simp only [vsSqzT, keccakA, Stmt.HoldsList, Stmt.Holds]
  exact ⟨hK, hch.2 hn⟩

/-- **`fp_w` and `β`'s squeeze, honestly.** -/
theorem vsFpwT_complete (hl : args.length = 6) {a0 a1 a2 a3 : E}
    (ha : ReadsAt rd (vsσ rd w args (.n 346)) [a0, a1, a2, a3])
    (hfp : ReadsAt rd (vsσ rd w args (.n 427)) (eqKernel [a0, a1, a2, a3]))
    (hz : ∀ i ∈ [8, 9, 10, 11], vsσ rd w args (.n i) = 0)
    (hcap : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (415 + i))))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd (vsσ rd w args) vsFpwT next kret := by
  have hsq := vsSqzT_complete (C := C) (kret := kret) hl (capb := 415) (o := 604)
    (fun s hs ↦ vs_mem_slice (n := 346) (blk := vsFpwT) (by decide +kernel)
      (by rw [vsFpwT]; exact List.mem_append_right _ hs)) hz hcap hn
  rw [vsFpwT, holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc]
  exact ⟨trivial, vsFpw_loop hl ha hfp _ (fun x hx ↦ List.mem_range.1 hx) hsq⟩

theorem kc_noNe (ins : List V) (o : ℕ) :
    (keccakA ins (vsRun o 13) :: challengeT (.n o) (.n (o + 1)) (o + 13)).all noNeB = true := by
  simp [keccakA, challengeT, noNeB]

set_option maxRecDepth 100000 in
/-- **A permutation and its challenge, honestly**: on canonical inputs, the `KECCAK` atom and
`challenge_from_state` hold, and the permutation's thirteen output cells are canonical. -/
theorem kc_complete (hl : args.length = 6) {ins : List V} {o : ℕ}
    (hmem : ∀ s ∈ keccakA ins (vsRun o 13) :: challengeT (.n o) (.n (o + 1)) (o + 13), s ∈ vsCPre)
    (hcan : AllCanonical (ins.map (vsσ rd w args)))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    (∀ k < 13, IsCanonical128 (vsσ rd w args (.n (o + k)))) ∧
      Stmt.HoldsList C rd (vsσ rd w args)
        (keccakA ins (vsRun o 13) :: challengeT (.n o) (.n (o + 1)) (o + 13)) next kret := by
  have hG : ∀ s ∈ keccakA ins (vsRun o 13) :: challengeT (.n o) (.n (o + 1)) (o + 13),
      GoodS rd vsSL w (vsσ rd w args) s := fun s hs ↦ by
    have h := vs_goodS (rd := rd) (w := w) hl (hmem s hs)
    rwa [fixNe_of_noNe (List.all_eq_true.mp (kc_noNe ins o) s hs)] at h
  have hk : Good rd vsSL w (vsσ rd w args) (.keccak ins (vsRun o 13) false false) :=
    hG (keccakA ins (vsRun o 13)) List.mem_cons_self
  have hK := keccakA_complete hk hcan
  have hout : ∀ k < 13, IsCanonical128 (vsσ rd w args (.n (o + k))) := by
    intro k hk13
    have := (good_keccak13 hk (by simp [vsRun])).2.2 ⟨k, hk13⟩
    simp [cells13, vsRun, List.getD_eq_getElem?_getD, hk13] at this
    rw [this]
    exact canon_cellsOfState _ _ _
  have hch := challenge_complete (C := C)
    (fun s hs ↦ hG s (List.mem_cons_of_mem _ hs)) (hout 1 (by norm_num))
  simp only [keccakA, Stmt.HoldsList, Stmt.Holds]
  exact ⟨hout, hK, hch.2 hn⟩

end
end LeanVM.Guest.B1.VerifySub
