/-
  LeanVM.Guest.B1.Whir.CHead

  The head of open_stacked, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CLevels

/-!
# The head, honestly

`osHead_complete`: on the first round polynomial's two words `c0`, `c2` at the cursor and the
commitment's root stored at `level_roots`, the head holds at the values `headF` (the words, the
fixed buffers at the pointers `P`), and the levels start from its state.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The head's values from `9`. -/
def headVals (c : OsCfg) (target : E) (P : OsPtrs) (c0 c2 : E) : List E :=
  [c0, c2, target + c2, gw (4 * c.capLen), P.caps, gw c.capLen, P.flags, gw c.yrLen, P.fmsg,
    gw (2 * c.levels.length), P.roots, gw c.nFolds, P.fch, gw c.levels.length, P.betas,
    gw c.levels.length, P.mus, gw c.posLen, P.qpos, gw c.posLen, P.qbp, gw 128, P.win] ++
    (List.range 128).map (fun i ↦ word i 0 0) ++
    [gw (c.levels.length * ligColsCap), P.oodz, gw (c.levels.length * oodSlots), P.ood]

/-- The head's values. -/
def headF (c : OsCfg) (σ : Val) (P : OsPtrs) (c0 c2 : E) : ℕ → E :=
  fun i ↦ (headVals c (σ (.n 5)) P c0 c2).getD (i - 9) 0

theorem headVals_tab (c : OsCfg) (target : E) (P : OsPtrs) (c0 c2 : E) {i : ℕ} (hi : i < 128) :
    (headVals c target P c0 c2).getD (23 + i) 0 = word i 0 0 := by
  unfold headVals
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp)]
  simp [hi]

theorem headVals_end (c : OsCfg) (target : E) (P : OsPtrs) (c0 c2 : E) (j : ℕ) :
    (headVals c target P c0 c2).getD (151 + j) 0 =
      [gw (c.levels.length * ligColsCap), P.oodz, gw (c.levels.length * oodSlots), P.ood].getD j 0 := by
  unfold headVals
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- **The head, honestly.** -/
theorem osHead_complete {c : OsCfg} (σ : Val) (P : OsPtrs) {c0 c2 : E}
    (h0 : LoadHolds rd (σ (.n 8)) 0 c0) (h2 : LoadHolds rd (σ (.n 8)) 1 c2)
    (hr0 : LoadHolds rd P.roots 0 (σ (.n 6))) (hr1 : LoadHolds rd P.roots 1 (σ (.n 7)))
    (hwin : ∀ i < 128, LoadHolds rd P.win i (word i 0 0))
    (hcan : AllCanonical [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)]) :
    BlkF C rd σ 9 164 (headF c σ P c0 c2) (osHead c).1
      (fun σ' ↦ LvsSt σ' (osHead c).2
        ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(c0, dsObserve), (c2, dsObserve)]⟩
        [c0, σ (.n 5) + c2, c2] (σ (.n 5)) (σ (.n 8) * gen ^ 2) ∧ ptrsOf σ' = P ∧
        AgreeBelow 9 σ σ') := by
  intro σ' hg hr
  have V : ∀ j < 155, σ' (.n (9 + j)) = (headVals c (σ (.n 5)) P c0 c2).getD j 0 :=
    fun j hj ↦ by rw [hr _ (by omega) (by omega)]; simp only [headF, Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  have v6 := V 6 (by omega); have v7 := V 7 (by omega); have v8 := V 8 (by omega)
  have v9 := V 9 (by omega); have v10 := V 10 (by omega); have v11 := V 11 (by omega)
  have v12 := V 12 (by omega); have v13 := V 13 (by omega); have v14 := V 14 (by omega)
  have v15 := V 15 (by omega); have v16 := V 16 (by omega); have v17 := V 17 (by omega)
  have v18 := V 18 (by omega); have v19 := V 19 (by omega); have v20 := V 20 (by omega)
  have v21 := V 21 (by omega); have v22 := V 22 (by omega)
  simp only [headVals, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd,
    Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
  have ve : ∀ j < 4, σ' (.n (160 + j)) =
      [gw (c.levels.length * ligColsCap), P.oodz, gw (c.levels.length * oodSlots), P.ood].getD j 0 :=
    fun j hj ↦ by rw [show 160 + j = 9 + (151 + j) by omega, V _ (by omega), headVals_end _ _ _ _ _ j]
  have w0 := ve 0 (by omega); have w1 := ve 1 (by omega); have w2 := ve 2 (by omega)
  have w3 := ve 3 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.add_zero] at w0 w1 w2 w3
  have vt : ∀ i < 128, σ' (.n (32 + i)) = word i 0 0 := fun i hi ↦ by
    rw [show 32 + i = 9 + (23 + i) by omega, V _ (by omega), headVals_tab _ _ _ _ _ hi]
  have g0 := hg 0 (by omega); have g1 := hg 1 (by omega); have g2 := hg 2 (by omega)
  have g3 := hg 3 (by omega); have g4 := hg 4 (by omega); have g5 := hg 5 (by omega)
  have g6 := hg 6 (by omega); have g7 := hg 7 (by omega); have g8 := hg 8 (by omega)
  have hwt : AllOk C rd σ' osWinTabs := by
    unfold osWinTabs
    rw [allOk_flatten]
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hi
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨vt i hi, by rw [vt i hi, show osWin = 9 + 22 from rfl, v22]; exact hwin i hi⟩
  refine ⟨?_, ?_, ?_, hg⟩
  · simp only [osHead, allOk_append]
    refine ⟨⟨⟨?_, hwt⟩, ?_⟩, ?_⟩
    · simp only [osHeap, allOk_cons, allOk_nil, and_true,
        StmtOk, Atom.Holds, osCaps, osFlags, osRoots, v0, v1, v2, v3, v5, v7, v9, v10, v11, v13,
        v15, v17, v19, v21, g5, g6, g7, g8, and_self]
      exact ⟨⟨h0, h2⟩, hr0, hr1⟩
    · simp only [osHeap, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, w0]
    · simp only [osHeap, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, w2]
  · refine ⟨?_, ?_, ?_, ?_, rfl, (show 2 ≤ 8 by omega), ⟨?_, show 9 < 164 by omega,
      show 10 < 164 by omega, show 8 < 164 by omega, show 9 < 164 by omega, show 11 < 164 by omega,
      show 10 < 164 by omega, show 5 < 164 by omega⟩, le_rfl, ?_, trivial, (fun p hp ↦ by cases hp),
      matsOk_nil σ', (fun _ h ↦ absurd h (by simp [osHead]))⟩
    · simp only [OsSt.F, OsSt.fsv, osHead, List.map_cons, List.map_nil, g0, g1, g2, g3, g4, v0, v1]
    · simp only [OsSt.quad, osHead, v0, v1, v2]
    · simp only [osHead, g5]
    · simp only [OsSt.cur, osHead, g8]
    · intro f hf
      simp only [osHead, List.mem_cons, List.not_mem_nil, or_false] at hf
      show f < 164
      omega
    · simp only [OsSt.fsv, osHead, List.map_cons, List.map_nil, g0, g1, g2, g3, g4]; exact hcan
  · cases P
    simp only [ptrsOf, osCaps, osFlags, osFmsg, osRoots, osFch, osBetas, osMus, osQpos, osQbp,
      osWin, osOodz, osOod, v4, v6, v8, v10, v12, v14, v16, v18, v20, v22, w1, w3]

end
end LeanVM.Guest.B1.Whir
