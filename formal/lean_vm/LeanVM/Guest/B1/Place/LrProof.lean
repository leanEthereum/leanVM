/-
  LeanVM.Guest.B1.Place.LrProof

  `level_residual` complete placed, at every specialization of `lrTable`: the proof.
-/

module

public import LeanVM.Guest.B1.Place.LrFar

/-!
# `level_residual`, placed: the proof

`lrAtO_of`: at every frame pointer `fp`, three cases.
* Some memory defined below `2^κ` holds the buffers `lrBufL … fp` and the caller's words: the
  loops are pure, so each has one size on all of them (`guarded_uniform`, from `lr_loop1_rel`,
  `lr_loop2_rel` on the memory kept on those words), and the function is placed on each
  (`lr_relAtIn`); the bound by `TotalLe` on that memory's tree.
* None does, but one holds the caller's words: nothing to prove on a memory, the buffers fit in
  the frame and buffers, within the bound by `lr_far_bound`.
* None holds the caller's words: nothing to prove, no words.

`level_residual_completeAt`: every entry of `lrTable`, its shapes' facts by `decide`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **`level_residual` at `(name, q, cols)` is `LrAtO` at every bound.** -/
theorem lrAtO_of {name loop1 loop2 : String} {q cols : ℕ}
    (hlr : FnIs name (osParams 3) (lrBody q loop1 loop2))
    (hl1 : FnIs loop1 (osParams 6) (lrLoop1Body cols loop1))
    (hl2 : q % resBatch ≠ 0 → FnIs loop2 (osParams 6) (lrLoop2Body cols loop2))
    (hrb : FnIs (rbName cols) (osParams 4) (rbBody cols)) (hn : 1 ≤ cols) (hq8 : 0 < q / resBatch)
    (hqc : (q + cols + 1) * (q + 2) ≤ 2 ^ 64 - 1) (fs : String → ℕ) (cert : String → V → ℕ)
    (κ : ℕ) (Bd : Option ℕ) : LrAtO fs cert κ name q cols Bd := by
  intro Lin P BD M D p hreg hmem hBd fp
  classical
  have hq : q + 2 < 2 ^ 64 - 1 := by nlinarith
  set S := (lrSizes q).sum with hSdef
  set Lb := lrBufL fs name q cols D M p fp with hLb
  have hWb : Within Lb (fp + fs name) S := bufL_within _ _ _ (lrWords_forall₂ D cols M p q)
  have hDb : DisjL Lb := bufL_disj _ _ _ (lrWords_forall₂ D cols M p q)
  have hRb : ∀ i, RegionL Lb i → fp + fs name ≤ i ∧ i < fp + fs name + S := by
    rintro i ⟨e, he, h1, h2⟩
    have := hWb e he; omega
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd (Lb ++ Lin)
  · set Lk := Lb ++ Lin with hLk
    have hregK : ∀ i, RegionL Lk i → RegionL Lin i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + S) := by
      rintro i ⟨e, he, h1, h2⟩
      rcases List.mem_append.mp he with he | he
      · exact Or.inr (hRb i ⟨e, he, h1, h2⟩)
      · exact Or.inl ⟨e, he, h1, h2⟩
    have hLinK : ∀ i, RegionL Lin i → RegionL Lk i :=
      fun i ⟨e, he, h⟩ ↦ ⟨e, List.mem_append_right _ he, h⟩
    have hLbK : ∀ i, RegionL Lb i → RegionL Lk i :=
      fun i ⟨e, he, h⟩ ↦ ⟨e, List.mem_append_left _ he, h⟩
    have hres : ∀ rd, LowDef κ rd → MemL rd Lk →
        (∀ i < q, LoadHolds (Main.restrict rd (RegionL Lk)) P i (p i)) ∧
        (∀ s < cols, LoadHolds (Main.restrict rd (RegionL Lk)) BD s (D s)) ∧
        MemL (Main.restrict rd (RegionL Lk)) Lb := by
      intro rd hl hL
      obtain ⟨hLb', hLin'⟩ := Main.memL_append.mp hL
      obtain ⟨hP, hD⟩ := hmem rd hl hLin'
      refine ⟨fun i hi ↦ Main.loadHolds_restrict (hP i hi) ?_,
        fun s hs ↦ Main.loadHolds_restrict (hD s hs) ?_, Main.memL_restrict hLb' hLbK⟩
      · obtain ⟨j, hj, hR⟩ := hreg (0, q) (by simp) i hi
        exact ⟨j, hj, hLinK j hR⟩
      · obtain ⟨j, hj, hR⟩ := hreg (1, cols) (by simp) s hs
        exact ⟨j, hj, hLinK j hR⟩
    obtain ⟨m1, hm1⟩ := guarded_uniform (lrLoop1_pureIn hl1 hrb) List.mem_cons_self fs cert
      (κ := κ) (Lk := Lk)
      (fun hg rd hl hL ↦ lr_loop1_rel hl1 hrb hn hq8 (hres rd hl hL).1 (hres rd hl hL).2.1
        (hres rd hl hL).2.2 hg)
    obtain ⟨m2, hm2a, hm2b⟩ : ∃ m2, (q % resBatch = 0 → m2 = 0) ∧ ∀ rd, LowDef κ rd → MemL rd Lk →
        (q % resBatch ≠ 0 → if 1 + gen ^ (q % resBatch) ≠ 0 then
          RelAtIn coreProgram fs cert rd (RegionL Lk) (fun _ ↦ False) (fp + fs name + S + m1) m2
            loop2 [1, gen ^ (q % resBatch), ofK (addressOfIndex (fp + fs name + (q / resBatch + 1))),
              P * gen ^ (resBatch * (q / resBatch)), BD, M] []
          else m2 = fs loop2) := by
      by_cases h0 : q % resBatch = 0
      · exact ⟨0, fun _ ↦ rfl, fun _ _ _ h ↦ absurd h0 h⟩
      · obtain ⟨m2, hm2⟩ := guarded_uniform (lrLoop2_pureIn (hl2 h0)) (List.mem_singleton_self _)
          fs cert (κ := κ) (Lk := Lk)
          (fun hg rd hl hL ↦ lr_loop2_rel (hl2 h0) hn h0 (hres rd hl hL).1 (hres rd hl hL).2.1
            (hres rd hl hL).2.2 hg)
        exact ⟨m2, fun h ↦ absurd h h0, fun rd hl hL _ ↦ hm2 _ rd hl hL⟩
    have key : ∀ rd, LowDef κ rd → MemL rd Lk →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ ↦ False) fp (fs name + S + (m1 + m2))
          name [P, BD, M] [lrAcc D cols M p q] :=
      fun rd hl hL ↦ lr_relAtIn hlr hq fs cert (Main.memL_append.mp hL).1 (hm1 _ rd hl hL)
        (hm2b rd hl hL) hm2a hregK
    refine ⟨fs name + S + (m1 + m2), Lb, [lrAcc D cols M p q], [], ⟨rfl, rfl⟩, ?_,
      by simpa using hDb, ?_, fun rd hl hL ↦ relAtIn_dmono (key rd hl (by simpa using hL))
        (fun i hi ↦ ?_)⟩
    · simpa using hWb.mono (b' := fp) (n' := fs name + S + (m1 + m2)) (Nat.le_add_right _ _) (by omega)
    · intro B hB
      obtain ⟨rd, hl, hL⟩ := hex
      obtain ⟨t, hname, hv, hbo, -, htot, -⟩ := key rd hl hL
      rw [← htot]; exact hBd B hB rd t _ _ hname hv hbo
    · obtain ⟨e, he, _⟩ := hi; simp at he
  · by_cases hex1 : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
    · obtain ⟨rd1, hl1', hL1⟩ := hex1
      obtain ⟨hP1, hD1⟩ := hmem rd1 hl1' hL1
      exact ⟨fs name + S, Lb, [lrAcc D cols M p q], [], ⟨rfl, rfl⟩,
        by simpa using hWb.mono (b' := fp) (n' := fs name + S) (Nat.le_add_right _ _) (by omega), by simpa using hDb,
        fun B hB ↦ lr_far_bound hlr hl1 hl2 hrb hn hq8 hqc fs cert hreg hP1 hD1 (hBd B hB),
        fun rd hl hL ↦ absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
    · exact ⟨0, [], [lrAcc D cols M p q], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
        fun _ _ ↦ Nat.zero_le _, fun rd hl hL ↦ absurd ⟨rd, hl, by simpa using hL⟩ hex1⟩

/-- An entry's shape: `residual_batch` at its columns, at least one column, a batch, and room for
the far window. -/
def lrShapeOk (e : String × ℕ × ℕ × String × String) : Bool :=
  rbTable.contains (rbName e.2.2.1, e.2.2.1) && decide (1 ≤ e.2.2.1) && decide (0 < e.2.1 / resBatch) &&
    decide ((e.2.1 + e.2.2.1 + 1) * (e.2.1 + 2) ≤ 2 ^ 64 - 1)

theorem lrTable_shapes : lrTable.all lrShapeOk = true := by decide +kernel

theorem lrTable_facts : ∀ e ∈ lrTable, (rbName e.2.2.1, e.2.2.1) ∈ rbTable ∧ 1 ≤ e.2.2.1 ∧
    0 < e.2.1 / resBatch ∧ (e.2.1 + e.2.2.1 + 1) * (e.2.1 + 2) ≤ 2 ^ 64 - 1 := by
  intro e he
  have h := List.all_eq_true.mp lrTable_shapes e he
  simp only [lrShapeOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **`level_residual` is complete placed at every specialization.** -/
theorem level_residual_completeAt : level_residual_completeAt_Spec := by
  intro fs cert κ _ _ _ e he Bd
  obtain ⟨hlr, hl1, hl2⟩ := lrTable_ok e he
  obtain ⟨hrbm, hn, hq8, hqc⟩ := lrTable_facts e he
  have hrb : FnIs (rbName e.2.2.1) (osParams 4) (rbBody e.2.2.1) :=
    rbTable_ok (rbName e.2.2.1, e.2.2.1) hrbm
  exact lrAtO_of hlr hl1 hl2 hrb hn hq8 hqc fs cert κ Bd

end
end LeanVM.Guest.B1
