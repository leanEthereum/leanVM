/-
  LeanVM.Guest.B1.Place.LrFar

  A bound on `level_residual`'s frame and buffers from any bound on its trees: one honest tree,
  its buffers on a window of addresses its other loads miss.
-/

module

public import LeanVM.Guest.B1.Place.LrBufs

/-!
# The frame and buffers within a bound on the trees

`lr_far_bound`: if every valid tree of `level_residual` at `[P, BD, M]` has at most `B` words, its
frame and buffers fit in `B`, as soon as some memory holds the positions and the row. The memory:
those words where the positions and the row are, the honest chains on `L` consecutive addresses
missing them (`exists_free_window`), the function placed there (`lr_relAtIn`) at the frame pointer
whose buffers land on them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem addr_ordG_mul_add (k x : ℕ) :
    addressOfIndex ((2 ^ 64 - 1) * k + x) = addressOfIndex x := by
  rw [Parameters.addressOfIndex, Parameters.addressOfIndex, pow_add, pow_mul, ← orderOf_g,
    pow_orderOf_eq_one, one_pow, one_mul]

theorem lrSizes_sum (q : ℕ) : 0 < (lrSizes q).sum ∧ (lrSizes q).sum ≤ q + 2 := by
  have hqd := Nat.div_add_mod q resBatch
  have h1 : q / resBatch ≤ q := Nat.div_le_self _ _
  unfold lrSizes
  split
  · simp only [List.sum_cons, List.sum_nil, resBatch] at *; omega
  · simp only [List.sum_cons, List.sum_nil, resBatch] at *; omega

theorem lrWords_flatten_length (D : ℕ → E) (cols : ℕ) (M : E) (p : ℕ → E) (q : ℕ) :
    (lrWords D cols M p q).flatten.length = (lrSizes q).sum := by
  unfold lrSizes lrWords
  split <;> simp [lrCH, lrRS]

/-- **`level_residual`'s frame and buffers within any bound on its trees**, given a memory holding
the positions and the row where the pointers say. -/
theorem lr_far_bound {name loop1 loop2 : String} {q cols : ℕ}
    (hlr : FnIs name (osParams 3) (lrBody q loop1 loop2))
    (hl1 : FnIs loop1 (osParams 6) (lrLoop1Body cols loop1))
    (hl2 : q % resBatch ≠ 0 → FnIs loop2 (osParams 6) (lrLoop2Body cols loop2))
    (hrb : FnIs (rbName cols) (osParams 4) (rbBody cols)) (hn : 1 ≤ cols) (hq8 : 0 < q / resBatch)
    (hqc : (q + cols + 1) * (q + 2) ≤ 2 ^ 64 - 1) (fs : String → ℕ) (cert : String → V → ℕ)
    {P BD M : E} {D p : ℕ → E} {R : ℕ → Prop} (hreg : RegPtrs [(0, q), (1, cols)] [P, BD, M] R)
    {rd1 : Reader} (hP1 : ∀ i < q, LoadHolds rd1 P i (p i))
    (hD1 : ∀ s < cols, LoadHolds rd1 BD s (D s)) {B : ℕ}
    (hB : TotalLe coreProgram fs name (fun _ ↦ B)) :
    fs name + (lrSizes q).sum ≤ B := by
  classical
  have hq : q + 2 < 2 ^ 64 - 1 := by nlinarith
  obtain ⟨hS1, hS2⟩ := lrSizes_sum q
  set S := (lrSizes q).sum with hSdef
  set As : List K := (List.range q).map (fun t ↦ P.limb 0 * addressOfIndex t) ++
    (List.range cols).map (fun s ↦ BD.limb 0 * addressOfIndex s) with hAs
  have hlen : As.length = q + cols := by simp [hAs]
  obtain ⟨c, hc, hfree⟩ := exists_free_window As hS1 (by
    rw [hlen]; exact le_trans (Nat.mul_le_mul_left _ hS2) hqc)
  set fpF := c + (2 ^ 64 - 2) * fs name with hfpF
  have hbF : fpF + fs name = (2 ^ 64 - 1) * fs name + c := by
    rw [hfpF, show (2 : ℕ) ^ 64 - 1 = (2 ^ 64 - 2) + 1 by norm_num, Nat.add_mul, Nat.one_mul]
    ring
  have haddr : ∀ t, addressOfIndex (fpF + fs name + t) = addressOfIndex (c + t) := by
    intro t; rw [hbF, Nat.add_assoc, addr_ordG_mul_add]
  set flat := (lrWords D cols M p q).flatten with hflat
  let rdF : Reader := fun A ↦
    if h : ∃ t, t < S ∧ A = addressOfIndex (c + t) then some (flat.getD (Classical.choose h) 0)
    else if A ∈ As then rd1 A else none
  have hW : ∀ t < S, rdF (addressOfIndex (c + t)) = some (flat.getD t 0) := by
    intro t ht
    simp only [rdF]
    split
    · next h =>
      obtain ⟨h1, h2⟩ := Classical.choose_spec h
      have e := gpow_injOn (Set.mem_Iio.mpr (show c + t < 2 ^ 64 - 1 by omega))
        (Set.mem_Iio.mpr (show c + Classical.choose h < 2 ^ 64 - 1 by omega)) h2
      rw [show Classical.choose h = t by omega]
    · next h => exact absurd ⟨t, ht, rfl⟩ h
  have hA : ∀ A ∈ As, rdF A = rd1 A := by
    intro A hAm
    simp only [rdF]
    split
    · next h =>
      obtain ⟨t, ht, rfl⟩ := h
      exact absurd hAm (hfree t ht)
    · rfl
  have hsupp : ∀ A v, rdF A = some v → (∃ t, t < S ∧ A = addressOfIndex (c + t)) ∨ A ∈ As := by
    intro A v h
    simp only [rdF] at h
    split at h
    · next h' => exact Or.inl h'
    · split at h
      · next h' => exact Or.inr h'
      · exact absurd h (by simp)
  let Rw : ℕ → Prop := fun i ↦ (∃ t < q, P.limb 0 * addressOfIndex t = addressOfIndex i) ∨
    ∃ s < cols, BD.limb 0 * addressOfIndex s = addressOfIndex i
  let Rk : ℕ → Prop := fun i ↦ Rw i ∨ (fpF + fs name ≤ i ∧ i < fpF + fs name + S)
  have hsuppK : ∀ A v, rdF A = some v → ∃ i, A = addressOfIndex i ∧ Rk i := by
    intro A v h
    rcases hsupp A v h with ⟨t, ht, rfl⟩ | hm
    · exact ⟨fpF + fs name + t, (haddr t).symm, Or.inr ⟨Nat.le_add_right _ _, by omega⟩⟩
    · rw [hAs, List.mem_append, List.mem_map, List.mem_map] at hm
      rcases hm with ⟨t, ht, rfl⟩ | ⟨s, hs, rfl⟩
      · obtain ⟨i, hi, -⟩ := hreg (0, q) (by simp) t (List.mem_range.mp ht)
        exact ⟨i, hi, Or.inl (Or.inl ⟨t, List.mem_range.mp ht, hi⟩)⟩
      · obtain ⟨i, hi, -⟩ := hreg (1, cols) (by simp) s (List.mem_range.mp hs)
        exact ⟨i, hi, Or.inl (Or.inr ⟨s, List.mem_range.mp hs, hi⟩)⟩
  have hP : ∀ i < q, LoadHolds rdF P i (p i) := fun i hi ↦
    ⟨(hP1 i hi).1, by
      rw [hA _ (by rw [hAs]; exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))]
      exact (hP1 i hi).2⟩
  have hD : ∀ s < cols, LoadHolds rdF BD s (D s) := fun s hs ↦
    ⟨(hD1 s hs).1, by
      rw [hA _ (by rw [hAs]; exact List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩))]
      exact (hD1 s hs).2⟩
  have hfl : flat.length = S := lrWords_flatten_length D cols M p q
  have hcell : ∀ t < S, rdF (addressOfIndex (fpF + fs name + t)) = some (flat.getD t 0) :=
    fun t ht ↦ by rw [haddr, hW t ht]
  have hlenCH : (lrCH D cols M p q).length = q / resBatch + 1 := by simp [lrCH]
  have hbuf : MemL rdF (lrBufL fs name q cols D M p fpF) := by
    rw [lrBufL_eq]
    split
    · next h0 =>
      have hf0 : flat = lrCH D cols M p q := by simp [hflat, lrWords, h0]
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      intro k hk
      refine ⟨ofK_isInK _, ?_⟩
      have hk' : k < S := by rw [← hfl, hf0]; exact hk
      rw [Main.addr_ofK, hcell k hk', hf0, List.getD_eq_getElem _ _ hk]
    · next h0 =>
      have hf0 : flat = lrCH D cols M p q ++ lrRS D cols M p q := by simp [hflat, lrWords, h0]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · intro k hk
        refine ⟨ofK_isInK _, ?_⟩
        have hk' : k < S := by rw [← hfl, hf0, List.length_append]; simp only at hk; omega
        rw [Main.addr_ofK, hcell k hk', hf0, List.getD_eq_getElem _ _ (by simp only at hk ⊢; rw [List.length_append]; omega),
          List.getElem_append_left hk]
      · intro k hk
        refine ⟨ofK_isInK _, ?_⟩
        simp only at hk
        have hk' : q / resBatch + 1 + k < S := by rw [← hfl, hf0, List.length_append, hlenCH]; omega
        rw [Main.addr_ofK, show fpF + fs name + (q / resBatch + 1) + k =
          fpF + fs name + (q / resBatch + 1 + k) by ring, hcell _ hk', hf0,
          List.getD_eq_getElem _ _ (by rw [List.length_append, hlenCH]; omega)]
        rw [List.getElem_append_right (by rw [hlenCH]; omega)]
        simp [hlenCH]
  obtain ⟨m1, hm1⟩ := guarded_relAtIn (lrLoop1_pureIn hl1 hrb) List.mem_cons_self fs cert
    (rd := rdF) (Rk := Rk) hsuppK (lr_loop1_rel hl1 hrb hn hq8 hP hD hbuf) (fpF + fs name + S)
  obtain ⟨m2, hm2a, hm2b⟩ : ∃ m2, (q % resBatch = 0 → m2 = 0) ∧ (q % resBatch ≠ 0 →
      if 1 + gen ^ (q % resBatch) ≠ 0 then
        RelAtIn coreProgram fs cert rdF Rk (fun _ ↦ False) (fpF + fs name + S + m1) m2 loop2
          [1, gen ^ (q % resBatch), ofK (addressOfIndex (fpF + fs name + (q / resBatch + 1))),
            P * gen ^ (resBatch * (q / resBatch)), BD, M] []
      else m2 = fs loop2) := by
    by_cases h0 : q % resBatch = 0
    · exact ⟨0, fun _ ↦ rfl, fun h ↦ absurd h0 h⟩
    · obtain ⟨m2, hm2⟩ := guarded_relAtIn (lrLoop2_pureIn (hl2 h0)) (List.mem_singleton_self _) fs
        cert (rd := rdF) (Rk := Rk) hsuppK (lr_loop2_rel (hl2 h0) hn h0 hP hD hbuf)
        (fpF + fs name + S + m1)
      exact ⟨m2, fun h ↦ absurd h h0, fun _ ↦ hm2⟩
  obtain ⟨t, hname, hv, hbo, -, htot, -⟩ := lr_relAtIn hlr hq fs cert (R := Rw) (Rk := Rk)
    (fp := fpF) hbuf hm1 hm2b hm2a (fun i hi ↦ hi)
  have := hB rdF t _ _ hname hv hbo
  rw [htot] at this
  exact le_trans (Nat.le_add_right _ _) this

end
end LeanVM.Guest.B1
