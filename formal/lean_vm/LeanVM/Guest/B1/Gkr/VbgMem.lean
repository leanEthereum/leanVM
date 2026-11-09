/-
  LeanVM.Guest.B1.Gkr.VbgMem

  A memory holding `verify_bus_gkr`'s buffers whole holds its runs (`vbgLay`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgBuf

/-!
# The runs inside the whole buffers

`vbg_memLay`: on a memory holding `layers`, the round records, the point rows and the two tables
whole (`vbgLayersW`, `vbgRoundsW`, `vbgRowsW`, `vbgPairsW`, `vbgDshW`) at `g^eL`, `g^eR`, `g^eP`,
`g^ePa`, `g^eD`, every run of `vbgLay` holds: a slot is level `l`'s block of `layers`, a point row
row `t`'s block's prefix, step `j`'s records of field `f` the run at `gkPos j` of field `f`'s
block.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A block of a run of variable-width blocks, at the sum of the widths before it. -/
theorem tbReadsAt_flatMap_range {rd : Reader} {p : E} (g : ℕ → List E) :
    ∀ m, TbReadsAt rd p ((List.range m).flatMap g) →
      ∀ j < m, TbReadsAt rd (p * gen ^ ((List.range j).map fun i ↦ (g i).length).sum) (g j)
  | 0, _, j, hj => absurd hj (by omega)
  | m + 1, h, j, hj => by
    rw [List.range_succ, List.flatMap_append, tbReadsAt_append] at h
    rcases Nat.lt_or_ge j m with hjm | hjm
    · exact tbReadsAt_flatMap_range g m h.1 j hjm
    · obtain rfl : j = m := by omega
      have e : ((List.range j).flatMap g).length = ((List.range j).map fun i ↦ (g i).length).sum := by
        rw [List.length_flatMap]
      simpa [e] using h.2

/-- A block of a run of equal-width blocks. -/
theorem tbReadsAt_flatMap_eq {rd : Reader} {p : E} {w : ℕ} (g : ℕ → List E) (m : ℕ)
    (hw : ∀ c < m, (g c).length = w) (h : TbReadsAt rd p ((List.range m).flatMap g)) :
    ∀ j < m, TbReadsAt rd (p * gen ^ (w * j)) (g j) := by
  intro j hj
  have := tbReadsAt_flatMap_range g m h j hj
  have e : ((List.range j).map fun i ↦ (g i).length).sum = w * j := by
    have : (List.range j).map (fun i ↦ (g i).length) = List.replicate j w := by
      apply List.ext_getElem (by simp)
      intro i h1 _
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact hw i (by simp at h1; omega)
    rw [this, List.sum_replicate, smul_eq_mul, mul_comm]
  rwa [e] at this

theorem gkPos_eq (sh : ℕ) : ∀ j, gkPos sh j = sh + ((List.range j).map fun i ↦ 2 * i + sh + 1).sum
  | 0 => by simp [gkPos]
  | j + 1 => by
    rw [gkPos, gkPos_eq sh j, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

theorem gkSlotWords_length {s : Fs} {cur : E} {st : GkrState} {row pos half par : E}
    (hcl : s.cap.length = 5) (hvl : st.values.length = 3) :
    (gkSlotWords s cur st row pos half par).length = 17 := by
  simp [gkSlotWords, hcl, hvl, rateOf]

section
variable {depth : ℕ} {cap0 xs : List E} {cur : E} {eL eR eP eK ePa eD : ℕ}

theorem vbgLayBlock_length (hcl : cap0.length = 5) (hcan : AllCanonical cap0) (l : ℕ) :
    (vbgLayBlock depth cap0 xs cur eP l).length = 17 := by
  have inv := gkSl_inv (xs := xs) (sh := depth % 2) hcl hcan
  unfold vbgLayBlock
  split
  · exact gkSlotWords_length (inv _).1 (inv _).2.2.2
  · split
    · exact gkSlotWords_length hcl (by simp [gkRootSt])
    · simp

theorem vbgRowBlock_length (hd : depth ≤ 32)
    (hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2)
    (t : ℕ) : (vbgRowBlock depth cap0 xs t).length = 40 := by
  unfold vbgRowBlock
  split
  · rename_i h
    have := hpl (t - depth % 2) h.2
    simp only [List.length_append, List.length_replicate]
    omega
  · simp

theorem vbgRecRuns_length (f : ℕ) :
    ((List.range (depth / 2)).flatMap (vbgRecRun depth cap0 xs cur f)).length =
      ((List.range (depth / 2)).map fun i ↦ 2 * i + depth % 2 + 1).sum := by
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [vbgRecRun]

theorem vbgRecRuns_le (hd : depth ≤ 32) :
    depth % 2 + ((List.range (depth / 2)).map fun i ↦ 2 * i + depth % 2 + 1).sum ≤ 862 := by
  have : ∀ m ≤ 16, ∀ s ≤ 1, s + ((List.range m).map fun i ↦ 2 * i + s + 1).sum ≤ 862 := by
    decide
  exact this _ (by omega) _ (by omega)

theorem vbgRecBlock_length (hd : depth ≤ 32) (f : ℕ) :
    (vbgRecBlock depth cap0 xs cur f).length = 862 := by
  have h1 := vbgRecRuns_length (cap0 := cap0) (xs := xs) (cur := cur) (depth := depth) f
  have h2 := vbgRecRuns_le hd
  simp only [vbgRecBlock, List.length_append, List.length_replicate, h1]
  omega

/-- **A memory holding the whole buffers holds the runs.** -/
theorem vbg_memLay {rd : Reader} (hd : depth ≤ 32) (hcl : cap0.length = 5)
    (hcan : AllCanonical cap0)
    (hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2)
    (hL : TbReadsAt rd (ofK (addressOfIndex eL)) (vbgLayersW depth cap0 xs cur eP))
    (hR : TbReadsAt rd (ofK (addressOfIndex eR)) (vbgRoundsW depth cap0 xs cur))
    (hP : TbReadsAt rd (ofK (addressOfIndex eP)) (vbgRowsW depth cap0 xs))
    (hK : TbReadsAt rd (ofK (addressOfIndex eK)) kmnWords)
    (hPa : TbReadsAt rd (ofK (addressOfIndex ePa)) vbgPairsW) (hD : TbReadsAt rd (ofK
        (addressOfIndex eD)) vbgDshW) :
    MemLay rd (vbgLay depth cap0 xs cur eL eR eP eK ePa eD) := by
  have hLb := tbReadsAt_flatMap_eq (w := 17) _ (depth + 2)
    (fun c _ ↦ vbgLayBlock_length hcl hcan c) hL
  have hPb := tbReadsAt_flatMap_eq (w := 40) _ 41 (fun c _ ↦ vbgRowBlock_length hd hpl c) hP
  have hRb := tbReadsAt_flatMap_eq (w := 862) _ 7 (fun c _ ↦ vbgRecBlock_length hd c) hR
  unfold vbgLay
  rw [memLay_append, memLay_append, memLay_append, memLay_append]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- the root slot at an odd depth
    split
    · rename_i hodd
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      have := hLb 0 (by omega)
      simp only [Nat.mul_zero, pow_zero, mul_one] at this
      unfold vbgLayBlock at this
      have hc : ¬(0 % 2 = depth % 2 ∧ 0 ≤ depth) := by omega
      simp only [hc, ↓reduceIte] at this
      exact this
    · intro q hq; simp at hq
  · -- the slots
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    have hj' : j ≤ depth / 2 := by simp at hj; omega
    have := hLb (2 * j + depth % 2) (by omega)
    rw [tb_ofK_gpow_mul] at this
    unfold vbgLayBlock at this
    have hc : (2 * j + depth % 2) % 2 = depth % 2 ∧ 2 * j + depth % 2 ≤ depth := ⟨by omega, by omega⟩
    simp only [hc, and_self, ↓reduceIte, show (2 * j + depth % 2 - depth % 2) / 2 = j by omega]
      at this
    exact this
  · -- the point rows
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    have hj' : j ≤ depth / 2 := by simp at hj; omega
    have := hPb (j + depth % 2) (by omega)
    rw [tb_ofK_gpow_mul] at this
    unfold vbgRowBlock at this
    rw [show j + depth % 2 - depth % 2 = j by omega] at this
    simp only [Nat.le_add_left, hj', and_self, ↓reduceIte] at this
    rw [tbReadsAt_append] at this
    exact this.1
  · -- the round records
    intro q hq
    obtain ⟨_, hq1, hq2⟩ := List.mem_flatten.mp hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq1
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq2
    simp only [List.mem_range] at hj hf
    have hb := hRb f hf
    rw [tb_ofK_gpow_mul] at hb
    unfold vbgRecBlock at hb
    rw [tbReadsAt_append, tbReadsAt_append] at hb
    have hr := tbReadsAt_flatMap_range _ _ hb.1.2 j hj
    simp only [List.length_replicate, tb_ofK_gpow_mul] at hr
    have e : ((List.range j).map fun i ↦ (vbgRecRun depth cap0 xs cur f i).length).sum =
        ((List.range j).map fun i ↦ 2 * i + depth % 2 + 1).sum := by
      congr 1; apply List.map_congr_left; intro i _; simp [vbgRecRun]
    rw [e] at hr
    show TbReadsAt rd (ofK (addressOfIndex (eR + 862 * f + gkPos (depth % 2) j))) _
    rw [gkPos_eq, ← Nat.add_assoc]
    exact hr
  · -- the tables
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hPa
    · exact hD
    · exact hK

end

end
end LeanVM.Guest.B1.Tables
