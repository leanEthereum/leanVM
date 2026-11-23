/-
  LeanVM.Guest.B1.Gkr.VbgMem

  A memory holding `verify_bus_gkr`'s buffers whole holds its runs (`vbgLay`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgBuf

/-!
# The runs inside the whole buffers

`vbg_memLay`: on a memory holding `layers`, the round records, the point rows, the three tables,
the values and `gkr_sizes` whole (`vbgLayersW`, `vbgRoundsW`, `vbgRowsW`, `vbgOddW`, `vbgBndW`,
`vbgRemW`, `vbgValsW`, `vbgSizesW`) at `g^eL`, `g^eR`, `g^eP`, `g^eO`, `g^eB`, `g^eM`, `g^eV`,
`g^eS`, every run of `vbgLay` holds: a slot is level `l`'s block of `layers`, a point row row `t`'s
block's prefix, radix-four layer `j`'s record `y` the seven words from record
`gkPos sh (j + 1 - sh) + y`.
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

/-- **The layers' records' positions**: layer `j`'s (layer index `j + 1 - sh`) start past the
first word and the layers before it, layer `i` with `i / 4 + 1` records. -/
theorem gkPos_loop {sh : ℕ} (hsh : sh < 2) : ∀ j,
    gkPos sh (j + 1 - sh) = 1 + ((List.range j).map fun i ↦ i / 4 + 1).sum
  | 0 => by interval_cases sh <;> rfl
  | j + 1 => by
    rw [show j + 1 + 1 - sh = (j + 1 - sh) + 1 by omega, gkPos, gkPos_loop hsh j, List.range_succ,
      List.map_append, show j + 1 - sh + sh - 1 = j by omega, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem gkSlotWords_length {s : Fs} {cur : E} {st : GkrState} {pos : E}
    (hcl : s.cap.length = 5) (hvl : st.values.length = 3) :
    (gkSlotWords s cur st pos).length = 10 := by
  simp [gkSlotWords, hcl, hvl]

section
variable {depth : ℕ} {cap0 xs : List E} {cur : E} {eL eR eP eO eB eM eV eS : ℕ}

theorem vbgLayBlock_length (hcl : cap0.length = 5) (l : ℕ) :
    (vbgLayBlock depth cap0 xs cur l).length = 10 := by
  have inv := gkSl_inv (xs := xs) (sh := depth % 2) hcl
  unfold vbgLayBlock
  split
  · exact gkSlotWords_length (inv _).1 (inv _).2.1
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

theorem vbgRecRun_length (j : ℕ) : (vbgRecRun depth cap0 xs cur j).length = 7 * (j / 4 + 1) := by
  rw [vbgRecRun, List.length_flatMap]
  simp [Nat.mul_comm]

theorem vbgRecs_length :
    (vbgRecs depth cap0 xs cur).length = 7 * ((List.range ((depth - 1) / 2)).map fun i ↦ i / 4 + 1).sum := by
  rw [vbgRecs, List.length_flatMap, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro i _
  exact vbgRecRun_length i

theorem vbgRecs_le (hd : depth ≤ 32) :
    1 + ((List.range ((depth - 1) / 2)).map fun i ↦ i / 4 + 1).sum ≤ gkRecCount depth := by
  have : ∀ d ≤ 32, 1 + ((List.range ((d - 1) / 2)).map fun i ↦ i / 4 + 1).sum ≤ gkRecCount d := by
    decide
  exact this _ hd

theorem vbgRoundsW_length (hd : depth ≤ 32) :
    (vbgRoundsW depth cap0 xs cur).length = 7 * gkRecCount depth := by
  have h1 := vbgRecs_length (cap0 := cap0) (xs := xs) (cur := cur) (depth := depth)
  have h2 := vbgRecs_le (depth := depth) hd
  simp only [vbgRoundsW, List.length_append, List.length_replicate, h1]
  omega

theorem vbgRowsW_length (hd : depth ≤ 32)
    (hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2) :
    (vbgRowsW depth cap0 xs).length = (depth / 2 + 2) * 40 := by
  rw [vbgRowsW, List.length_flatMap]
  simp [vbgRowBlock_length hd hpl]

/-- **A memory holding the whole buffers holds the runs.** -/
theorem vbg_memLay {rd : Reader} (hd : depth ≤ 32) (hcl : cap0.length = 5)
    (hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2)
    (hL : TbReadsAt rd (ofK (addressOfIndex eL)) (vbgLayersW depth cap0 xs cur))
    (hR : TbReadsAt rd (ofK (addressOfIndex eR)) (vbgRoundsW depth cap0 xs cur))
    (hP : TbReadsAt rd (ofK (addressOfIndex eP)) (vbgRowsW depth cap0 xs))
    (hO : TbReadsAt rd (ofK (addressOfIndex eO)) vbgOddW)
    (hB : TbReadsAt rd (ofK (addressOfIndex eB)) vbgBndW)
    (hM : TbReadsAt rd (ofK (addressOfIndex eM)) vbgRemW)
    (hV : TbReadsAt rd (ofK (addressOfIndex eV)) (vbgValsW depth cap0 xs))
    (hS : TbReadsAt rd (ofK (addressOfIndex eS)) vbgSizesW) :
    MemLay rd (vbgLay depth cap0 xs cur eL eR eP eO eB eM eV eS) := by
  have hLb := tbReadsAt_flatMap_eq (w := 10) _ (depth + 2)
    (fun c _ ↦ vbgLayBlock_length hcl c) hL
  have hPb := tbReadsAt_flatMap_eq (w := 40) _ (depth / 2 + 2)
    (fun c _ ↦ vbgRowBlock_length hd hpl c) hP
  have hmid := (tbReadsAt_append.mp (tbReadsAt_append.mp hR).1).2
  simp only [List.length_replicate, tb_ofK_gpow_mul] at hmid
  unfold vbgLay
  rw [memLay_append, memLay_append, memLay_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the slots
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    have hi' : i < depth / 2 + depth % 2 := by simpa using hi
    have := hLb (2 * (i + 1 - depth % 2) + depth % 2) (by omega)
    rw [tb_ofK_gpow_mul] at this
    unfold vbgLayBlock at this
    have hc : (2 * (i + 1 - depth % 2) + depth % 2) % 2 = depth % 2 ∧
        1 ≤ 2 * (i + 1 - depth % 2) + depth % 2 ∧ 2 * (i + 1 - depth % 2) + depth % 2 ≤ depth :=
      ⟨by omega, by omega, by omega⟩
    simp only [hc, and_self, ↓reduceIte,
      show (2 * (i + 1 - depth % 2) + depth % 2 - depth % 2) / 2 = i + 1 - depth % 2 by omega]
      at this
    exact this
  · -- the point rows
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    have hi' : i < depth / 2 + depth % 2 := by simpa using hi
    have := hPb (i + 1 - depth % 2 + depth % 2) (by omega)
    rw [tb_ofK_gpow_mul] at this
    unfold vbgRowBlock at this
    rw [show i + 1 - depth % 2 + depth % 2 - depth % 2 = i + 1 - depth % 2 by omega] at this
    simp only [Nat.le_add_left, show i + 1 - depth % 2 ≤ depth / 2 by omega, and_self,
      ↓reduceIte] at this
    rw [tbReadsAt_append] at this
    exact this.1
  · -- the round records
    intro q hq
    obtain ⟨_, hq1, hq2⟩ := List.mem_flatten.mp hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq1
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq2
    simp only [List.mem_range] at hj hy
    rw [show j + 1 - depth % 2 + depth % 2 - 1 = j by omega] at hy
    have hr := tbReadsAt_flatMap_range _ _ hmid j hj
    have e : ((List.range j).map fun i ↦ (vbgRecRun depth cap0 xs cur i).length).sum =
        7 * ((List.range j).map fun i ↦ i / 4 + 1).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro i _
      exact vbgRecRun_length i
    rw [e, tb_ofK_gpow_mul] at hr
    have hb := tbReadsAt_flatMap_eq (w := 7) _ (j / 4 + 1) (fun _ _ ↦ by simp) hr y hy
    rw [tb_ofK_gpow_mul] at hb
    show TbReadsAt rd (ofK (addressOfIndex (eR + 7 * (gkPos (depth % 2) (j + 1 - depth % 2) + y))))
      _
    rw [gkPos_loop (by omega),
      show eR + 7 * (1 + ((List.range j).map fun i ↦ i / 4 + 1).sum + y) =
        eR + 7 + 7 * ((List.range j).map fun i ↦ i / 4 + 1).sum + 7 * y by ring]
    exact hb
  · -- the tables and the values
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hO
    · exact hB
    · exact hM
    · exact hV
    · exact hS

end

end
end LeanVM.Guest.B1.Tables
