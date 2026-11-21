/-
  LeanVM.Guest.B1.Gkr.VbgMem

  A memory holding `verify_bus_gkr`'s buffers whole holds its runs (`vbgLay`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgBuf

/-!
# The runs inside the whole buffers

`vbg_memLay`: on a memory holding the tables, `layers`, the round records, the point rows and the
values whole (`kmnWords`, `vbgBndW`, `vbgOddW`, `vbgRlenW`, `vbgLayersW`, `vbgRoundsW`,
`vbgRowsW`, `vbgValsW`) at `g^eK`, `g^eB`, `g^eO`, `g^eN`, `g^eL`, `g^eR`, `g^eP`, `g^eV`, every
run of `vbgLay` holds: a slot is record `i` of `layers`, a point row row `t`'s block's prefix, the
loop's step `j`'s records the run at record `gkPos sh (j + 1 - sh)`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value LeanVM.Guest.B1
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

/-- **The loop's records' positions**: the loop's step `j` (layer index `j + 1 - sh`) starts past
the steps before it. -/
theorem gkPos_loop {sh : ℕ} (hsh : sh < 2) : ∀ j,
    gkPos sh (j + 1 - sh) = ((List.range j).map fun i ↦ 2 * (i + 1 - sh) + sh + 1).sum
  | 0 => by interval_cases sh <;> rfl
  | j + 1 => by
    rw [show j + 1 + 1 - sh = (j + 1 - sh) + 1 by omega,
      gkPos_succ (sh := sh) (j := j + 1 - sh) (by omega), gkPos_loop hsh j,
      List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem gkSlotWords_length {s : Fs} {cur : E} {st : GkrState} {row pos half par : E}
    (hcl : s.cap.length = 5) (hvl : st.values.length = 3) :
    (gkSlotWords s cur st row pos half par).length = 13 := by
  simp [gkSlotWords, hcl, hvl]

section
variable {depth : ℕ} {cap0 xs : List E} {cur : E} {eL eR eP eK eB eO eN eV : ℕ}

theorem vbgSlotW_length (hcl : cap0.length = 5) (k : ℕ) :
    (vbgSlotW depth cap0 xs cur eP k).length = 13 :=
  gkSlotWords_length (gkSl_inv (xs := xs) (sh := depth % 2) hcl k).1
    (gkSl_inv (xs := xs) (sh := depth % 2) hcl k).2.1

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

theorem flatMap_const_length {f : ℕ → List E} {m w : ℕ} (hw : ∀ c < m, (f c).length = w) :
    ((List.range m).flatMap f).length = m * w := by
  rw [List.length_flatMap]
  have : (List.range m).map (fun c ↦ (f c).length) = List.replicate m w := by
    apply List.ext_getElem (by simp)
    intro i h1 _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hw i (by simp at h1; omega)
  rw [this, List.sum_replicate, smul_eq_mul]

theorem vbgLayersW_length (hcl : cap0.length = 5) :
    (vbgLayersW depth cap0 xs cur eP).length = 13 * ((depth - 1) / 2 + 1) := by
  unfold vbgLayersW
  rw [flatMap_const_length (fun c _ ↦ vbgSlotW_length hcl _), Nat.mul_comm]

theorem vbgRowsW_length (hd : depth ≤ 32)
    (hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2) :
    (vbgRowsW depth cap0 xs).length = 40 * ((depth - 1) / 2 + 2) := by
  unfold vbgRowsW
  rw [flatMap_const_length (fun c _ ↦ vbgRowBlock_length hd hpl c), Nat.mul_comm]

/-- The loop's steps' records before step `j`, as words. -/
theorem vbgRecRuns_length (j : ℕ) :
    ((List.range j).map fun i ↦ (vbgRecRun depth cap0 xs cur i).length).sum =
      7 * gkPos (depth % 2) (j + 1 - depth % 2) := by
  rw [gkPos_loop (sh := depth % 2) (by omega), ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [vbgRecRun]

theorem vbgRoundsW_length (hd1 : 1 ≤ depth) :
    (vbgRoundsW depth cap0 xs cur).length = 7 * vbgRecs depth := by
  unfold vbgRoundsW
  rw [List.length_flatMap, vbgRecRuns_length,
    show (depth - 1) / 2 + 1 - depth % 2 = depth / 2 by omega, gkPos_last hd1]

/-- **A memory holding the whole buffers holds the runs.** -/
theorem vbg_memLay {rd : Reader} (hd : depth ≤ 32) (hcl : cap0.length = 5)
    (hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2)
    (hL : TbReadsAt rd (ofK (addressOfIndex eL)) (vbgLayersW depth cap0 xs cur eP))
    (hR : TbReadsAt rd (ofK (addressOfIndex eR)) (vbgRoundsW depth cap0 xs cur))
    (hP : TbReadsAt rd (ofK (addressOfIndex eP)) (vbgRowsW depth cap0 xs))
    (hK : TbReadsAt rd (ofK (addressOfIndex eK)) kmnWords)
    (hB : TbReadsAt rd (ofK (addressOfIndex eB)) vbgBndW)
    (hO : TbReadsAt rd (ofK (addressOfIndex eO)) vbgOddW)
    (hN : TbReadsAt rd (ofK (addressOfIndex eN)) vbgRlenW)
    (hV : TbReadsAt rd (ofK (addressOfIndex eV)) (vbgValsW depth cap0 xs)) :
    MemLay rd (vbgLay depth cap0 xs cur eL eR eP eK eB eO eN eV) := by
  unfold vbgLayersW at hL
  unfold vbgRowsW at hP
  unfold vbgRoundsW at hR
  have hLb := tbReadsAt_flatMap_eq (w := 13) _ ((depth - 1) / 2 + 1)
    (fun c _ ↦ vbgSlotW_length hcl _) hL
  have hPb := tbReadsAt_flatMap_eq (w := 40) _ ((depth - 1) / 2 + 2)
    (fun c _ ↦ vbgRowBlock_length hd hpl c) hP
  unfold vbgLay
  rw [memLay_append, memLay_append, memLay_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the slots
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    have hi' : i < depth / 2 + depth % 2 := by simpa using hi
    have := hLb i (by omega)
    rw [tb_ofK_gpow_mul] at this
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
    simp only [gkRecRuns, List.mem_singleton] at hq2
    subst hq2
    have hr := tbReadsAt_flatMap_range _ _ hR j (by simpa using hj)
    rw [vbgRecRuns_length, tb_ofK_gpow_mul] at hr
    exact hr
  · -- the tables and the values
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hB
    · exact hO
    · exact hN
    · exact hK
    · exact hV

end

end
end LeanVM.Guest.B1.Tables
