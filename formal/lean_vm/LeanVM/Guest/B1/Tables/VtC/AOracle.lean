/-
  LeanVM.Guest.B1.Tables.VtC.AOracle

  `verify_tables`' honest oracle, explicitly: a table of the values it answers.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ADefs

/-!
# The honest oracle

`vtWKeys`: the 331 values the oracle answers (the allocations, the padding weights' returns,
`plus_one_run`'s, the bytecode value, `g^n`, the index MLEs, the selectors' returns), each at its position (`vtWKeys_alloc` …, by the kernel). `vtWVals H B`: their honest words, aligned. `vtW H B`: the
oracle, the word of a value's position in the table. `vtW_ok`: it answers `VtWOk`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel)

@[expose] public section

/-- The push side's selector return values. -/
def vtSelKP (i : ℕ) : ℕ := vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1

/-- The count side's selector return values. -/
def vtSelKC (i : ℕ) : ℕ :=
  vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1

/-- **The values the oracle answers.** -/
def vtWKeys : List ℕ :=
  vtAllocVars ++ ((List.range 6).flatMap fun t ↦ [vtPadV t, vtPadV t + 1, vtPadV t + 2]) ++
    [700, 2544, 809, 837] ++
    ((List.range 3).flatMap fun b ↦ [vtFwW b + 10, vtFwW b + 11]) ++
    ((List.range 51).flatMap fun i ↦ [vtSelKP i, vtSelKP i + 1]) ++
    ((List.range 45).flatMap fun i ↦ [vtSelKC i, vtSelKC i + 1]) ++
    (List.range 24).map (1876 + ·)

/-- The first tail round's returns: its capacity, cursor, claim and challenge. -/
noncomputable def vtTail1 (H : VtHonest) (B : VtBases) : List E :=
  (vtBcR1 (vtF0 (H.args B) H.xs4) H.bcW).1 ++
    [(H.args B).getD 5 0 * gen ^ 7 * gen ^ 2, (vtBcR1 (vtF0 (H.args B) H.xs4) H.bcW).2.1,
      (vtBcR1 (vtF0 (H.args B) H.xs4) H.bcW).2.2]

/-- The second's. -/
noncomputable def vtTail2 (H : VtHonest) (B : VtBases) : List E :=
  (vtBcR2 (vtF0 (H.args B) H.xs4) H.bcW).1 ++
    [(H.args B).getD 5 0 * gen ^ 7 * gen ^ 2 * gen ^ 2, (vtBcR2 (vtF0 (H.args B) H.xs4) H.bcW).2.1,
      (vtBcR2 (vtF0 (H.args B) H.xs4) H.bcW).2.2]

/-- The third's. -/
noncomputable def vtTail3 (H : VtHonest) (B : VtBases) : List E :=
  (vtBcR3 (vtF0 (H.args B) H.xs4) H.bcW).1 ++
    [(H.args B).getD 5 0 * gen ^ 7 * gen ^ 2 * gen ^ 2 * gen ^ 2,
      (vtBcR3 (vtF0 (H.args B) H.xs4) H.bcW).2.1, (vtBcR3 (vtF0 (H.args B) H.xs4) H.bcW).2.2]

/-- The tail rounds' returns. -/
noncomputable def vtTailW (H : VtHonest) (B : VtBases) : List E :=
  vtTail1 H B ++ (vtTail2 H B ++ vtTail3 H B)

/-- **Their honest words.** -/
noncomputable def vtWVals (H : VtHonest) (B : VtBases) : List E :=
  (H.ownB B).map (fun b ↦ ofK (addressOfIndex b)) ++
    ((List.range 6).flatMap fun t ↦ [paddingWeight (H.point.take (H.τ t)) (vtRw H.rows t),
      PadLead (H.τ t) (vtRw H.rows t), PadRest (H.τ t) (vtRw H.rows t)]) ++
    [0, gen ^ H.n, indexMle (H.point.take H.lm), indexMle (H.point.take 19)] ++
    ((List.range 3).flatMap fun b ↦ [blockSel (vtSizesP H.lm H.τ) H.μ b H.point,
      gen ^ H.offP.getD b 0]) ++
    ((List.range 51).flatMap fun i ↦ [blockSel (vtSizesP H.lm H.τ) H.μ (3 + i) H.point,
      gen ^ H.offP.getD (3 + i) 0]) ++
    ((List.range 45).flatMap fun i ↦ [blockSel (vtSizesC H.τ) H.μ i H.point,
      gen ^ H.offC.getD i 0]) ++ vtTailW H B

/-- **The honest oracle.** -/
noncomputable def vtW (H : VtHonest) (B : VtBases) (i : ℕ) : E :=
  (vtWVals H B).getD (vtWKeys.idxOf i) 0

theorem getD_flatMap_const' {α : Type} {S : ℕ} (d : α) (f : ℕ → List α)
    (hf : ∀ i, (f i).length = S) :
    ∀ (m i k : ℕ), i < m → k < S →
      ((List.range m).flatMap f).getD (S * i + k) d = (f i).getD k d
  | 0, _, _, hi, _ => absurd hi (by omega)
  | m + 1, i, k, hi, hk => by
    rw [List.range_succ, List.flatMap_append]
    have hlen : ((List.range m).flatMap f).length = S * m := by
      rw [List.length_flatMap]
      simp [hf, List.sum_replicate, Nat.mul_comm]
    rcases Nat.lt_or_ge i m with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact getD_flatMap_const' d f hf m i k h hk
    · obtain rfl : i = m := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp

section
variable (H : VtHonest) (B : VtBases)

theorem vtWVals_split :
    vtWVals H B = (H.ownB B).map (fun b ↦ ofK (addressOfIndex b)) ++
      (((List.range 6).flatMap fun t ↦ [paddingWeight (H.point.take (H.τ t)) (vtRw H.rows t),
      PadLead (H.τ t) (vtRw H.rows t), PadRest (H.τ t) (vtRw H.rows t)]) ++
      ([0, gen ^ H.n, indexMle (H.point.take H.lm), indexMle (H.point.take 19)] ++
      (((List.range 3).flatMap fun b ↦ [blockSel (vtSizesP H.lm H.τ) H.μ b H.point,
      gen ^ H.offP.getD b 0]) ++
      (((List.range 51).flatMap fun i ↦ [blockSel (vtSizesP H.lm H.τ) H.μ (3 + i) H.point,
      gen ^ H.offP.getD (3 + i) 0]) ++
      (((List.range 45).flatMap fun i ↦ [blockSel (vtSizesC H.τ) H.μ i H.point,
      gen ^ H.offC.getD i 0]) ++ vtTailW H B))))) := by
  simp only [vtWVals, List.append_assoc]

theorem ownB_map_length : ((H.ownB B).map (fun b ↦ ofK (addressOfIndex b))).length = 111 := by
  simp [VtHonest.ownB, VtHonest.sizes, LeanVM.Guest.Memory.length_bases]

set_option maxRecDepth 100000 in
theorem vtWKeys_alloc : ∀ j < 111, vtWKeys.idxOf (vtAllocVars.getD j 0) = j := by decide +kernel

theorem vtW_alloc {j : ℕ} (hj : j < 111) :
    vtW H B (vtAllocVars.getD j 0) = ofK (addressOfIndex ((H.ownB B).getD j 0)) := by
  rw [vtW, vtWKeys_alloc j hj, vtWVals_split, List.getD_append _ _ _ _
    (by rw [ownB_map_length]; exact hj), List.getD_eq_getElem _ _ (by rw [ownB_map_length]; exact hj),
    List.getD_eq_getElem _ _ (by
      simp [VtHonest.ownB, VtHonest.sizes, LeanVM.Guest.Memory.length_bases]; omega)]
  simp

theorem getD_append_len {α : Type} {A rest : List α} {n k : ℕ} {d : α} (h : A.length = n) :
    (A ++ rest).getD (n + k) d = rest.getD k d := by
  rw [List.getD_append_right _ _ _ _ (by omega), h, Nat.add_sub_cancel_left]

theorem flatMap_len {α : Type} {S : ℕ} (m : ℕ) (f : ℕ → List α) (hf : ∀ i, (f i).length = S) :
    ((List.range m).flatMap f).length = S * m := by
  rw [List.length_flatMap]; simp [hf, List.sum_replicate, Nat.mul_comm]

set_option maxRecDepth 100000 in
theorem vtWKeys_pads : ∀ t < 6, vtWKeys.idxOf (vtPadV t) = 111 + 3 * t ∧
    vtWKeys.idxOf (vtPadV t + 1) = 111 + (3 * t + 1) ∧
    vtWKeys.idxOf (vtPadV t + 2) = 111 + (3 * t + 2) := by decide +kernel
set_option maxRecDepth 100000 in
theorem vtWKeys_misc : vtWKeys.idxOf 700 = 129 ∧ vtWKeys.idxOf 2544 = 130 ∧
    vtWKeys.idxOf 809 = 131 ∧ vtWKeys.idxOf 837 = 132 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem vtWKeys_fw : ∀ b < 3, vtWKeys.idxOf (vtFwW b + 10) = 133 + 2 * b ∧
    vtWKeys.idxOf (vtFwW b + 11) = 133 + (2 * b + 1) := by decide +kernel
set_option maxRecDepth 100000 in
theorem vtWKeys_push : ∀ i < 51,
    vtWKeys.idxOf (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1) =
      139 + 2 * i ∧
    vtWKeys.idxOf (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1 + 1) =
      139 + (2 * i + 1) := by decide +kernel
set_option maxRecDepth 100000 in
theorem vtWKeys_count : ∀ i < 45,
    vtWKeys.idxOf (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1) =
      241 + 2 * i ∧
    vtWKeys.idxOf (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1 + 1) =
      241 + (2 * i + 1) := by decide +kernel

theorem vtWVals_pads {t c j : ℕ} (ht : t < 6) (hc : c < 3) (hj : j = 111 + (3 * t + c)) :
    (vtWVals H B).getD j 0 =
      [paddingWeight (H.point.take (H.τ t)) (vtRw H.rows t), PadLead (H.τ t) (vtRw H.rows t),
        PadRest (H.τ t) (vtRw H.rows t)].getD c 0 := by
  subst hj
  rw [vtWVals_split, getD_append_len (ownB_map_length H B),
    List.getD_append _ _ _ _ (by rw [flatMap_len (S := 3) _ _ (fun _ ↦ rfl)]; omega)]
  exact getD_flatMap_const' (S := 3) 0 _ (fun _ ↦ rfl) 6 t c ht hc

theorem vtWVals_misc {k j : ℕ} (hk : k < 4) (hj : j = 111 + (18 + k)) :
    (vtWVals H B).getD j 0 =
      [0, gen ^ H.n, indexMle (H.point.take H.lm), indexMle (H.point.take 19)].getD k 0 := by
  subst hj
  rw [vtWVals_split, getD_append_len (ownB_map_length H B),
    getD_append_len (flatMap_len (S := 3) _ _ (fun _ ↦ rfl)),
    List.getD_append _ _ _ _ (by simp; omega)]

theorem vtWVals_fw {b c j : ℕ} (hb : b < 3) (hc : c < 2) (hj : j = 111 + (18 + (4 + (2 * b + c)))) :
    (vtWVals H B).getD j 0 =
      [blockSel (vtSizesP H.lm H.τ) H.μ b H.point, gen ^ H.offP.getD b 0].getD c 0 := by
  subst hj
  rw [vtWVals_split, getD_append_len (ownB_map_length H B),
    getD_append_len (flatMap_len (S := 3) _ _ (fun _ ↦ rfl)), getD_append_len (by rfl),
    List.getD_append _ _ _ _ (by rw [flatMap_len (S := 2) _ _ (fun _ ↦ rfl)]; omega)]
  exact getD_flatMap_const' (S := 2) 0 _ (fun _ ↦ rfl) 3 b c hb hc

theorem vtWVals_push {i c j : ℕ} (hi : i < 51) (hc : c < 2)
    (hj : j = 111 + (18 + (4 + (6 + (2 * i + c))))) :
    (vtWVals H B).getD j 0 =
      [blockSel (vtSizesP H.lm H.τ) H.μ (3 + i) H.point, gen ^ H.offP.getD (3 + i) 0].getD c 0 := by
  subst hj
  rw [vtWVals_split, getD_append_len (ownB_map_length H B),
    getD_append_len (flatMap_len (S := 3) _ _ (fun _ ↦ rfl)), getD_append_len (by rfl),
    getD_append_len (flatMap_len (S := 2) _ _ (fun _ ↦ rfl)),
    List.getD_append _ _ _ _ (by rw [flatMap_len (S := 2) _ _ (fun _ ↦ rfl)]; omega)]
  exact getD_flatMap_const' (S := 2) 0 _ (fun _ ↦ rfl) 51 i c hi hc

theorem vtWVals_count {i c j : ℕ} (hi : i < 45) (hc : c < 2)
    (hj : j = 111 + (18 + (4 + (6 + (102 + (2 * i + c)))))) :
    (vtWVals H B).getD j 0 =
      [blockSel (vtSizesC H.τ) H.μ i H.point, gen ^ H.offC.getD i 0].getD c 0 := by
  subst hj
  rw [vtWVals_split, getD_append_len (ownB_map_length H B),
    getD_append_len (flatMap_len (S := 3) _ _ (fun _ ↦ rfl)), getD_append_len (by rfl),
    getD_append_len (flatMap_len (S := 2) _ _ (fun _ ↦ rfl)),
    getD_append_len (flatMap_len (S := 2) _ _ (fun _ ↦ rfl)),
    List.getD_append _ _ _ _ (by rw [flatMap_len (S := 2) _ _ (fun _ ↦ rfl)]; omega)]
  exact getD_flatMap_const' (S := 2) 0 _ (fun _ ↦ rfl) 45 i c hi hc

set_option maxRecDepth 100000 in
theorem vtWKeys_tail : ∀ i < 24, vtWKeys.idxOf (1876 + i) = 331 + i := by decide +kernel

theorem vtTail1_length : (vtTail1 H B).length = 8 := by
  simp [vtTail1, vtBcR1, bcRound, Fs.squeeze, capOf]

theorem vtTail2_length : (vtTail2 H B).length = 8 := by
  simp [vtTail2, vtBcR2, bcRound, Fs.squeeze, capOf]

theorem vtTail3_length : (vtTail3 H B).length = 8 := by
  simp [vtTail3, vtBcR3, bcRound, Fs.squeeze, capOf]

theorem vtTailW_length : (vtTailW H B).length = 24 := by
  simp [vtTailW, vtTail1_length, vtTail2_length, vtTail3_length]

theorem vtWVals_tail (i : ℕ) : (vtWVals H B).getD (331 + i) 0 = (vtTailW H B).getD i 0 := by
  rw [vtWVals_split, show 331 + i = 111 + (18 + (4 + (6 + (102 + (90 + i))))) by omega,
    getD_append_len (ownB_map_length H B),
    getD_append_len (flatMap_len (S := 3) _ _ (fun _ ↦ rfl)), getD_append_len (by rfl),
    getD_append_len (flatMap_len (S := 2) _ _ (fun _ ↦ rfl)),
    getD_append_len (flatMap_len (S := 2) _ _ (fun _ ↦ rfl)),
    getD_append_len (flatMap_len (S := 2) _ _ (fun _ ↦ rfl))]

theorem vtW_tail (k : ℕ) (hk : k + 8 ≤ 24) :
    (List.range 8).map (fun i ↦ vtW H B (1876 + k + i)) = ((vtTailW H B).drop k).take 8 := by
  apply List.ext_getElem (by simp [vtTailW_length]; omega)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, vtW, show 1876 + k + i = 1876 + (k + i) by omega,
    vtWKeys_tail _ (by omega), vtWVals_tail H B, List.getElem_take, List.getElem_drop,
    List.getD_eq_getElem _ _ (by rw [vtTailW_length]; omega)]

/-- **The honest oracle answers.** -/
theorem vtW_ok : VtWOk H B (vtW H B) where
  alloc j hj := vtW_alloc H B hj
  pads t ht := by
    obtain ⟨k0, k1, k2⟩ := vtWKeys_pads t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [vtW, k0, vtWVals_pads H B ht (c := 0) (by norm_num) (by omega)]; rfl
    · rw [vtW, k1, vtWVals_pads H B ht (c := 1) (by norm_num) (by omega)]; rfl
    · rw [vtW, k2, vtWVals_pads H B ht (c := 2) (by norm_num) (by omega)]; rfl
  w700 := by rw [vtW, vtWKeys_misc.1, vtWVals_misc H B (k := 0) (by norm_num) (by omega)]; rfl
  w2544 := by
    rw [vtW, vtWKeys_misc.2.1, vtWVals_misc H B (k := 1) (by norm_num) (by omega)]; rfl
  hwI := by
    refine ⟨?_, ?_⟩
    · rw [vtW, vtWKeys_misc.2.2.1, vtWVals_misc H B (k := 2) (by norm_num) (by omega)]; rfl
    · rw [vtW, vtWKeys_misc.2.2.2, vtWVals_misc H B (k := 3) (by norm_num) (by omega)]; rfl
  hwF b hb := by
    obtain ⟨k0, k1⟩ := vtWKeys_fw b hb
    refine ⟨?_, ?_⟩
    · rw [vtW, k0, vtWVals_fw H B hb (c := 0) (by norm_num) (by omega)]; rfl
    · rw [vtW, k1, vtWVals_fw H B hb (c := 1) (by norm_num) (by omega)]; rfl
  hwP i hi := by
    obtain ⟨k0, k1⟩ := vtWKeys_push i hi
    refine ⟨?_, ?_⟩
    · rw [vtW, k0, vtWVals_push H B hi (c := 0) (by norm_num) (by omega)]; rfl
    · rw [vtW, k1, vtWVals_push H B hi (c := 1) (by norm_num) (by omega)]; rfl
  hwC i hi := by
    obtain ⟨k0, k1⟩ := vtWKeys_count i hi
    refine ⟨?_, ?_⟩
    · rw [vtW, k0, vtWVals_count H B hi (c := 0) (by norm_num) (by omega)]; rfl
    · rw [vtW, k1, vtWVals_count H B hi (c := 1) (by norm_num) (by omega)]; rfl
  hw1 := by
    have := vtW_tail H B 0 (by norm_num)
    simp only [Nat.add_zero, List.drop_zero] at this
    rw [this, vtTailW, List.take_left' (vtTail1_length H B)]
    rfl
  hw2 := by
    have := vtW_tail H B 8 (by norm_num)
    rw [show 1876 + 8 = 1884 by rfl] at this
    rw [this, vtTailW, List.drop_left' (vtTail1_length H B), List.take_left' (vtTail2_length H B)]
    rfl
  hw3 := by
    have := vtW_tail H B 16 (by norm_num)
    rw [show 1876 + 16 = 1892 by rfl] at this
    rw [this, vtTailW, ← List.append_assoc,
      List.drop_left' (by rw [List.length_append, vtTail1_length, vtTail2_length]),
      List.take_of_length_le (by rw [vtTail3_length])]
    rfl

end

end
end LeanVM.Guest.B1.Tables
