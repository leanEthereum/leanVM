/-
  LeanVM.Guest.B1.KeccakGkr.VkCE

  `verify_keccak`'s inputs' opening, completely: the slices, then the rest.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCD
public import LeanVM.Guest.B1.KeccakGkr.VkIn
public import LeanVM.Guest.B1.KeccakGkr.VkSlices

/-!
# The inputs' opening, completely

`slices_complete`: on `verify_keccak`'s evaluated valuation, the 64 slices at the cursor and at
`slices`, the reads are the slices, the sponge absorbing them ends with a full queue whose
permutation's capacity is the last one's, and the section holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val}

theorem not_mem_of_contains {a : Atom} {S : List Atom} (h : S.contains a = false) : a ∉ S :=
  fun hm ↦ by rw [List.contains_iff_mem.mpr hm] at h; exact absurd h (by decide)

set_option maxRecDepth 20000 in
/-- **The slices, completely.** -/
theorem slices_complete (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ st ∈ slicesT (.n 1338) 1340 1345, GoodS rd vkSt w σ st)
    {slices : List E} (hslL : slices.length = 64)
    (hcur : ReadsAt rd (σ (.n 1338)) slices) (hsl : ReadsAt rd (σ (.n 10)) slices) :
    (∀ z < 64, σ (.n (slB 1345 z)) = slices.getD z 0) ∧
      ((⟨(cap5 1340).map σ, []⟩ : Fs).absorbAll slices dsObserve).pend.length = rateScalars ∧
      capOf ((⟨(cap5 1340).map σ, []⟩ : Fs).absorbAll slices dsObserve).perm =
        (cap5 (slP 1345 16 + 8)).map σ ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (slicesT (.n 1338) 1340 1345) next kret := by
  obtain ⟨k1, k3⟩ := vkSlices_ker
  -- each read
  have mR : ∀ z < 64, ∀ st ∈ fsNextT (.n 1338) z (slB 1345 z), st ∈ slicesT (.n 1338) 1340 1345 := by
    intro z hz st h
    rw [slicesT]
    refine List.mem_append_left _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨z / 4,
      List.mem_range.mpr (by omega), rfl⟩, List.mem_append_right _ (List.mem_flatten.mpr ⟨_,
        List.mem_map.mpr ⟨z % 4, List.mem_range.mpr (Nat.mod_lt _ (by norm_num)), rfl⟩,
        List.mem_append_left _ ?_⟩)⟩)
    rw [Nat.div_add_mod]; exact h
  have R : ∀ z < 64, σ (.n (slB 1345 z)) = slices.getD z 0 := by
    intro z hz
    have hm := mR z hz _ List.mem_cons_self
    have hns : Atom.load (.n (slB 1345 z)) (.n 1338) z ∉ vkSt := by
      have := List.all_eq_true.mp k3 _ (load_mem_resid hm)
      simp only [slRes, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        Bool.not_eq_true'] at this
      rcases this with ⟨-, h⟩ | ⟨⟨⟨h, -⟩, -⟩, -⟩
      · exact not_mem_of_contains h
      · exact absurd h (by simp)
    obtain ⟨e, -, -⟩ := fsNext_complete (C := C) (fun st h ↦ hg st (mR z hz st h))
      hns (v := slices.getD z 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact hcur z (by omega))
    exact e
  have H : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (slicesT (.n 1338) 1340 1345) next kret :=
    fun hn ↦ block_holds (S := vkSt) (w := w) k1 hσ hg
      (fun a ha ↦ by
        have hs := List.all_eq_true.mp k3 a ha
        cases a with
        | load d p off =>
          simp only [slRes, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
            Bool.not_eq_true'] at hs
          rcases hs with ⟨⟨rfl, hoff⟩, hns⟩ | ⟨⟨⟨rfl, hoff⟩, rfl⟩, -⟩
          · exact Or.inr (side_load (not_mem_of_contains hns) (hcur off (by omega)))
          · left
            show LoadHolds rd (σ (.n 10)) off (σ (.n (slB 1345 off)))
            rw [R off hoff, List.getD_eq_getElem _ _ (by omega)]
            exact hsl off (by omega)
        | _ => simp [slRes] at hs) hn
  obtain ⟨-, -, hpl, hcap, -⟩ := slicesT_holds (H (next := True) (kret := fun _ ↦ True) trivial)
  have hm : (List.range 64).map (fun z ↦ σ (.n (slB 1345 z))) = slices := by
    apply List.ext_getElem (by simp [hslL])
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [R k (by simpa using h1), List.getD_eq_getElem _ _ h2]
  rw [hm] at hpl hcap
  exact ⟨R, hpl, hcap, H⟩

set_option maxRecDepth 20000 in
/-- **The inputs' opening, completely.** -/
theorem vkIn_complete (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ st ∈ vkInT, GoodS rd vkSt w σ st)
    {v12 : E} (hv : LoadHolds rd (σ (.n 161)) 264 v12) {low : List E} (hlowL : low.length = 4)
    (hlow : ∀ t < 4, LoadHolds rd (σ (.n 9)) (39 + t) (low.getD t 0))
    (hT : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t,
      LoadHolds rd (σ (.n 1210)) (2 ^ t - 2 + i) ((eqKernel (low.take t)).getD i 0))
    {mu : List E} (hmuL : mu.length = 16)
    (hmu : ∀ k < 16, LoadHolds rd (σ (.n 161)) (270 + k) (mu.getD k 0))
    {slices : List E} (hslL : slices.length = 64) (hcur : ReadsAt rd (w 1338) slices)
    (hsl : ReadsAt rd (σ (.n 10)) slices) :
    σ (.n 1199) = σ (.n 929) * gen ∧ σ (.n 1200) = v12 ∧ σ (.n 1202) = σ (.n 9) * gen ^ 39 ∧
      (∀ j < 7, σ (.n (1203 + j)) = w (1203 + j)) ∧ σ (.n 1327) = multilinearEval mu low ∧
      σ (.n 1330) = σ (.n 9) * gen ^ 39 * σ (.n 6) ∧ (∀ j < 7, σ (.n (1333 + j)) = w (1333 + j)) ∧
      (∀ z < 64, σ (.n (slB 1345 z)) = slices.getD z 0) ∧
      ((⟨(List.range 5).map fun j ↦ w (1333 + j), []⟩ : Fs).absorbAll slices dsObserve).pend.length =
        rateScalars ∧
      capOf ((⟨(List.range 5).map fun j ↦ w (1333 + j), []⟩ : Fs).absorbAll slices dsObserve).perm =
        (cap5 1740).map σ ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkInT next kret := by
  obtain ⟨k1, k2, k3, k5, k6⟩ := vkIn_ker
  have mEQ : ∀ st ∈ eqtreeT (.n 9) (.n 1210) 39 1211 4, st ∈ vkInT := fun st h ↦ by
    rw [vkInT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ h))))
  have mPD : ∀ st ∈ vkInPD, st ∈ vkInT := fun st h ↦ by
    rw [vkInT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ h)))
  have mCP : ∀ st ∈ (List.range 5).map (fun j ↦ Stmt.atom (.copy (.n (1340 + j)) (.n (1333 + j)))),
      st ∈ vkInT := fun st h ↦ by
    rw [vkInT]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have mSL : ∀ st ∈ slicesT (.n 1338) 1340 1345, st ∈ vkInT := fun st h ↦ by
    rw [vkInT]; exact List.mem_append_right _ h
  have gA : ∀ a, Stmt.atom a ∈ vkInT → Good rd vkSt w σ a := fun a h ↦ hg _ h
  -- the atoms
  have c3975 : σ (.n 1198) = word 2 0 := gA (.const (.n 1198) (word 2 0)) (by simp [vkInT])
  have m3976 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1199) (.n 929) (.n 1198)) (by simp [vkInT]))
  have e3977 : σ (.n 1200) = v12 :=
    load_val (gA (.load (.n 1200) (.n 161) 264) (by simp [vkInT])) (not_mem_of_noneIn k1 _ (by simp)) hv
  have c3978 : σ (.n 1201) = word 549755813888 0 :=
    gA (.const (.n 1201) (word 549755813888 0)) (by simp [vkInT])
  have m3979 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1202) (.n 9) (.n 1201)) (by simp [vkInT]))
  have gc1 := hg (.call "keccak_plain_rounds__L4_L1" [.n 924, .n 925, .n 926, .n 927, .n 928,
    .n 932, .n 933, .n 1199, .n 1200, .n 1202, .n 11] ((List.range 7).map fun j ↦ .n (1203 + j)))
    (by simp [vkInT])
  have e3980 : ∀ j < 7, σ (.n (1203 + j)) = w (1203 + j) := fun j hj ↦
    gc1 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have c4105 : σ (.n 1328) = word 549755813888 0 :=
    gA (.const (.n 1328) (word 549755813888 0)) (by simp [vkInT])
  have m4106 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1329) (.n 9) (.n 1328)) (by simp [vkInT]))
  have m4107 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1330) (.n 1329) (.n 6)) (by simp [vkInT]))
  have c4108 : σ (.n 1331) = word 0 0 := gA (.const (.n 1331) (word 0 0)) (by simp [vkInT])
  have c4109 : σ (.n 1332) = word 0 0 := gA (.const (.n 1332) (word 0 0)) (by simp [vkInT])
  have gc2 := hg (.call "keccak_plain_rounds__L6_L0" [.n 1203, .n 1204, .n 1205, .n 1206, .n 1207,
    .n 1331, .n 1332, .n 1208, .n 1209, .n 1330, .n 11] ((List.range 7).map fun j ↦ .n (1333 + j)))
    (by simp [vkInT])
  have e4110 : ∀ j < 7, σ (.n (1333 + j)) = w (1333 + j) := fun j hj ↦
    gc2 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have ecp : ∀ j < 5, σ (.n (1340 + j)) = σ (.n (1333 + j)) := fun j hj ↦
    hg _ (mCP _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  -- the low tree and `μ` at the low point
  have EQ : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (eqtreeT (.n 9) (.n 1210) 39 1211 4) next kret :=
    fun hn ↦ eqtree_complete (by norm_num) (fun st h ↦ hg st (mEQ st h)) (not_mem_of_noneIn k2)
      hlowL hlow hT hn
  have PD : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkInPD next kret :=
    fun hn ↦ loads_complete k3 hσ (fun st h ↦ hg st (mPD st h)) k5 k6 (fun q hq off h1 h2 ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp only at h1 h2 ⊢
        have := hT 4 (by norm_num) le_rfl (off - 14) (by norm_num; omega)
        rw [show 2 ^ 4 - 2 + (off - 14) = off by norm_num; omega] at this
        exact ⟨_, this⟩
      · simp only at h1 h2 ⊢
        have := hmu (off - 270) (by omega)
        rw [show 270 + (off - 270) = off by omega] at this
        exact ⟨_, this⟩) hn
  obtain ⟨hdot, -⟩ := pairsDotT_holds (C := fun _ _ _ ↦ True) (P := fun i ↦ (eqKernel low).getD i 0)
    (Q := fun i ↦ mu.getD i 0) (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some] at hv
      have := hT 4 (by norm_num) le_rfl k (by norm_num; omega)
      rw [show low.take 4 = low by rw [← hlowL]; exact List.take_length] at this
      exact loadHolds_unique hv (by simpa using this))
    (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some] at hv
      have := hmu k hk
      rw [List.getD_eq_getElem?_getD] at this
      exact loadHolds_unique hv this)
    (by simp [consecOffs]) (PD (next := True) (kret := fun _ ↦ True) trivial)
  simp only [consecOffs, List.length_map, List.length_range, pairsDotV] at hdot
  have e4104 : σ (.n 1327) = multilinearEval mu low := by
    rw [show (1327 : ℕ) = 1265 + 4 * (16 - 1) + 2 from rfl, hdot,
      multilinearEval_eqAt mu low hmuL hlowL]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < 16 := Finset.mem_range.1 hi
    rw [eqKernel_getD]
    simp [hlowL, hi']
  -- the slices
  have hc5 : (cap5 1340).map σ = (List.range 5).map fun j ↦ w (1333 + j) := by
    simp only [cap5, List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append]
    rw [ecp 0 (by omega), ecp 1 (by omega), ecp 2 (by omega), ecp 3 (by omega), ecp 4 (by omega),
      e4110 0 (by omega), e4110 1 (by omega), e4110 2 (by omega), e4110 3 (by omega),
      e4110 4 (by omega)]
    rfl
  obtain ⟨esl, hpl, hcp, SL⟩ := slices_complete (C := fun _ _ _ ↦ True) hσ
    (fun st h ↦ hg st (mSL st h)) hslL
    (by rw [show (1338 : ℕ) = 1333 + 5 from rfl, e4110 5 (by omega)]; exact hcur) hsl
  rw [hc5] at hpl hcp
  refine ⟨by rw [m3976, c3975, word_gen], e3977, by rw [m3979, c3978, word_2p39], e3980, e4104,
    by rw [m4107, m4106, c4105, word_2p39], e4110, esl, hpl, hcp, fun {next kret} hn ↦ ?_⟩
  rw [vkInT]
  simp only [holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨c3975, m3976, ?_, c3978, m3979, trivial, trivial, EQ (PD ⟨c4105, m4106, m4107, c4108,
    c4109, trivial, ?_⟩)⟩
  · rw [e3977]; exact hv
  rw [holdsList_map_atoms]
  exact ⟨fun j hj ↦ ecp j hj, SL hn⟩

end
end LeanVM.Guest.B1.VerifySub
