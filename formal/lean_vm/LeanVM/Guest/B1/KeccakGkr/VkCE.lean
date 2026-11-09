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
`slices`, the capacity canonical, the reads are the slices, the sponge absorbing them squeezes the
ring map's first challenge, and the section holds.
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
    (hg : ∀ st ∈ slicesT (.n 1387) 1389 1394, GoodS rd vkSt w σ st)
    (hcap : AllCanonical ((cap5 1389).map σ)) {slices : List E} (hslL : slices.length = 64)
    (hcur : ReadsAt rd (σ (.n 1387)) slices) (hsl : ReadsAt rd (σ (.n 10)) slices) :
    (∀ z < 64, σ (.n (slB 1394 z)) = slices.getD z 0) ∧
      ((⟨(cap5 1389).map σ, []⟩ : Fs).absorbAll slices dsObserve).squeeze =
        (σ (.n (1394 + 854)), ⟨(cap5 (1394 + 843)).map σ, []⟩) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (slicesT (.n 1387) 1389 1394) next kret := by
  obtain ⟨k1, k2, k3⟩ := vkSlices_ker
  have mP : ∀ st ∈ slicesPre (.n 1387) 1389 1394, st ∈ slicesT (.n 1387) 1389 1394 :=
    fun st h ↦ by rw [slicesT_pre]; exact List.mem_append_left _ h
  have mC : ∀ st ∈ challengeT (.n (1394 + 835)) (.n (1394 + 836)) (1394 + 848),
      st ∈ slicesT (.n 1387) 1389 1394 :=
    fun st h ↦ by rw [slicesT_pre]; exact List.mem_append_right _ h
  -- each read
  have mR : ∀ z < 64, ∀ st ∈ fsNextT (.n 1387) z (slB 1394 z), st ∈ slicesPre (.n 1387) 1389 1394 := by
    intro z hz st h
    rw [slicesPre]
    refine List.mem_append_left _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨z / 4,
      List.mem_range.mpr (by omega), rfl⟩, List.mem_append_right _ (List.mem_flatten.mpr ⟨_,
        List.mem_map.mpr ⟨z % 4, List.mem_range.mpr (Nat.mod_lt _ (by norm_num)), rfl⟩,
        List.mem_append_left _ ?_⟩)⟩)
    rw [Nat.div_add_mod]; exact h
  have R : ∀ z < 64, σ (.n (slB 1394 z)) = slices.getD z 0 ∧
      IsCanonical128 (σ (.n (slB 1394 z + 7))) ∧ IsCanonical128 (σ (.n (slB 1394 z + 9))) := by
    intro z hz
    have hm := mR z hz _ List.mem_cons_self
    have hns : Atom.load (.n (slB 1394 z)) (.n 1387) z ∉ vkSt := by
      have := List.all_eq_true.mp k3 _ (load_mem_resid hm)
      simp only [slRes, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        Bool.not_eq_true'] at this
      rcases this with ⟨-, h⟩ | ⟨⟨⟨h, -⟩, -⟩, -⟩
      · exact not_mem_of_contains h
      · exact absurd h (by simp)
    obtain ⟨e, c7, c9, -, -⟩ := fsNext_complete (C := C) (fun st h ↦ hg st (mP st (mR z hz st h)))
      hns (v := slices.getD z 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact hcur z (by omega))
    exact ⟨e, c7, c9⟩
  -- the reads and their permutations
  have hA : ∀ i ∈ slA, IsCanonical128 (σ (.n i)) := by
    intro i hi
    simp only [slA, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl | rfl | rfl | rfl) | ⟨z, hz, rfl | rfl⟩
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact (R z hz).2.1
    · exact (R z hz).2.2
  have SP : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (slicesPre (.n 1387) 1389 1394) next kret :=
    fun hn ↦ block_holdsP (S := vkSt) (w := w) (P := []) k1 hσ k2 (by simpa using fun st h ↦ hg st (mP st h)) hA
      (fun a ha ↦ by
        have hs := List.all_eq_true.mp k3 a ha
        cases a with
        | load d p off =>
          simp only [slRes, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
            Bool.not_eq_true'] at hs
          rcases hs with ⟨⟨rfl, hoff⟩, hns⟩ | ⟨⟨⟨rfl, hoff⟩, rfl⟩, -⟩
          · exact Or.inr (side_load (not_mem_of_contains hns) (hcur off (by omega)))
          · left
            show LoadHolds rd (σ (.n 10)) off (σ (.n (slB 1394 off)))
            rw [(R off hoff).1, List.getD_eq_getElem _ _ (by omega)]
            exact hsl off (by omega)
        | _ => simp [slRes] at hs) hn
  -- the last permutation, and the challenge
  have hall := ((holdsList_atoms (C := C) (rd := rd) (σ := σ) (allAtoms_of_all k1) True
    (fun _ ↦ True)).1 (SP trivial)).1
  have kf := hall (.keccak (slCells 1394 15 ++ cap5 (slCap 1389 1394 15))
    ((List.range 13).map fun k ↦ .n (1394 + 835 + k)) false false)
    (by rw [slicesPre]; exact List.mem_append_right _ List.mem_cons_self)
  obtain ⟨-, -, -, hout⟩ := keccak_outs kf
  have c1 : IsCanonical128 (σ (.n (1394 + 836))) := by
    have := hout 1 (by norm_num)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : 1 < 13),
      Option.map_some, Option.getD_some] at this
    rw [show 1394 + 836 = 1394 + 835 + 1 from rfl, this]; exact cellsOfState_canonical _ _ _
  obtain ⟨-, CH⟩ := challenge_complete (C := C) (fun st h ↦ hg st (mC st h)) c1
  have H : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (slicesT (.n 1387) 1389 1394) next kret := fun hn ↦ by
    rw [slicesT_pre, holdsList_append]; exact SP (CH hn)
  obtain ⟨-, -, hsq, -⟩ := slicesT_holds (H (next := True) (kret := fun _ ↦ True) trivial)
  have hm : (List.range 64).map (fun z ↦ σ (.n (slB 1394 z))) = slices := by
    apply List.ext_getElem (by simp [hslL])
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [(R k (by simpa using h1)).1, List.getD_eq_getElem _ _ h2]
  rw [hm] at hsq
  exact ⟨fun z hz ↦ (R z hz).1, hsq, H⟩

set_option maxRecDepth 20000 in
/-- **The inputs' opening, completely.** -/
theorem vkIn_complete (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ st ∈ vkInT, GoodS rd vkSt w σ st)
    {v12 : E} (hv : LoadHolds rd (σ (.n 203)) 264 v12) {low : List E} (hlowL : low.length = 4)
    (hlow : ∀ t < 4, LoadHolds rd (σ (.n 9)) (39 + t) (low.getD t 0))
    (hT : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t,
      LoadHolds rd (σ (.n 1259)) (2 ^ t - 2 + i) ((eqKernel (low.take t)).getD i 0))
    {mu : List E} (hmuL : mu.length = 16)
    (hmu : ∀ k < 16, LoadHolds rd (σ (.n 203)) (270 + k) (mu.getD k 0))
    (hcap : AllCanonical ((List.range 5).map fun j ↦ w (1382 + j))) {slices : List E}
    (hslL : slices.length = 64) (hcur : ReadsAt rd (w 1387) slices)
    (hsl : ReadsAt rd (σ (.n 10)) slices) :
    σ (.n 1248) = σ (.n 971) * gen ∧ σ (.n 1249) = v12 ∧ σ (.n 1251) = σ (.n 9) * gen ^ 39 ∧
      (∀ j < 7, σ (.n (1252 + j)) = w (1252 + j)) ∧ σ (.n 1376) = multilinearEval mu low ∧
      σ (.n 1379) = σ (.n 9) * gen ^ 39 * σ (.n 6) ∧ (∀ j < 7, σ (.n (1382 + j)) = w (1382 + j)) ∧
      (∀ z < 64, σ (.n (slB 1394 z)) = slices.getD z 0) ∧
      ((⟨(List.range 5).map fun j ↦ w (1382 + j), []⟩ : Fs).absorbAll slices dsObserve).squeeze =
        (σ (.n 2248), ⟨(cap5 2237).map σ, []⟩) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkInT next kret := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := vkIn_ker
  have mEQ : ∀ st ∈ eqtreeT (.n 9) (.n 1259) 39 1260 4, st ∈ vkInT := fun st h ↦ by
    rw [vkInT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ h))))
  have mPD : ∀ st ∈ vkInPD, st ∈ vkInT := fun st h ↦ by
    rw [vkInT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ h)))
  have mCP : ∀ st ∈ (List.range 5).map (fun j ↦ Stmt.atom (.copy (.n (1389 + j)) (.n (1382 + j)))),
      st ∈ vkInT := fun st h ↦ by
    rw [vkInT]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have mSL : ∀ st ∈ slicesT (.n 1387) 1389 1394, st ∈ vkInT := fun st h ↦ by
    rw [vkInT]; exact List.mem_append_right _ h
  have gA : ∀ a, Stmt.atom a ∈ vkInT → Good rd vkSt w σ a := fun a h ↦ hg _ h
  -- the atoms
  have c3975 : σ (.n 1247) = word 2 0 0 := gA (.const (.n 1247) (word 2 0 0)) (by simp [vkInT])
  have m3976 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1248) (.n 971) (.n 1247)) (by simp [vkInT]))
  have e3977 : σ (.n 1249) = v12 :=
    load_val (gA (.load (.n 1249) (.n 203) 264) (by simp [vkInT])) (not_mem_of_noneIn k1 _ (by simp)) hv
  have c3978 : σ (.n 1250) = word 549755813888 0 0 :=
    gA (.const (.n 1250) (word 549755813888 0 0)) (by simp [vkInT])
  have m3979 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1251) (.n 9) (.n 1250)) (by simp [vkInT]))
  have gc1 := hg (.call "keccak_plain_rounds__L4_L1" [.n 966, .n 967, .n 968, .n 969, .n 970,
    .n 980, .n 982, .n 1248, .n 1249, .n 1251] ((List.range 7).map fun j ↦ .n (1252 + j)))
    (by simp [vkInT])
  have e3980 : ∀ j < 7, σ (.n (1252 + j)) = w (1252 + j) := fun j hj ↦
    gc1 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have c4105 : σ (.n 1377) = word 549755813888 0 0 :=
    gA (.const (.n 1377) (word 549755813888 0 0)) (by simp [vkInT])
  have m4106 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1378) (.n 9) (.n 1377)) (by simp [vkInT]))
  have m4107 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1379) (.n 1378) (.n 6)) (by simp [vkInT]))
  have c4108 : σ (.n 1380) = word 0 0 0 := gA (.const (.n 1380) (word 0 0 0)) (by simp [vkInT])
  have c4109 : σ (.n 1381) = word 0 0 0 := gA (.const (.n 1381) (word 0 0 0)) (by simp [vkInT])
  have gc2 := hg (.call "keccak_plain_rounds__L6_L0" [.n 1252, .n 1253, .n 1254, .n 1255, .n 1256,
    .n 1380, .n 1381, .n 1257, .n 1258, .n 1379] ((List.range 7).map fun j ↦ .n (1382 + j)))
    (by simp [vkInT])
  have e4110 : ∀ j < 7, σ (.n (1382 + j)) = w (1382 + j) := fun j hj ↦
    gc2 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have ecp : ∀ j < 5, σ (.n (1389 + j)) = σ (.n (1382 + j)) := fun j hj ↦
    hg _ (mCP _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  -- the low tree and `μ` at the low point
  have EQ : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (eqtreeT (.n 9) (.n 1259) 39 1260 4) next kret :=
    fun hn ↦ eqtree_complete (by norm_num) (fun st h ↦ hg st (mEQ st h)) (not_mem_of_noneIn k2)
      hlowL hlow hT hn
  have PD : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkInPD next kret :=
    fun hn ↦ loads_complete k3 hσ k4 (fun st h ↦ hg st (mPD st h)) k5 k6 (fun q hq off h1 h2 ↦ by
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
  have e4104 : σ (.n 1376) = multilinearEval mu low := by
    rw [show (1376 : ℕ) = 1314 + 4 * (16 - 1) + 2 from rfl, hdot,
      multilinearEval_eqAt mu low hmuL hlowL]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < 16 := Finset.mem_range.1 hi
    rw [eqKernel_getD]
    simp [hlowL, hi']
  -- the slices
  have hc5 : (cap5 1389).map σ = (List.range 5).map fun j ↦ w (1382 + j) := by
    simp only [cap5, List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append]
    rw [ecp 0 (by omega), ecp 1 (by omega), ecp 2 (by omega), ecp 3 (by omega), ecp 4 (by omega),
      e4110 0 (by omega), e4110 1 (by omega), e4110 2 (by omega), e4110 3 (by omega),
      e4110 4 (by omega)]
    rfl
  obtain ⟨esl, hsq, SL⟩ := slices_complete (C := fun _ _ _ ↦ True) hσ (fun st h ↦ hg st (mSL st h))
    (by rw [hc5]; exact hcap) hslL (by rw [show (1387 : ℕ) = 1382 + 5 from rfl, e4110 5 (by omega)]; exact hcur) hsl
  rw [hc5] at hsq
  refine ⟨by rw [m3976, c3975, word_gen], e3977, by rw [m3979, c3978, word_2p39], e3980, e4104,
    by rw [m4107, m4106, c4105, word_2p39], e4110, esl, hsq, fun {next kret} hn ↦ ?_⟩
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
