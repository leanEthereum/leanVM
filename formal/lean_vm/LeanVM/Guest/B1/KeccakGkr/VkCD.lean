/-
  LeanVM.Guest.B1.KeccakGkr.VkCD

  `verify_keccak`'s committed outputs' opening, completely.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCDK
public import LeanVM.Guest.B1.KeccakGkr.VkCC
public import LeanVM.Guest.B1.KeccakGkr.VkChecks

/-!
# The committed outputs' opening, completely

`vkOut_complete`: on `verify_keccak`'s evaluated valuation, the word at the cursor the slot's
rounds return, the slot point at `z_vals·g^τ`, the segment coordinate and the lane weights in
memory, and the guest's check holding, the opening holds (its rounds' call and the copy loop
with any relation); the slot's rounds return the oracle's words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {σ : Val}

theorem one_add_gen_pow_inK (k : ℕ) : IsInK (1 + gen ^ k) :=
  isInK_add ((isInK_iff _).mpr ⟨1, ofK_one.symm⟩) ((isInK_iff _).mpr ⟨_, gen_pow_eq_ofK k⟩)

/-- **The committed outputs' opening, completely.** -/
theorem vkOut_complete (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ st ∈ vkOutT, GoodS rd vkSt w σ st)
    {τ : ℕ} (h17 : σ (.n 18) = gen ^ (τ - 4)) {wd : E}
    (hword : LoadHolds rd (σ (.n 923)) 0 wd) {slotO : List E}
    (hslot : ReadsAt rd (σ (.n 9) * σ (.n 6)) slotO) (hslotL : slotO.length = 6) {r0 : E}
    (hr0 : LoadHolds rd (σ (.n 61) * σ (.n 18)) 0 r0) {L : ℕ → E}
    (hL : ∀ lane < 25, LoadHolds rd (σ (.n 228)) (30 + lane) (L lane))
    (hchk : (∑ lane ∈ range 25, (∑ m ∈ range 1, eqAt [r0] m * eqAt slotO (25 * (1 + m) + lane)) *
      L lane) * wd = σ (.n 924)) :
    σ (.n 915) = σ (.n 9) * σ (.n 6) ∧ (∀ j < 7, σ (.n (918 + j)) = w (918 + j)) ∧
      σ (.n 925) = wd ∧ (σ (.n 926), σ (.n 927)) = Keccak.scalarCells wd dsObserve ∧
      σ (.n 928) = σ (.n 61) * σ (.n 18) ∧
      σ (.n 1188) = 1 + σ (.n 18) ∧ σ (.n 1189) = 1 ∧ σ (.n 1191) = σ (.n 9) * gen ^ 4 ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkOutT next kret := by
  obtain ⟨k1, k2, k4, k5, k6, k8, k9⟩ := vkOut_ker
  have mFN : ∀ st ∈ fsNextT (.n 923) 0 925, st ∈ vkOutT := fun st h ↦ by
    rw [vkOutT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ h))))
  have mSL : ∀ st ∈ vkOutSL, st ∈ vkOutT := fun st h ↦ by
    rw [vkOutT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  have mDL : ∀ st ∈ vkOutDL, st ∈ vkOutT := fun st h ↦ by
    rw [vkOutT]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have gA : ∀ a, Stmt.atom a ∈ vkOutT → Good rd vkSt w σ a := fun a h ↦ hg _ h
  -- the atoms
  have m3691 := mulG (by norm_num) (by norm_num) (gA (.mul (.n 915) (.n 9) (.n 6)) (by simp [vkOutT]))
  have c3692 : σ (.n 916) = word 0 0 := gA (.const (.n 916) (word 0 0)) (by simp [vkOutT])
  have c3693 : σ (.n 917) = word 0 0 := gA (.const (.n 917) (word 0 0)) (by simp [vkOutT])
  have gcall := hg (.call "keccak_plain_rounds__L6_L0" [.n 909, .n 910, .n 911, .n 912, .n 913,
    .n 916, .n 917, .n 914, .n 152, .n 915, .n 11] ((List.range 7).map fun j ↦ .n (918 + j)))
    (by simp [vkOutT])
  have e3694 : ∀ j < 7, σ (.n (918 + j)) = w (918 + j) := fun j hj ↦
    gcall _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have m3711 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 928) (.n 61) (.n 18)) (by simp [vkOutT]))
  have m3969 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1186) (.n 1185) (.n 925)) (by simp [vkOutT]))
  have c3970 : σ (.n 1187) = word 1 0 := gA (.const (.n 1187) (word 1 0)) (by simp [vkOutT])
  have a3971 : σ (.n 1188) = σ (.n 1187) + σ (.n 18) :=
    gA (.add (.n 1188) (.n 1187) (.n 18)) (by simp [vkOutT])
  have c3972 : σ (.n 1189) = word 1 0 := gA (.const (.n 1189) (word 1 0)) (by simp [vkOutT])
  have c3973 : σ (.n 1190) = word 16 0 := gA (.const (.n 1190) (word 16 0)) (by simp [vkOutT])
  have m3974 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1191) (.n 9) (.n 1190)) (by simp [vkOutT]))
  -- the word
  obtain ⟨ew, cells, FN⟩ := fsNext_complete (C := fun _ _ _ ↦ True)
    (fun st h ↦ hg st (mFN st h)) (not_mem_of_noneIn k1 _ (by simp)) hword
  -- the lane weights
  have SL : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkOutSL next kret :=
    fun hn ↦ loads_complete k2 hσ (fun st h ↦ hg st (mSL st h)) k4 k5 (fun q hq off h1 h2 ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp only at h2 ⊢
        rw [m3691]; exact ⟨_, hslot off (by omega)⟩
      · simp only at h2 ⊢
        obtain rfl : off = 0 := by omega
        rw [m3711]; exact ⟨_, hr0⟩) hn
  obtain ⟨rs, hrsL, hrs, r, hr, hlanes, -⟩ := slotLanesT_holds (Or.inl rfl) (by norm_num)
    (SL (next := True) (kret := fun _ ↦ True) trivial)
  have hrs' : rs = slotO := by
    apply List.ext_getElem (by rw [hrsL, hslotL])
    intro k h1 h2
    exact loadHolds_unique (hrs k h1) (by rw [m3691]; exact hslot k h2)
  have hr' : r = r0 := loadHolds_unique hr (by rw [m3711] at hr ⊢; exact hr0)
  -- the dot product
  have DL : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkOutDL next kret :=
    fun hn ↦ loads_complete k6 hσ (fun st h ↦ hg st (mDL st h)) k8 k9 (fun q hq off h1 h2 ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      simp only at h1 h2 ⊢
      have := hL (off - 30) (by omega)
      rw [show 30 + (off - 30) = off by omega] at this
      exact ⟨_, this⟩) hn
  obtain ⟨hdot, -⟩ := dotLoadsT_holds (xs := (List.range 25).map (slotLaneV 929 1)) (P := L)
    (fun k hk v hv ↦ loadHolds_unique hv (hL k (by simpa using hk))) (by simp)
    (DL (next := True) (kret := fun _ ↦ True) trivial)
  simp only [List.length_map, List.length_range] at hdot
  have e3968 : σ (.n 1185) = ∑ lane ∈ range 25,
      (∑ m ∈ range 1, eqAt [r0] m * eqAt slotO (25 * (1 + m) + lane)) * L lane := by
    rw [show (1185 : ℕ) = dotLoadsV 1112 25 from rfl, hdot]
    refine Finset.sum_congr rfl fun lane hl ↦ ?_
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_range,
      hlanes lane (Finset.mem_range.1 hl), hrs', hr']
  have e3969 : σ (.n 1186) = σ (.n 924) := by rw [m3969, e3968, ew, hchk]
  refine ⟨m3691, e3694, ew, cells, m3711,
    by rw [a3971, c3970, word_one], by rw [c3972, word_one], by rw [m3974, c3973, word_16],
    fun {next kret} hn ↦ ?_⟩
  rw [vkOutT]
  simp only [holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨m3691, c3692, c3693, trivial, FN ⟨m3711, SL (DL ⟨m3969, ?_, c3970, a3971, c3972, c3973,
    m3974, ?_, fun _ ↦ trivial, hn⟩)⟩⟩
  · rw [e3969]; exact e_add_self _
  · rw [a3971, c3970, word_one, h17]; exact one_add_gen_pow_inK _

end
end LeanVM.Guest.B1.VerifySub
