/-
  LeanVM.Guest.B1.KeccakGkr.VkCF

  `verify_keccak`'s inputs' check and return, completely.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCE
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The inputs' check and the return, completely

`vkFin_complete`: on `verify_keccak`'s evaluated valuation, the last claim's point, local point
and lanes, the slot point at `1324` and the slices in memory, and the guest's check holding at
them, the section holds and returns its words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {σ : Val}

set_option maxRecDepth 20000 in
/-- **The inputs' check and the return, completely.** -/
theorem vkFin_complete (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ st ∈ vkFinT, GoodS rd vkSt w σ st)
    {τ : ℕ} (hτ : 4 ≤ τ) (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (τ - 4)) {pp lc lp : E}
    {point loc lanes slotI slices : List E}
    (hpp : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 266 pp) (hpt : ReadsAt rd pp point)
    (hptL : point.length = τ - 3)
    (hlc : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 268 lc) (hloc : ReadsAt rd lc loc) (hlocL : loc.length = 11)
    (hlp : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 267 lp) (hlanes : ReadsAt rd lp lanes)
    (hlen : lanes.length = 25) (hslot : ReadsAt rd (σ (.n (val% «verify_keccak» "in_slot"))) slotI) (hslotL : slotI.length = 6)
    (hsl : ReadsAt rd (σ (.n (val% «verify_keccak» "slices"))) slices) (hslL : slices.length = 64)
    (hchk : σ (.n (val% «verify_keccak» "mu_at_low@16")) * formVal (fun l ↦ ∑ m ∈ range 2,
        eqAt [point.getD (τ - 4) 0] m * eqAt slotI (25 * (0 + m) + l)) (kLane lanes)
        (fun r ↦ ∑ z ∈ range 64, slices.getD z 0 * eqAt (loc.take 6) ((z + r) % 64)) =
      σ (.n (val% «verify_keccak» "in_value"))) (h1251 : σ (.n (val% «verify_keccak» "fs0@15~11")) = σ (.n (val% «verify_keccak» "z_vals")) * gen ^ 39) :
    σ (.n (val% «verify_keccak» "last_point")) = pp ∧ σ (.n (val% «verify_keccak» "s81#1")) = 1 + σ (.n (val% «verify_keccak» "pack_g")) ∧ σ (.n (val% «verify_keccak» "s81#2")) = 1 ∧
      σ (.n (val% «verify_keccak» "s81#4")) = σ (.n (val% «verify_keccak» "z_vals")) * gen ^ 43 ∧
      ∀ {kret : List E → Prop}, kret [σ (.n (val% «verify_keccak» "nxt[8]@22")), σ (.n (val% «verify_keccak» "nxt[9]@22")), σ (.n (val% «verify_keccak» "nxt[10]@22")), σ (.n (val% «verify_keccak» "nxt[11]@22")),
        σ (.n (val% «verify_keccak» "nxt[12]@22")), σ (.n (val% «verify_keccak» "cursor@16")) * gen ^ 64, σ (.n (val% «verify_keccak» "x@2"))] →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkFinT False kret := by
  obtain ⟨k1, k2, k4, k5, k6, k8, k9, k10, k12, k13, k14⟩ := vkFin_ker
  have mSL : ∀ st ∈ vkFinSL, st ∈ vkFinT := fun st h ↦ by
    rw [vkFinT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))
  have mLD : ∀ st ∈ (List.range 64).map (fun z ↦ Stmt.atom (.load (.n (1976 + z)) (.n (val% «verify_keccak» "slices")) z)),
      st ∈ vkFinT := fun st h ↦ by
    rw [vkFinT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ h))))))
  have mFT : ∀ st ∈ vkFinFT, st ∈ vkFinT := fun st h ↦ by
    rw [vkFinT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
  have mFA : ∀ st ∈ vkFinFA, st ∈ vkFinT := fun st h ↦ by
    rw [vkFinT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ h)))
  have mCP : ∀ st ∈ (List.range 5).map (fun j ↦ Stmt.atom (.copy (.n (3359 + j)) (.n (1735 + j)))),
      st ∈ vkFinT := fun st h ↦ by
    rw [vkFinT]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have gA : ∀ a, Stmt.atom a ∈ vkFinT → Good rd vkSt w σ a := fun a h ↦ hg _ h
  -- the pointers
  have e4977 : σ (.n (val% «verify_keccak» "last_point")) = pp :=
    load_val (gA (.load (.n (val% «verify_keccak» "last_point")) (.n (val% «verify_keccak» "claims")) 266) (by simp [vkFinT])) (not_mem_of_noneIn k1 _ (by simp)) hpp
  have e5212 : σ (.n (val% «verify_keccak» "last_local")) = lc :=
    load_val (gA (.load (.n (val% «verify_keccak» "last_local")) (.n (val% «verify_keccak» "claims")) 268) (by simp [vkFinT])) (not_mem_of_noneIn k1 _ (by simp)) hlc
  have e6363 : σ (.n (val% «verify_keccak» "last_lanes")) = lp :=
    load_val (gA (.load (.n (val% «verify_keccak» "last_lanes")) (.n (val% «verify_keccak» "claims")) 267) (by simp [vkFinT])) (not_mem_of_noneIn k1 _ (by simp)) hlp
  have m4978 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n (val% «verify_keccak» "s72#0")) (.n (val% «verify_keccak» "last_point")) (.n (val% «verify_keccak» "pack_g"))) (by simp [vkFinT]))
  have hseg : LoadHolds rd (σ (.n (val% «verify_keccak» "s72#0"))) 0 (point.getD (τ - 4) 0) := by
    rw [m4978, e4977, h17, loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by omega)]
    exact hpt _ (by omega)
  -- the slot's lane weights
  have SL : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkFinSL next kret :=
    fun hn ↦ loads_complete k2 hσ (fun st h ↦ hg st (mSL st h)) k4 k5 (fun q hq off h1 h2 ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp only at h2 ⊢; exact ⟨_, hslot off (by omega)⟩
      · simp only at h2 ⊢
        obtain rfl : off = 0 := by omega
        exact ⟨_, hseg⟩) hn
  obtain ⟨rs, hrsL, hrs, r, hr, hlw, -⟩ := slotLanesT_holds (Or.inr rfl) (by norm_num)
    (SL (next := True) (kret := fun _ ↦ True) trivial)
  have hrs' : rs = slotI := by
    apply List.ext_getElem (by rw [hrsL, hslotL])
    intro k h1 h2
    exact loadHolds_unique (hrs k h1) (hslot k h2)
  have hr' : r = point.getD (τ - 4) 0 := loadHolds_unique hr hseg
  -- the slices read
  have eLD : ∀ z < 64, σ (.n ((val% «verify_keccak» "level[0]") + z)) = slices.getD z 0 := fun z hz ↦
    load_val (gA _ (mLD _ (List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩)))
      (not_mem_of_noneIn k1 _ (List.mem_append_right _ (List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩)))
      (by rw [List.getD_eq_getElem _ _ (by omega)]; exact hsl z (by omega))
  -- the shifts
  have FT : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkFinFT next kret :=
    fun hn ↦ loads_complete k6 hσ (fun st h ↦ hg st (mFT st h)) k8 k9 (fun q hq off h1 h2 ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      simp only at h2 ⊢
      rw [e5212]; exact ⟨_, hloc off (by omega)⟩) hn
  obtain ⟨hsh, -⟩ := foldT_holds (A := loc.take 6) (S := fun z ↦ slices.getD z 0)
    (by simp [hlocL]) (fun t ht v hv ↦ by
      rw [e5212] at hv
      rw [List.getD_eq_getElem _ _ (by simp [hlocL]; omega), List.getElem_take]
      exact loadHolds_unique hv (hloc t (by omega)))
    eLD (FT (next := True) (kret := fun _ ↦ True) trivial)
  -- `keccak_form`
  have FA : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkFinFA next kret :=
    fun hn ↦ loads_complete k10 hσ (fun st h ↦ hg st (mFA st h)) k12 k13 (fun q hq off h1 h2 ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      simp only at h2 ⊢
      rw [e6363]; exact ⟨_, hlanes off (by omega)⟩) hn
  obtain ⟨hform, -⟩ := formAll_holds (by rw [e6363]; exact hlanes) hlen
    (FA (next := True) (kret := fun _ ↦ True) trivial)
  rw [k14] at hform
  have hform' : σ (.n (val% «verify_keccak» "total@30")) = formVal (fun l ↦ ∑ m ∈ range 2,
        eqAt [point.getD (τ - 4) 0] m * eqAt slotI (25 * (0 + m) + l)) (kLane lanes)
        (fun r ↦ ∑ z ∈ range 64, slices.getD z 0 * eqAt (loc.take 6) ((z + r) % 64)) := by
    rw [hform]
    refine formVal_congr (fun l hl ↦ ?_) (fun l hl ↦ ⟨hsh _ (rho_used l hl).1, hsh _ (rho_used l hl).2⟩)
    rw [hlw l hl, hrs', hr']
  -- the check, the copy loop, the return
  have m6578 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n (val% «verify_keccak» "s79#1")) (.n (val% «verify_keccak» "mu_at_low@16")) (.n (val% «verify_keccak» "total@30"))) (by rw [← k14]; simp [vkFinT]))
  have e6578 : σ (.n (val% «verify_keccak» "s79#1")) = σ (.n (val% «verify_keccak» "in_value")) := by rw [m6578, hform', hchk]
  have c6579 : σ (.n (val% «verify_keccak» "s81#0")) = word 1 0 := gA (.const (.n (val% «verify_keccak» "s81#0")) (word 1 0)) (by simp [vkFinT])
  have a6580 : σ (.n (val% «verify_keccak» "s81#1")) = σ (.n (val% «verify_keccak» "s81#0")) + σ (.n (val% «verify_keccak» "pack_g")) :=
    gA (.add (.n (val% «verify_keccak» "s81#1")) (.n (val% «verify_keccak» "s81#0")) (.n (val% «verify_keccak» "pack_g"))) (by simp [vkFinT])
  have c6581 : σ (.n (val% «verify_keccak» "s81#2")) = word 1 0 := gA (.const (.n (val% «verify_keccak» "s81#2")) (word 1 0)) (by simp [vkFinT])
  have c6582 : σ (.n (val% «verify_keccak» "s81#3")) = word 16 0 :=
    gA (.const (.n (val% «verify_keccak» "s81#3")) (word 16 0)) (by simp [vkFinT])
  have m6583 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n (val% «verify_keccak» "s81#4")) (.n (val% «verify_keccak» "fs0@15~11")) (.n (val% «verify_keccak» "s81#3"))) (by simp [vkFinT]))
  have ecp : ∀ j < 5, σ (.n ((val% «verify_keccak» "s82#0") + j)) = σ (.n ((val% «verify_keccak» "nxt[8]@22") + j)) := fun j hj ↦
    hg _ (mCP _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  have c6589 : σ (.n (val% «verify_keccak» "s82#1")) = word 27 0 := gA (.const (.n (val% «verify_keccak» "s82#1")) (word 27 0)) (by simp [vkFinT])
  have m6590 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n (val% «verify_keccak» "s82#2")) (.n (val% «verify_keccak» "cursor@16")) (.n (val% «verify_keccak» "s82#1"))) (by simp [vkFinT]))
  have e6591 : σ (.n (val% «verify_keccak» "s82#0[5]")) = σ (.n (val% «verify_keccak» "s82#2")) := gA (.copy (.n (val% «verify_keccak» "s82#0[5]")) (.n (val% «verify_keccak» "s82#2"))) (by simp [vkFinT])
  have e6592 : σ (.n (val% «verify_keccak» "s82#0[6]")) = σ (.n (val% «verify_keccak» "x@2")) := gA (.copy (.n (val% «verify_keccak» "s82#0[6]")) (.n (val% «verify_keccak» "x@2"))) (by simp [vkFinT])
  have e6580 : σ (.n (val% «verify_keccak» "s81#1")) = 1 + σ (.n (val% «verify_keccak» "pack_g")) := by rw [a6580, c6579, word_one]
  refine ⟨e4977, e6580, by rw [c6581, word_one], by rw [m6583, c6582, word_16, h1251, mul_assoc, ← pow_add],
    fun {kret} hk ↦ ?_⟩
  rw [vkFinT]
  simp only [holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨by rw [e4977]; exact hpp, m4978, SL ⟨by rw [e5212]; exact hlc, ?_⟩⟩
  rw [holdsList_map_atoms]
  refine ⟨fun z hz ↦ ?_, FT ⟨by rw [e6363]; exact hlp, FA ?_⟩⟩
  · show LoadHolds rd (σ (.n (val% «verify_keccak» "slices"))) z (σ (.n (1976 + z)))
    rw [eLD z hz, List.getD_eq_getElem _ _ (by omega)]; exact hsl z (by omega)
  rw [k14]
  refine ⟨m6578, by rw [e6578]; exact e_add_self _, c6579, a6580, c6581, c6582, m6583,
    by rw [e6580, h17]; exact one_add_gen_pow_inK _, fun _ ↦ trivial, ?_⟩
  rw [holdsList_map_atoms]
  refine ⟨fun j hj ↦ ecp j hj, ?_⟩
  simp only [List.map_cons, List.map_nil]
  refine ⟨c6589, m6590, e6591, e6592, ?_⟩
  convert hk using 1
  rw [ecp 0 (by omega), ecp 1 (by omega), ecp 2 (by omega), ecp 3 (by omega), ecp 4 (by omega),
    e6591, m6590, c6589, word_g64, e6592]

end
end LeanVM.Guest.B1.VerifySub
