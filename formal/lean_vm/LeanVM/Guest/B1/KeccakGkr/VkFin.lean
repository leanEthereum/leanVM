/-
  LeanVM.Guest.B1.KeccakGkr.VkFin

  `verify_keccak`'s inputs' check, the copy of their pack coordinates, the return
 .
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkIn
public import LeanVM.Guest.B1.KeccakGkr.FoldT
public import LeanVM.Guest.B1.KeccakGkr.LayerWeight0

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {rd : Reader} {σ : Val}

set_option maxRecDepth 100000 in
theorem word_g64 : word 27 0 = gen ^ 64 := by
  rw [word_eOfNat, gen_pow_eq_ofK, ← gpowK_eq (by unfold u128Bound; omega)]
  show ofK (K.ofBits 27) = ofK (gpowK 64)
  congr 1

/-- **The inputs' check and the return**. -/
theorem vkFinT_holds {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h17 : σ (.n 18) = gen ^ (τ - 4))
    {c : KeccakClaim} (hc : ClaimRec rd ((0 : ℕ) = 1) (σ (.n 161) * gen ^ (22 * 12)) c (τ - 3))
    {slotI : List E} (hsl : slotI.length = 6) (hslR : ReadsAt rd (σ (.n 1330)) slotI)
    {S : ℕ → E} (hS : ∀ z < 64, LoadHolds rd (σ (.n 10)) z (S z))
    (h1251 : σ (.n 1202) = σ (.n 9) * gen ^ 39)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vkFinT next kret) :
    ∃ (lanes loc : List E), lanes.length = 25 ∧ loc.length = 11 ∧
      c.weights = laterWeights lanes (eqKernel (loc.take 6)) ∧
      σ (.n 1327) * formVal (fun l ↦ σ (.n (slotLaneV 1747 2 l))) (kLane lanes)
        (fun r ↦ σ (.n (vkSh r))) = σ (.n 1339) ∧
      (∀ lane < 25, σ (.n (slotLaneV 1747 2 lane)) = ∑ m ∈ range 2,
        eqAt [c.point.getD (τ - 4) 0] m * eqAt slotI (25 * (0 + m) + lane)) ∧
      (∀ r ∈ shiftUsed, σ (.n (vkSh r)) = ∑ z ∈ range 64, S z * eqAt (loc.take 6) ((z + r) % 64)) ∧
      (∀ j < τ - 4, ∃ (pp v : E), LoadHolds rd (σ (.n 161) * gen ^ (22 * 12)) 2 pp ∧
        LoadHolds rd pp j v ∧ LoadHolds rd (σ (.n 9) * gen ^ 43) j v) ∧
      kret [σ (.n 1740), σ (.n 1741), σ (.n 1742), σ (.n 1743), σ (.n 1744),
        σ (.n 1338) * gen ^ 64, σ (.n 931)] := by
  obtain ⟨-, hptL, -, -, -, ⟨pp, hpp, hpt⟩, lp, lanes, hlp, hlen, hlanes, hrest⟩ := hc
  simp only [show ((0 : ℕ) = 1) = False by decide, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hrest
  obtain ⟨lc, sl, loc, hlc, hlocL, hloc, -, -, hw⟩ := hrest
  rw [vkFinT] at h
  generalize hSLT : slotLanesT 1330 1746 1747 0 2 = SLT at h
  generalize hLD : (List.range 64).map (fun z ↦ Stmt.atom (.load (.n (1981 + z)) (.n 10) z)) = LD at h
  generalize hFT : foldT (fun j ↦ 1981 + j) 2045 (.n 1980) = FT at h
  generalize hFA : formAll (.n 3143) vkSh (slotLaneV 1747 2) 3144 = FA at h
  generalize hCP : (List.range 5).map (fun j ↦ Stmt.atom (.copy (.n (3364 + j)) (.n (1740 + j)))) = CP at h
  simp only [holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil] at h
  obtain ⟨l4977, e4978, h⟩ := h
  have epp : σ (.n 1745) = pp := loadHolds_unique l4977 (by
    have := (loadHolds_mul_gen_pow rd _ _ _ _).1 hpp; simpa using this)
  -- the slot's lane weights
  rw [← hSLT] at h
  obtain ⟨rs, hrsL, hrs, r, hr, hlw, h⟩ := slotLanesT_holds (Or.inr rfl) (by norm_num) h
  have hrs' : rs = slotI := by
    apply List.ext_getElem (by rw [hrsL, hsl])
    intro k h1 h2
    exact loadHolds_unique (hrs k h1) (hslR k h2)
  have hr' : r = c.point.getD (τ - 4) 0 := by
    rw [e4978, epp, h17, loadHolds_mul_gen_pow] at hr
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique hr (by simpa using hpt (τ - 4) (by omega))
  -- the shifts of the slices
  obtain ⟨l5212, h⟩ := h
  have elc : σ (.n 1980) = lc := loadHolds_unique l5212 (by
    have := (loadHolds_mul_gen_pow rd _ _ _ _).1 hlc; simpa using this)
  rw [← hLD, holdsList_map_atoms] at h
  obtain ⟨hld, h⟩ := h
  simp only [Atom.Holds] at hld
  rw [← hFT] at h
  obtain ⟨hsh, h⟩ := foldT_holds (A := loc.take 6) (S := S) (by simp [hlocL, keccakLocalBits])
    (fun t ht v hv ↦ by
      rw [elc] at hv
      rw [List.getD_eq_getElem _ _ (by simp [hlocL, keccakLocalBits]; omega), List.getElem_take]
      exact loadHolds_unique hv (hloc t (by simp [keccakLocalBits] at hlocL; omega)))
    (fun j hj ↦ loadHolds_unique (hld j hj) (hS j hj)) h
  -- keccak_form
  obtain ⟨l6363, h⟩ := h
  have elp : σ (.n 3143) = lp := loadHolds_unique l6363 (by
    have := (loadHolds_mul_gen_pow rd _ _ _ _).1 hlp; simpa using this)
  rw [← elp] at hlanes
  rw [← hFA] at h
  obtain ⟨hform, h⟩ := formAll_holds hlanes hlen h
  obtain ⟨e6578, heq, c79, e80, c81, c82, e83, -, hcall13, h⟩ := h
  rw [← hCP, holdsList_map_atoms] at h
  obtain ⟨hcp, c89, e90, e91, e92, hret⟩ := h
  simp only [Atom.Holds] at hcp
  refine ⟨lanes, loc, hlen, by simpa [keccakLocalBits] using hlocL, hw, ?_, fun lane hl ↦ ?_,
    fun r hr ↦ hsh r hr, fun j hj ↦ ?_, ?_⟩
  · rw [← eq_of_add_eq_zero' heq, e6578, hform]
  · rw [hlw lane hl, hrs', hr']
  · have hne : 1 + σ (.n 18) ≠ 0 := by
      rw [h17]; exact gen_pow_ne_one (by omega) (by unfold ordG; omega)
    have hcall := hcall13 (by rw [e80, c79, word_one]; exact hne)
    simp only [c81, e83, c82, word_one, word_16, epp, h1251, mul_assoc, ← pow_add] at hcall
    obtain ⟨v, h1, h2⟩ := copyLoop_sound find_copyLoop13 copyLoop_body13 rfl h17
      (by unfold ordG; omega) hcall j hj
    exact ⟨pp, v, hpp, h1, h2⟩
  · convert hret using 1
    simp only [e92, e91, e90, c89, word_g64]
    rw [hcp 0 (by omega), hcp 1 (by omega), hcp 2 (by omega), hcp 3 (by omega), hcp 4 (by omega)]

end
end LeanVM.Guest.B1.VerifySub
