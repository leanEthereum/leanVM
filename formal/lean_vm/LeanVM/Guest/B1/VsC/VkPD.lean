/-
  LeanVM.Guest.B1.VsC.VkPD

  `verify_keccak` placed: the twelve steps on the layout (the archive's `VkCN`, `VkCT`'s steps).
-/

module

public import LeanVM.Guest.B1.VsC.VkPC
public import LeanVM.Guest.B1.VsC.VkCF
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The steps, on the layout

`step_on`: step `s` holds on a memory holding the layout, from claim `s`'s record (`recs`), its
`ι` term the claim's; `steps_chain`: the claim records' pointers the steps pass on;
`steps_holds`: the twelve steps.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL

@[expose] public section

theorem mem_steps : ∀ s < 12, ∀ st ∈ stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s),
    st ∈ vkStepsT := by
  intro s hs st hst
  rw [vkStepsT]
  simp only [List.mem_append]
  interval_cases s <;> simp only [stepB, stepCap, stepCur, stepCb, stepPn] at hst <;> tauto

theorem step_bounds : ∀ s < 12, 157 ≤ stepT0 s (stepB s) ∧ 19 ≤ stepB s ∧
    stepCb s < stepT0 s (stepB s) ∧ stepPn s < stepT0 s (stepB s) := by decide +kernel

theorem stepCb_eq : ∀ s < 12, 2 ≤ s → stepCb s = stepPn (s - 1) := by decide

theorem stepPn_eq : ∀ s < 11,
    stepPn (s + 1) = stepT0 s (stepB s) + (if s = 0 then 5 else 7) := by decide +kernel

namespace VkData

variable {D : VkData} {rd : Reader} {c curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}

set_option maxRecDepth 20000 in
/-- **Step `s`, on the layout**: from the claim records' pointers it reads (`cb`: claim `s`'s,
`pn`: claim `s + 1`'s, as the step before computed them). -/
theorem step_on (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) {s : ℕ} (hs : s < 12)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4))
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201))
    (h274 : σ (.n (val% «verify_keccak» "lane_tree")) = VsC.ptrAtV (c + D.o274))
    (hcb : 1 ≤ s → σ (.n (stepCb s)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * (s - 1)))
    (hpn : 1 ≤ s → σ (.n (stepPn s)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * s)) :
    σ (.n (stepT0 s (stepB s) - 1)) = keccakIota D.τ s (D.layer s).c ∧
    (s = 0 → σ (.n (stepT0 s (stepB s) + 1)) = σ (.n (val% «verify_keccak» "cursor@1")) * gen ∧
      σ (.n (stepT0 s (stepB s) + 3)) = gen ^ (D.τ - 3) ∧
      σ (.n (stepT0 s (stepB s) + 5)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * 1)) ∧
    (s ≠ 0 → σ (.n (stepT0 s (stepB s))) = 0 ∧ σ (.n (stepT0 s (stepB s) + 1)) = 0 ∧
      σ (.n (stepT0 s (stepB s) + 3)) = gen ^ (D.τ - 3) ∧
      σ (.n (stepT0 s (stepB s) + 5)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * s) ∧
      σ (.n (stepT0 s (stepB s) + 7)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * (s + 1))) ∧
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ
        (stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s)) next kret := by
  have hτ1 := h.1
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hg : ∀ st ∈ stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s),
      GoodS rd vkSt (D.w c curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mem_steps s hs st hst)))))
  rw [stepT_split] at hg ⊢
  have hgC : ∀ st ∈ stepCore s (stepB s), GoodS rd vkSt (D.w c curE) σ st :=
    fun st hst ↦ hg st (List.mem_append_left _ hst)
  have hgT := fun st hst ↦ hg st (List.mem_append_right _ hst)
  obtain ⟨hbT, hbB, hcbT, hpnT⟩ := step_bounds s hs
  -- the claim's record
  have hcr := recs h hm s hs.le
  rw [← ptr_mul_gen, ← h201] at hcr
  have hyL : (D.layer s).y = D.τ - 3 := D.layer_y h (by omega)
  obtain ⟨-, hptL, -, -, -, ⟨pp, hpp, hpt⟩, lp, lanes, hlp, hlen, hlanes, hrest⟩ := hcr
  have hpp' := (loadHolds_mul_gen_pow rd _ _ _ _).1 hpp
  -- the flips
  obtain ⟨hF, HF⟩ : (∀ i ∈ iotaUsed s, σ (.n (flipOf s (stepB s + 6) i)) =
        (D.layer s).c.weights.getD (2 ^ i - 1) 0) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (flipsT s (stepB s + 6)) next kret := by
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · obtain ⟨-, -, -, -, -, -, m274, -, -⟩ := own_mem hm.own
      have hL0 : LoadHolds rd (σ (.n (val% «verify_keccak» "lane_tree"))) 30 ((eqKernel D.rl).getD 0 0) := by
        rw [h274]
        have := lanes_first m274 0 (by simp [eqKernel_length, rl_length])
        rw [← ptr_mul_gen, loadHolds_mul_gen_pow] at this
        rw [List.getD_eq_getElem _ _ (by simp [eqKernel_length, rl_length])]
        simpa using this
      exact flips0_complete hσ hgC (step_ker 0 (by norm_num)) hL0 fun z hz ↦ by
        rw [layer_zero_c, c0, vkFirst_weights _ _ _ _ _ (by omega), Nat.div_eq_of_lt hz,
          Nat.mod_eq_of_lt hz, ← gen_pow_eq_eOfNat hz]
    · have hd : decide (s = 0) = false := by simp; omega
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hrest
      obtain ⟨-, fl, -, -, -, -, hfl, hflR, -⟩ := hrest
      exact flipsL_complete (by omega) hσ hgC (step_ker s hs)
        ((loadHolds_mul_gen_pow rd _ _ _ _).1 hfl) hflR
  -- the core
  obtain ⟨hio, HC⟩ := stepCore_of_flips hs hbB hσ hgC (step_ker s hs) hτ1 h17 hpp' hpt
    (by rw [hptL]) hF HF
  refine ⟨hio, fun hs0 ↦ ?_, fun hs0 ↦ ?_, fun {next kret} hn ↦ ?_⟩
  · subst hs0
    obtain ⟨e1, e3, e5, -⟩ := tail0_complete hbT hgT h17 (by omega)
    exact ⟨e1, e3, e5⟩
  · obtain ⟨e0, e1, e3, e5, e7, -⟩ := tailL_complete (by omega) (by omega) hcbT hpnT hgT h17
      (by omega)
    refine ⟨e0, e1, e3, ?_, ?_⟩
    · rw [e5, hcb (by omega), mul_assoc, ← pow_add]; congr 2; omega
    · rw [e7, hpn (by omega), mul_assoc, ← pow_add]; congr 2
  · rw [holdsList_append]
    refine HC ?_
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · exact (tail0_complete hbT hgT h17 (by omega)).2.2.2 hn
    · exact (tailL_complete (by omega) (by omega) hcbT hpnT hgT h17 (by omega)).2.2.2.2.2 hn

/-- **The claim records' pointers the steps pass on**: step `s ≥ 1` reads claim `s`'s at
`stepCb s` and claim `s + 1`'s at `stepPn s`, as the step before computed them. -/
theorem steps_chain (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4))
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201))
    (h274 : σ (.n (val% «verify_keccak» "lane_tree")) = VsC.ptrAtV (c + D.o274)) :
    ∀ s, s < 12 → 1 ≤ s → σ (.n (stepCb s)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * (s - 1)) ∧
      σ (.n (stepPn s)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * s)
  | 0, _, h1 => absurd h1 (by norm_num)
  | 1, _, _ => by
    refine ⟨by simp [stepCb], ?_⟩
    rw [stepPn_eq 0 (by norm_num)]
    exact ((step_on h hm hσd (s := 0) (by norm_num) h17 h201 h274 (fun h ↦ absurd h (by norm_num))
      (fun h ↦ absurd h (by norm_num))).2.1 rfl).2.2
  | k + 2, hs, _ => by
    have IH := steps_chain h hm hσd h17 h201 h274 (k + 1) (by omega) (by omega)
    refine ⟨by rw [stepCb_eq (k + 2) hs (by omega)]; exact IH.2, ?_⟩
    rw [stepPn_eq (k + 1) (by omega)]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    exact ((step_on h hm hσd (s := k + 1) (by omega) h17 h201 h274 (fun _ ↦ IH.1)
      (fun _ ↦ IH.2)).2.2.1 (by omega)).2.2.2.2

/-- **Step `s`'s facts, on the layout**, its claim records' pointers discharged. -/
theorem step_on' (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) {s : ℕ} (hs : s < 12)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4))
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201))
    (h274 : σ (.n (val% «verify_keccak» "lane_tree")) = VsC.ptrAtV (c + D.o274)) :
    σ (.n (stepT0 s (stepB s) - 1)) = keccakIota D.τ s (D.layer s).c ∧
    (s = 0 → σ (.n (stepT0 s (stepB s) + 1)) = σ (.n (val% «verify_keccak» "cursor@1")) * gen ∧
      σ (.n (stepT0 s (stepB s) + 3)) = gen ^ (D.τ - 3) ∧
      σ (.n (stepT0 s (stepB s) + 5)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * 1)) ∧
    (s ≠ 0 → σ (.n (stepT0 s (stepB s))) = 0 ∧ σ (.n (stepT0 s (stepB s) + 1)) = 0 ∧
      σ (.n (stepT0 s (stepB s) + 3)) = gen ^ (D.τ - 3) ∧
      σ (.n (stepT0 s (stepB s) + 5)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * s) ∧
      σ (.n (stepT0 s (stepB s) + 7)) = σ (.n (val% «verify_keccak» "claims")) * gen ^ (22 * (s + 1))) ∧
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ
        (stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s)) next kret :=
  step_on h hm hσd hs h17 h201 h274
    (fun h1 ↦ (steps_chain h hm hσd h17 h201 h274 s hs h1).1)
    (fun h1 ↦ (steps_chain h hm hσd h17 h201 h274 s hs h1).2)

/-- **The twelve steps, on the layout.** -/
theorem steps_holds (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4))
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201))
    (h274 : σ (.n (val% «verify_keccak» "lane_tree")) = VsC.ptrAtV (c + D.o274))
    {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkStepsT next kret := by
  have S : ∀ s, s < 12 → ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ
        (stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s)) next kret :=
    fun s hs ↦ (step_on' h hm hσd hs h17 h201 h274).2.2.2
  rw [vkStepsT]
  simp only [holdsList_append]
  exact S 0 (by norm_num) (S 1 (by norm_num) (S 2 (by norm_num) (S 3 (by norm_num)
    (S 4 (by norm_num) (S 5 (by norm_num) (S 6 (by norm_num) (S 7 (by norm_num)
    (S 8 (by norm_num) (S 9 (by norm_num) (S 10 (by norm_num) (S 11 (by norm_num) hn)))))))))))

end VkData

end
end LeanVM.Guest.B1.VerifySub
