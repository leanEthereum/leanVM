/-
  LeanVM.Guest.B1.KeccakGkr.VkCN

  `verify_keccak`'s steps on its layout: the claim records in memory, each step holding.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCM

/-!
# The steps, on the layout

`CL_mem`: on a memory holding the layout, claim `s`'s record and buffers (`CL`) are in memory:
the first in `verify_keccak`'s buffers, the later ones in its claim records and the previous
layer's buffers. `mem_steps`: step `s`'s statements are the body's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

theorem mem_steps : ∀ s < 12, ∀ st ∈ stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s),
    st ∈ vkStepsT := by
  intro s hs st hst
  rw [vkStepsT]
  interval_cases s
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hst)))))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst))))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst))))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst))))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst))))
  · exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))
  · exact (List.mem_append_left _ (List.mem_append_right _ hst))
  · exact (List.mem_append_right _ hst)

namespace VkData

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}

theorem outWs_length (s : ℕ) : (D.outWs ls s).length = 22 := by
  simp [outWs, LayerData.outW, LayerData.next, layerClaim, keccakInstanceWeights_length]

theorem cw0_length (h : D.Ok) : (D.cw0 B).length = 22 := by simp [cw0, c0_mu h]

/-- Claim `s + 1`'s record, in the claim records. -/
theorem claims_slice (h : D.Ok) {k : ℕ} (hk : k < 12)
    (hc : ReadsAt rd (ptr (B + D.o201)) (D.claims B ls)) :
    ReadsAt rd (ptr (B + D.o201 + 22 * (k + 1))) (D.outWs ls k) := by
  rw [claims, flatMap_range_split _ hk] at hc
  have := readsAt_mid (A := D.cw0 B ++ (List.range k).flatMap (D.outWs ls))
    (by simpa only [List.append_assoc] using hc)
  rw [ptr_mul_gen, List.length_append, cw0_length h,
    flatMap_range_length _ (fun j _ ↦ outWs_length j)] at this
  rwa [show B + D.o201 + (22 + k * 22) = B + D.o201 + 22 * (k + 1) by ring] at this

/-- The first claim's record, in the claim records. -/
theorem claims_first (hc : ReadsAt rd (ptr (B + D.o201)) (D.claims B ls)) :
    ReadsAt rd (ptr (B + D.o201 + 22 * 0)) (D.cw0 B) :=
  (readsAt_append.1 hc).1

/-- The first claim's lanes, in the lane coordinates' tree. -/
theorem lanes_first (ht : ReadsAt rd (ptr (B + D.o274)) (eqLevels D.rl 5)) :
    ReadsAt rd (ptr (B + D.o274 + 30)) ((eqKernel D.rl).take 25) := by
  rw [eqLevels_succ] at ht
  have := (readsAt_append.1 ht).2
  rw [ptr_mul_gen, eqLevels_length (by rw [rl_length]; norm_num),
    show D.rl.take (4 + 1) = D.rl from List.take_of_length_le (by rw [rl_length])] at this
  intro k hk
  simp only [List.length_take, eqKernel_length, rl_length] at hk
  rw [List.getElem_take]
  exact this k (by simp [eqKernel_length, rl_length]; omega)

/-- **Claim `s`'s record and buffers, in memory.** -/
theorem CL_mem (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {s : ℕ} (hs : s < 12) :
    MemL rd ((D.CL B ls s).L (firstOf s) (D.layer s).c) := by
  obtain ⟨m58, -, m201, -, m274, -, -⟩ := own_mem (by have := h.1; omega) hm.own
  rcases s with _ | k
  · intro q hq
    simp only [CL, ClaimLay.L, firstOf, ↓reduceIte, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact claims_first m201
    · exact m58
    · exact lanes_first m274
  · have hk : k < 12 := by omega
    have hL := hm.lay k hk
    rw [layerBufs_eq] at hL
    have hc : (D.layer (k + 1)).c = (D.layer k).next (firstOf k) := by
      show (D.chain (k + 1)).1 = _
      rw [D.layer_succ h hk]
    intro q hq
    simp only [CL, ClaimLay.L, show firstOf (k + 1) = 0 from rfl, show (0 : ℕ) ≠ 1 by decide,
      ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl) | rfl | rfl
    · exact claims_slice h hk m201
    · rw [hc, show ((D.layer k).next (firstOf k)).point = (D.layer k).chs (firstOf k) from rfl]
      exact hL _ (by simp)
    · exact hL _ (by simp)
    · exact hL _ (by simp)
    · have hw := (D.CL_ok h B ls (s := k + 1) (by omega)).2.2.2.2.2.2.2.2.2
      simp only [show firstOf (k + 1) = 0 from rfl, zero_ne_one, ↓reduceIte] at hw
      rw [hw.2.2.2]
      exact hL _ (by simp [CL])

theorem step_bounds : ∀ s < 12, 162 ≤ stepT0 s (stepB s) ∧ 18 ≤ stepB s ∧
    stepCb s < stepT0 s (stepB s) ∧ stepPn s < stepT0 s (stepB s) := by decide +kernel

set_option maxRecDepth 20000 in
/-- **Step `s`, on the layout**: from the claim records' pointers it reads (`cb`: claim `s`'s,
`pn`: claim `s + 1`'s, as the step before computed them). -/
theorem step_on (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) {s : ℕ} (hs : s < 12)
    (h17 : σ (.n 18) = gen ^ (D.τ - 4))
    (h201 : σ (.n 161) = ptr (B + D.o201)) (h274 : σ (.n 234) = ptr (B + D.o274))
    (hcb : 1 ≤ s → σ (.n (stepCb s)) = σ (.n 161) * gen ^ (22 * (s - 1)))
    (hpn : 1 ≤ s → σ (.n (stepPn s)) = σ (.n 161) * gen ^ (22 * s)) :
    σ (.n (stepT0 s (stepB s) - 1)) = keccakIota D.τ s (D.layer s).c ∧
    (s = 0 → σ (.n (stepT0 s (stepB s) + 1)) = σ (.n 5) * gen ∧
      σ (.n (stepT0 s (stepB s) + 3)) = gen ^ (D.τ - 3) ∧
      σ (.n (stepT0 s (stepB s) + 5)) = σ (.n 161) * gen ^ (22 * 1)) ∧
    (s ≠ 0 → σ (.n (stepT0 s (stepB s))) = 0 ∧ σ (.n (stepT0 s (stepB s) + 1)) = 0 ∧
      σ (.n (stepT0 s (stepB s) + 3)) = gen ^ (D.τ - 3) ∧
      σ (.n (stepT0 s (stepB s) + 5)) = σ (.n 161) * gen ^ (22 * s) ∧
      σ (.n (stepT0 s (stepB s) + 7)) = σ (.n 161) * gen ^ (22 * (s + 1))) ∧
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ
        (stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s)) next kret := by
  have hτ1 := h.1
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hg : ∀ st ∈ stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s),
      GoodS rd vkSt (D.w B curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mem_steps s hs st hst)))))
  rw [stepT_split] at hg ⊢
  have hgC : ∀ st ∈ stepCore s (stepB s), GoodS rd vkSt (D.w B curE) σ st :=
    fun st hst ↦ hg st (List.mem_append_left _ hst)
  have hgT := fun st hst ↦ hg st (List.mem_append_right _ hst)
  obtain ⟨hbT, hbB, hcbT, hpnT⟩ := step_bounds s hs
  -- the claim's record
  have hcr := ClaimLay.claimRec (D.CL_ok h B ls hs.le) (CL_mem h hm hs)
  have hbc : (D.CL B ls s).bclaim = B + D.o201 + 22 * s := by cases s <;> rfl
  rw [hbc, ← ptr_mul_gen, ← h201] at hcr
  have hyL : (D.layer s).y = D.τ - 3 := D.layer_y h (by omega)
  obtain ⟨-, hptL, -, -, -, ⟨pp, hpp, hpt⟩, lp, lanes, hlp, hlen, hlanes, hrest⟩ := hcr
  have hpp' := (loadHolds_mul_gen_pow rd _ _ _ _).1 hpp
  -- the flips
  obtain ⟨hF, HF⟩ : (∀ i ∈ iotaUsed s, σ (.n (flipOf s (stepB s + 6) i)) =
        (D.layer s).c.weights.getD (2 ^ i - 1) 0) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (flipsT s (stepB s + 6)) next kret := by
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · obtain ⟨-, -, -, -, m274, -, -⟩ := own_mem (by omega) hm.own
      have hL0 : LoadHolds rd (σ (.n 234)) 30 ((eqKernel D.rl).getD 0 0) := by
        rw [h274]
        have := lanes_first m274 0 (by simp [eqKernel_length, rl_length])
        rw [← ptr_mul_gen, loadHolds_mul_gen_pow] at this
        rw [List.getD_eq_getElem _ _ (by simp [eqKernel_length, rl_length])]
        simpa using this
      exact flips0_complete hσ hgC (step_ker 0 (by norm_num)) hL0 fun z hz ↦ by
        rw [layer_zero_c, c0, vkFirst_weights _ _ _ _ _ (by omega), Nat.div_eq_of_lt hz,
          Nat.mod_eq_of_lt hz, ← gen_pow_eq_eOfNat hz]
    · have hf0 : firstOf s = 0 := by unfold firstOf; split <;> omega
      simp only [hf0, show (0 : ℕ) = 1 ↔ False by decide, decide_false, Bool.false_eq_true,
        ↓reduceIte] at hrest
      obtain ⟨-, fl, -, -, -, -, hfl, hflR, -⟩ := hrest
      exact flipsL_complete (by omega) hσ hgC (step_ker s hs)
        ((loadHolds_mul_gen_pow rd _ _ _ _).1 hfl) hflR
  -- the core
  obtain ⟨hio, HC⟩ := stepCore_of_flips hs hbB hσ hgC (step_ker s hs) hτ1 h17 hpp' hpt
    (by rw [hptL, hyL]) hF HF
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

end VkData

end
end LeanVM.Guest.B1.VerifySub
