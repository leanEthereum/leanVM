/-
  LeanVM.Guest.B1.KeccakGkr.VkChecks

  `verifyKeccak`'s two opening checks (V:2079, 2086) from the guest's.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkFin

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

theorem headD_eq_getD (l : List E) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem vkFirst_weights (inst outs : List E) (comm : E) (seg rl : List E) {z : ℕ} (hz : z < 1600) :
    (vkFirst inst outs comm seg rl).weights.getD z 0 =
      (eqKernel rl).getD (z / 64) 0 * eOfNat (2 ^ (z % 64)) := by
  rw [vkFirst, List.getD_eq_getElem _ _ (by simp [keccakBits]; omega), List.getElem_map,
    List.getElem_range]

theorem point_drop (p : List E) {τ : ℕ} (hτ : 4 ≤ τ) (hp : p.length = τ - 3) :
    p.drop (τ - 4) = [p.getD (τ - 4) 0] := by
  rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
  simp [show τ - 4 + 1 = p.length by omega]

theorem eqKernel_one (r : E) {m : ℕ} (hm : m < 2) : (eqKernel [r]).getD m 0 = eqAt [r] m := by
  rw [eqKernel_getD]; simp [hm]

/-- **The committed outputs' check** (V:2079): the guest's lanes sum times the word. -/
theorem vk_out_check {τ : ℕ} (inst outs : List E) (comm : E) (r0 : E) (rl : List E)
    (hinst : (inst.drop 4).length = τ - 4) {slotO : List E} (hs : slotO.length = 6) {word v : E}
    (h : (∑ lane ∈ range 25, (∑ m ∈ range 1, eqAt [r0] m * eqAt slotO (25 * (1 + m) + lane)) *
      (eqKernel rl).getD lane 0) * word = v) :
    ((foldAll slotO (keccakSlotWeights τ (vkFirst inst outs comm [r0] rl) 1 1)).headD []).headD 0 *
      word = v := by
  rw [headD_eq_getD, openWeights_getD τ _ (Or.inl ⟨rfl, rfl⟩) slotO hs (by norm_num)]
  rw [← h]
  refine congrArg (· * word) (Finset.sum_congr rfl fun lane hl ↦ ?_)
  have hl' := Finset.mem_range.1 hl
  have hpd : (vkFirst inst outs comm [r0] rl).point.drop (τ - 4) = [r0] := by
    simp only [vkFirst, List.drop_append_of_le_length (by omega : τ - 4 ≤ (inst.drop 4).length),
      List.drop_eq_nil_of_le (by omega : (inst.drop 4).length ≤ τ - 4), List.nil_append]
  rw [hpd, vkFirst_weights _ _ _ _ _ (by omega), show (64 * lane + 0) / 64 = lane by omega,
    show (64 * lane + 0) % 64 = 0 by omega, pow_zero, Value.eOfNat_one, mul_one]
  refine congrArg (· * _) (Finset.sum_congr rfl fun m hm ↦ ?_)
  rw [eqKernel_one r0 (by have := Finset.mem_range.1 hm; omega)]

/-- **The inputs' check** (V:2086): the guest's `μ(low)·keccak_form(...)`. -/
theorem vk_in_check {τ : ℕ} (hτ : 4 ≤ τ) {c : KeccakClaim} (hpt : c.point.length = τ - 3)
    {lanes loc : List E} (hlocL : loc.length = 11)
    (hw : c.weights = laterWeights lanes (eqKernel (loc.take 6))) {slotI : List E}
    (hs : slotI.length = 6) {slices : List E} (hsl : slices.length = 64) {F Sh : ℕ → E}
    (hF : ∀ lane < 25, F lane = ∑ m ∈ range 2,
      eqAt [c.point.getD (τ - 4) 0] m * eqAt slotI (25 * (0 + m) + lane))
    (hSh : ∀ r ∈ shiftUsed, Sh r = ∑ z ∈ range 64, slices.getD z 0 * eqAt (loc.take 6) ((z + r) % 64))
    {μ v : E} (h : μ * formVal F (kLane lanes) Sh = v) :
    μ * dot ((foldAll slotI (keccakSlotWeights τ c 0 2)).headD []) slices = v := by
  rw [← h]
  refine congrArg (μ * ·) ?_
  obtain ⟨-, hWl, -⟩ := foldAll_eq slotI (keccakSlotWeights τ c 0 2)
    (by rw [slotWeights_length _ _ _ _ (by norm_num), hs]; rfl)
    (fun o ho ↦ slotWeights_row_length _ _ _ _ (by norm_num)
      (by rwa [slotWeights_length _ _ _ _ (by norm_num)] at ho))
  have h6 : (loc.take 6).length = 6 := by simp [hlocL]
  rw [dot_eq _ _ (by rw [hWl, hsl]), hWl]
  rw [Finset.sum_congr rfl fun z hz ↦ by
    rw [openWeights_getD τ c (Or.inr ⟨rfl, rfl⟩) slotI hs (Finset.mem_range.1 hz)]]
  rw [Finset.sum_congr rfl fun z _ ↦ Finset.sum_mul (range 25) _ _, Finset.sum_comm]
  have hgen := later_dot_gen (loc.take 6) lanes h6
    (fun lane ↦ ∑ m ∈ range 2, (eqKernel (c.point.drop (τ - 4))).getD m 0 *
      eqAt slotI (25 * (0 + m) + lane)) (fun z ↦ slices.getD z 0)
  rw [← hw] at hgen
  rw [show ∑ y ∈ range 25, ∑ x ∈ range 64, (∑ m ∈ range 2, (eqKernel (c.point.drop (τ - 4))).getD m 0 *
      eqAt slotI (25 * (0 + m) + y)) * c.weights.getD (64 * y + x) 0 * slices.getD x 0 =
      ∑ l ∈ range 25, ∑ z ∈ range 64, (∑ m ∈ range 2, (eqKernel (c.point.drop (τ - 4))).getD m 0 *
      eqAt slotI (25 * (0 + m) + l)) * slices.getD z 0 * c.weights.getD (64 * l + z) 0 from
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring, hgen]
  refine formVal_congr (fun l hl ↦ ?_) (fun l hl ↦ ⟨?_, ?_⟩)
  · rw [hF l hl, point_drop c.point hτ hpt]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [eqKernel_one _ (Finset.mem_range.1 hm)]
  · rw [hSh _ (rho_used l hl).1]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  · rw [hSh _ (rho_used l hl).2]
    exact Finset.sum_congr rfl fun z _ ↦ by ring

end
end LeanVM.Guest.B1.VerifySub
