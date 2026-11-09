/-
  LeanVM.Guest.B1.KeccakGkr.VkOpenMath

  The openings of `q_keccak` in `verifyKeccak` (V:2043-2053): the folded slot weights through the
  slots' lane weights.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkSpec
public import LeanVM.Guest.B1.KeccakGkr.KFormMath
public import LeanVM.Guest.B1.KeccakGkr.FormT
public import LeanVM.Protocol.Whir.Complete.Tables

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Complete Finset

@[expose] public section

/-- The slot weights summed along the slot's equality weights, through the lanes. -/
theorem slotW_sum (segs w slot : List E) {first count : ℕ}
    (hc : (first = 1 ∧ count = 1) ∨ (first = 0 ∧ count = 2)) {z : ℕ} (hz : z < 64) :
    ∑ o ∈ range 64, eqAt slot o * slotW segs w first count o z =
      ∑ lane ∈ range 25, (∑ m ∈ range count, segs.getD m 0 * eqAt slot (25 * (first + m) + lane)) *
        w.getD (64 * lane + z) 0 := by
  rw [show (64 : ℕ) = 25 + (25 + 14) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h1 : ∑ x ∈ range 25, eqAt slot x * slotW segs w 1 1 x z = 0 :=
      Finset.sum_eq_zero fun x hx ↦ by
        have := Finset.mem_range.1 hx
        simp [slotW, show ¬ (25 ≤ x) by omega]
    have h3 : ∑ x ∈ range 14, eqAt slot (25 + (25 + x)) * slotW segs w 1 1 (25 + (25 + x)) z = 0 :=
      Finset.sum_eq_zero fun x hx ↦ by
        simp [slotW, show ¬ (25 + (25 + x) < 50) by omega]
    rw [h1, h3, zero_add, add_zero]
    refine Finset.sum_congr rfl fun lane hl ↦ ?_
    have := Finset.mem_range.1 hl
    simp only [slotW, show 25 * 1 ≤ 25 + lane by omega, show 25 + lane < 25 * (1 + 1) by omega,
      hz, and_self, ↓reduceIte, show (25 + lane) / 25 - 1 = 0 by omega,
      show (25 + lane) % 25 = lane by omega, Finset.sum_range_one, Nat.add_zero,
      show 25 * (1 + 0) + lane = 25 + lane by omega]
    ring
  · have h3 : ∑ x ∈ range 14, eqAt slot (25 + (25 + x)) * slotW segs w 0 2 (25 + (25 + x)) z = 0 :=
      Finset.sum_eq_zero fun x hx ↦ by
        simp only [slotW]
        rw [ite_eq_right_iff.2 (fun h ↦ absurd h.2.1 (by omega)), mul_zero]
    rw [h3, add_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun lane hl ↦ ?_
    have := Finset.mem_range.1 hl
    simp only [slotW, show 25 * 0 ≤ lane by omega, show lane < 25 * (0 + 2) by omega,
      show 25 * 0 ≤ 25 + lane by omega, show 25 + lane < 25 * (0 + 2) by omega,
      hz, and_self, ↓reduceIte, show lane / 25 - 0 = 0 by omega, show lane % 25 = lane by omega,
      show (25 + lane) / 25 - 0 = 1 by omega, show (25 + lane) % 25 = lane by omega,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      show 25 * (0 + 0) + lane = lane by omega, show 25 * (0 + 1) + lane = 25 + lane by omega]
    ring

/-- **An opening's weight at slice `z`** (V:2043-2053). -/
theorem openWeights_getD (τ : ℕ) (c : KeccakClaim) {first count : ℕ}
    (hc : (first = 1 ∧ count = 1) ∨ (first = 0 ∧ count = 2)) (slot : List E)
    (hs : slot.length = 6) {z : ℕ} (hz : z < 64) :
    ((foldAll slot (keccakSlotWeights τ c first count)).headD []).getD z 0 =
      ∑ lane ∈ range 25, (∑ m ∈ range count, (eqKernel (c.point.drop (τ - 4))).getD m 0 *
        eqAt slot (25 * (first + m) + lane)) * c.weights.getD (64 * lane + z) 0 := by
  have hfc : first + count ≤ 2 := by omega
  obtain ⟨-, -, hf⟩ := foldAll_eq slot (keccakSlotWeights τ c first count)
    (by rw [slotWeights_length _ _ _ _ hfc, hs]; rfl)
    (fun o ho ↦ slotWeights_row_length _ _ _ _ hfc (by rwa [slotWeights_length _ _ _ _ hfc] at ho))
  rw [hf z hz, hs, show (2 : ℕ) ^ 6 = 64 from rfl]
  rw [← slotW_sum _ _ slot hc hz]
  refine Finset.sum_congr rfl fun o ho ↦ ?_
  rw [slotWeights_getD _ _ _ _ hfc (Finset.mem_range.1 ho)]

/-- The multilinear extension of `2^4` values at four coordinates. -/
theorem multilinearEval_eqAt (t p : List E) (ht : t.length = 16) (hp : p.length = 4) :
    multilinearEval t p = ∑ i ∈ range 16, eqAt p i * t.getD i 0 := by
  rw [multilinearEval_eq_sum 4 t p ht hp]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [← hp, ← getD_eqKernel p i (by rw [hp]; exact Finset.mem_range.1 hi), eqKernel_getD]
  simp only [hp, show i < 2 ^ 4 from Finset.mem_range.1 hi, ↓reduceIte]
  ring

end
end LeanVM.Guest.B1.VerifySub
