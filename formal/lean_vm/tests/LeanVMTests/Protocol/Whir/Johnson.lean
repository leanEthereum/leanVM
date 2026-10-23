/-
  LeanVMTests.Protocol.Whir.Johnson

  The Johnson double count on a concrete set system, the interleaved Reed-Solomon bound on
  four points of `ZMod 5`, and the failure of the bound without the pairwise agreement bound.
-/

import LeanVM.Protocol.ToArkLib.Whir.Johnson
import Mathlib.Algebra.Field.ZMod

/-!
# Johnson bound controls

* The three sets `{0,1}, {1,2}, {2,3}` of `Fin 4` meet pairwise in at most one point:
  `(3·2)² = 36 ≤ 4 (3·2 + 3·2·1) = 48`.
* On four points of `ZMod 5` with `D = 1` (lines) and `η = 1/4`, `ρ₋ = 1/4`, ArkLib's Johnson
  threshold is `⌈(1/2 + 1/4) 4⌉₊ = 3` and every list has at most `1 / (2 · 1/4 · 1/2) = 4`
  members.
* **Negative control.** Without the pairwise agreement hypothesis the bound fails: five copies
  of the whole of `Fin 4` each have `(√(1/4) + 1/4) · 4 = 3` points, and `5 > 4`.
-/

namespace LeanVMTests.Protocol.Whir

open LeanVM.Protocol.Whir Finset ReedSolomon.HiddenDerivative

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private def chain : Fin 3 → Finset (Fin 4) := ![{0, 1}, {1, 2}, {2, 3}]

example : ((univ : Finset (Fin 3)).card * 2) ^ 2 ≤ Fintype.card (Fin 4) *
    ((univ : Finset (Fin 3)).card * 2 +
      (univ : Finset (Fin 3)).card * ((univ : Finset (Fin 3)).card - 1) * 1) :=
  johnson_count (univ : Finset (Fin 3)) chain 2 1 (by decide) (by decide)

#guard ((univ : Finset (Fin 3)).card * 2) ^ 2 = 36
#guard Fintype.card (Fin 4) * (3 * 2 + 3 * 2 * 1) = 48

private theorem sqrt_quarter : √(1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Four evaluation points of `ZMod 5`. -/
private def dom4 : Fin 4 ↪ ZMod 5 := ⟨![0, 1, 2, 3], by decide⟩

/-- **Interleaved Reed-Solomon instance.** Lines on four points, `η = 1/4`: at most four list
members at ArkLib's Johnson threshold, which is `3`. -/
example (O : Fin 2 → Fin 4 → ZMod 5) :
    ((iList (ReedSolomon.code dom4 2) ⌈johnsonAgreement 4 1 (1 / 4) * 4⌉₊ O).card : ℝ) ≤ 4 := by
  have h := card_iList_johnsonAgreement_le dom4 (D := 1) (η := 1 / 4) (by decide) (by decide)
    (by norm_num) O
  have hρ : johnsonRhoMinus 4 1 = 1 / 4 := by norm_num [johnsonRhoMinus]
  rw [hρ, sqrt_quarter] at h
  refine h.trans (le_of_eq ?_)
  norm_num

example : ⌈johnsonAgreement 4 1 (1 / 4) * 4⌉₊ = 3 := by
  have : johnsonAgreement 4 1 (1 / 4) * 4 = 3 := by
    rw [johnsonAgreement, johnsonRhoMinus, show ((1 : ℕ) : ℝ) / (4 : ℕ) = 1 / 4 by norm_num,
      sqrt_quarter]
    norm_num
  rw [this]
  exact Nat.ceil_natCast 3

/-- **Negative control.** Dropping the pairwise agreement hypothesis breaks the bound. -/
example : ¬ ∀ (L : Finset (Fin 5)) (T : Fin 5 → Finset (Fin 4)),
    (∀ b ∈ L, (√(1 / 4 : ℝ) + 1 / 4) * Fintype.card (Fin 4) ≤ (T b).card) →
    (L.card : ℝ) ≤ 1 / (2 * (1 / 4) * √(1 / 4 : ℝ)) := by
  intro h
  have := h univ (fun _ ↦ univ) fun b _ ↦ by rw [sqrt_quarter]; norm_num
  rw [sqrt_quarter] at this
  norm_num at this

end LeanVMTests.Protocol.Whir
