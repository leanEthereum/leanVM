module

public import LeanVM.Cost.AS.Bounds.Finish
import all LeanVM.Protocol.Whir.Sound.DescentC
import all LeanVM.Protocol.Whir.Params.Check
import all LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDeployedTable
import all LeanVM.Protocol.Extraction.AS.TraceShape
import all Statement.LeanVmVerifier

/-!
# Bounds: the descent's worst price at every shape

`traceBound`: the descent across levels' price (`traceCostB`) at the largest trace the ladder
admits, every level's rounds its folds, the final polynomial of `2^(μ − A) + ℓ` coefficients
(`traceCostB_le_bound`). **`traceBound_ok`**: at every admissible stack size and rate, the
descent's worst price, level 0's stack and `2^55` are within `2^max(58, 2μ + 9)`.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Extraction.AS

public section

theorem descPrice_mono (n d W : ℕ) {r r' : ℕ} (h : r ≤ r') : descPrice n d W r ≤ descPrice n d W r' := by
  unfold descPrice stepG
  have : 2 ^ (0 + 1 + r) ≤ 2 ^ (0 + 1 + r') := Nat.pow_le_pow_right (by norm_num) (by omega)
  gcongr

theorem polyPrice_mono {L L' : ℕ} (h : L ≤ L') : polyPrice L ≤ polyPrice L' := by
  unfold polyPrice
  gcongr

theorem upPrice_mono (κ κ' m R : ℕ) {L L' : ℕ} (h : L ≤ L') : upPrice κ κ' m R L ≤ upPrice κ κ' m R L' := by
  unfold upPrice
  have := polyPrice_mono h
  gcongr

/-- The descent's price at the largest trace of the levels `cfg`, from level `i`, `A` the folds
made before it. -/
@[expose] def traceBound (μ R W : ℕ) : ℕ → ℕ → List Whir.Level → ℕ
  | _, _, [] => 0
  | i, A, [lv] =>
    (15 * (μ + R + i) + 20000) + 15 * i + 17 + 11 * lv.fold + 3 +
      (polyPrice (2 ^ (μ - (A + lv.fold)) + lv.fold) + 13 + 16) *
        2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) + 5 +
      2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) +
      descPrice (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1)
        W lv.fold + 100
  | i, A, lv :: nx :: rest =>
    traceBound μ R W (i + 1) (A + lv.fold) (nx :: rest) + (15 * (μ + R + i) + 20000) +
      (15 * (μ + R + (i + 1)) + 20000) + 15 * i + 17 + 11 * lv.fold + 3 +
      upPrice (lvC μ R i).1 (lvC μ R (i + 1)).1 (lvC μ R (i + 1)).2.2.1 (lvC μ R i).2.1 lv.fold +
      descPrice (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1)
        W lv.fold + 200

/-- **A trace of the ladder's shape costs at most its levels' bound.** -/
theorem traceCostB_le_bound (μ R W : ℕ) :
    ∀ (i A : ℕ) (cfg : List Whir.Level) (tr : WhirTrace), TraceShape μ A cfg tr →
      traceCostB μ R W tr i ≤ traceBound μ R W i A cfg
  | _, _, [], tr, h => by cases tr <;> simp [TraceShape] at h
  | i, A, [lv], .final rounds folded, h => by
    simp only [TraceShape] at h
    simp only [traceCostB, traceBound]
    have h1 := descPrice_mono (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1))
      (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1) W h.1
    have h2 := Nat.mul_le_mul_right (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1))
      (Nat.add_le_add_right (Nat.add_le_add_right (polyPrice_mono h.2) 13) 16)
    omega
  | _, _, [_], .mid _ _ _, h => by simp [TraceShape] at h
  | _, _, _ :: _ :: _, .final _ _, h => by simp [TraceShape] at h
  | i, A, lv :: nx :: rest, .mid rounds high tr, h => by
    simp only [TraceShape] at h
    simp only [traceCostB, traceBound]
    have ih := traceCostB_le_bound μ R W (i + 1) (A + lv.fold) (nx :: rest) tr h.2.2
    have h1 := descPrice_mono (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1))
      (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1) W h.1
    have h2 := upPrice_mono (lvC μ R i).1 (lvC μ R (i + 1)).1 (lvC μ R (i + 1)).2.2.1 (lvC μ R i).2.1 h.2.1
    omega

/-- **The descent's worst price, level 0's stack and `2^55` within `2^max(58, 2μ + 9)`**, at
every admissible stack size and rate. -/
theorem traceBound_ok : ∀ m < 15, ∀ r < 4,
    traceBound (m + 16) (r + 1) 64 0 0 ((Whir.ladder (m + 16) (r + 1)).getD []) + stackPrice (m + 16) +
      2 ^ 55 ≤ 2 ^ max 58 (2 * (m + 16) + 9) := by
  decide +kernel

end

end LeanVM.Cost.Bounds.AS
