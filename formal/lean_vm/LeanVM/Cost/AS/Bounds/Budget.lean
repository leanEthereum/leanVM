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

/-! ## The words -/

/-- A root's word's price but its leaves' lookups, at most. -/
@[expose] def wordConst : ℕ :=
  2 * (15 * 40 + 20000) + 100 + (45 * 64 + 68) * 2 ^ 34 + 2 ^ 28 * (84 + 468 * 64 + 30760 + 5 * 28)

/-- **The words' price**, at most six roots of at most `64` words and height `H ≤ 28`: a constant
per root and its leaves' lookups in the roots' index. -/
theorem wordsPrice_le (D Wl μ R H : ℕ) (hμ : μ ≤ 30) (hR : R ≤ 4) (hH : H ≤ 28) :
    ∀ (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)) (a : ℕ), a + roots.length ≤ 6 →
      (∀ x ∈ roots, x.2.2 ≤ 64 ∧ x.2.1 ≤ H) →
      wordsPrice D Wl μ R a roots ≤ 3 + roots.length * (wordConst +
        2 ^ H * (2 * (D * (20 + (162 + 9 * Wl) * (D + 2)))))
  | [], _, _, _ => by simp [wordsPrice]
  | x :: xs, a, ha, hx => by
    simp only [List.length_cons] at ha
    have ih := wordsPrice_le D Wl μ R H hμ hR hH xs (a + 1) (by omega)
      fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)
    obtain ⟨hw, hh⟩ := hx x List.mem_cons_self
    simp only [wordsPrice, wordPrice, leavesPrice, List.length_cons]
    generalize D * (20 + (162 + 9 * Wl) * (D + 2)) = X at ih ⊢
    have e1 : 2 ^ x.2.1 * (2 * (X + 42) + 468 * x.2.2 + 30760 + 5 * x.2.1) =
        2 ^ x.2.1 * (2 * X) + 2 ^ x.2.1 * (84 + 468 * x.2.2 + 30760 + 5 * x.2.1) := by ring
    have e2 : 2 ^ x.2.1 * (2 * X) ≤ 2 ^ H * (2 * X) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hh)
    have e3 : 2 ^ x.2.1 * (84 + 468 * x.2.2 + 30760 + 5 * x.2.1) ≤
        2 ^ 28 * (84 + 468 * 64 + 30760 + 5 * 28) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (by omega)
    have e4 : (45 * x.2.2 + 68) * 2 ^ ((lvC μ R a).1 + (lvC μ R a).2.1) ≤ (45 * 64 + 68) * 2 ^ 34 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (lvC_small μ R a))
    have e5 : (xs.length + 1) * (wordConst + 2 ^ H * (2 * X)) =
        xs.length * (wordConst + 2 ^ H * (2 * X)) + (wordConst + 2 ^ H * (2 * X)) := by ring
    unfold wordConst at e5 ih ⊢
    omega

theorem transcriptIndexPrice_mono (D N W : ℕ) {L L' : ℕ} (h : L ≤ L') :
    transcriptIndexPrice D L N W ≤ transcriptIndexPrice D L' N W := by
  unfold transcriptIndexPrice replayStepPrice firstAnswersStepPrice preimageStepPrice
  gcongr

end

end LeanVM.Cost.Bounds.AS
