/-
  LeanVM.Guest.B1.Whir.CHonStatic

  The configuration facts the honest buffers' reads take, as one decidable proposition.
-/

module

public import LeanVM.Guest.B1.Whir.CHead
public import LeanVM.Guest.B1.Place.OsHonest

/-!
# The honest buffers' configuration facts

`HonStatic c`: the levels' segments of `merkle_caps`, `merkle_cap_active` and `query_positions`
in order within their buffers, the squeeze runs within `sqz`, the out-of-domain rows and the high
parts within their strides, the fold rounds' offsets, and the buffers' sizes (`osSizesF`) at the
indices the reads use. `Whir/CHonStatic{0..3}.lean` decide it for the 28 candidates.
`chain_disj`: segments in order are disjoint.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- **The honest buffers' configuration facts.** -/
def HonStatic (c : OsCfg) : Prop :=
  let n := c.levels.length
  let lv := osLvAt c
  2 ≤ n ∧ c.yrLevel + 1 = n ∧ c.yrLog ≤ yrLogCap ∧
  (∀ l < n, 4 * (lv l).capOff + 2 ^ ((lv l).capDepth + 2) ≤
    (if l + 1 < n then 4 * (lv (l + 1)).capOff else 4 * c.capLen)) ∧
  (∀ l < n, (lv l).capOff + 2 ^ (lv l).capDepth ≤ (if l + 1 < n then (lv (l + 1)).capOff else c.capLen)) ∧
  (∀ l < n, (lv l).posOff + (lv l).squeezes * sqPer (lv l) ≤
    (if l + 1 < n then (lv (l + 1)).posOff else c.posLen)) ∧
  (∀ l < n, (lv l).squeezes ≤ c.maxSq ∧ 1 ≤ sqPer (lv l)) ∧
  (∀ l < c.yrLevel, (lv l).logCols ≤ ligColsCap ∧ (lv l).folds ≤ hsStride) ∧
  (lv 0).foldsOff = 0 ∧ (∀ l < c.yrLevel, (lv (l + 1)).foldsOff = (lv l).foldsOff + (lv l).folds) ∧
  (lv c.yrLevel).foldsOff + (lv c.yrLevel).folds = c.nFolds ∧
  (osSizesF c).length = 20 + 2 * n + c.yrLevel ∧
  (∀ j < 13, (osSizesF c).getD j 0 = (headSizes c).getD j 0) ∧
  (∀ l < n, (osSizesF c).getD (13 + 2 * l) 0 =
      (if l = c.yrLevel then (c.maxSq + 1) * 5 else 2 + (lv l).folds) ∧
    (osSizesF c).getD (14 + 2 * l) 0 =
      (if l = c.yrLevel then c.yrLen + (lv l).folds else (c.maxSq + 1) * 5)) ∧
  (∀ k < 7, (osSizesF c).getD (13 + 2 * n + k) 0 =
    [yrLogCap, pointCap, pointCap, n * ligColsCap, n, n, 2 * n].getD k 0) ∧
  (∀ l < c.yrLevel, (osSizesF c).getD (20 + 2 * n + l) 0 = 2 * ((lv l).queries / resBatch + 1))

instance (c : OsCfg) : Decidable (HonStatic c) := by
  unfold HonStatic; dsimp only; infer_instance

/-- **Segments in order are disjoint.** -/
theorem chain_disj {n top : ℕ} {a w : ℕ → ℕ}
    (h : ∀ l < n, a l + w l ≤ (if l + 1 < n then a (l + 1) else top)) :
    (∀ l l', l < n → l' < n → l < l' → a l + w l ≤ a l') ∧ ∀ l < n, a l + w l ≤ top := by
  have step : ∀ l, l + 1 < n → a l + w l ≤ a (l + 1) := fun l hl ↦ by
    have := h l (by omega); simpa only [hl, ↓reduceIte] using this
  have up : ∀ d l, l + d < n → a l + w l ≤ a (l + d) + w (l + d) := by
    intro d
    induction d with
    | zero => intro l _; exact le_rfl
    | succ d ih =>
      intro l hl
      have h1 := ih l (by omega)
      have h2 := step (l + d) (by omega)
      rw [show l + (d + 1) = l + d + 1 by omega]
      omega
  refine ⟨fun l l' _ hl' hll ↦ ?_, fun l hl ↦ ?_⟩
  · have h1 := up (l' - 1 - l) l (by omega)
    have h2 := step (l + (l' - 1 - l)) (by omega)
    rw [show l + (l' - 1 - l) + 1 = l' by omega] at h2
    omega
  · have h1 := up (n - 1 - l) l (by omega)
    have h2 := h (l + (n - 1 - l)) (by omega)
    simp only [show ¬ (l + (n - 1 - l) + 1 < n) by omega, ↓reduceIte] at h2
    omega

end
end LeanVM.Guest.B1.Whir
