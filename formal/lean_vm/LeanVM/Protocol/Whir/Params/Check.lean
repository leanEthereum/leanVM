/-
  LeanVM.Protocol.Whir.Params.Check

  The deployed WHIR parameters' rows other than the fold rounds, checked on every admissible
  shape by kernel evaluation: the ladder's geometry, the list bounds, the batching, out-of-domain
  and query rows.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDeployedTable
public import LeanVM.Parameters.Whir

/-!
# The deployed parameters' check

The levels of a shape are the fold certificate's (`AffineCombiner.foldTable`: `(κ, R, k, Aend,
rounds)` per level, exported from the Rust's `derive_config_with_log_inv_rate`). `shapeOK μ R`
checks, in natural numbers, everything the round-by-round analysis takes of them besides the
fold rounds' own check (`AffineCombiner.levelOK`, which it includes):

* the levels are the statement's ladder (`Whir.ladder μ R`): folds, rates, and `κ_i + k_i =
  κ_(i−1)` with `κ_(−1) = μ`; `κ + R ≤ 64`, `1 ≤ R`, `1 ≤ k ≤ 2^κ`, `k < Aend`;
* the list each level starts on is defined (`n d₀ < A₀²`) and its bound `jlStart` is
  `jl n A₀ d₀`;
* each level's queries: `((Aend − 1)/n)^t ≤ 2^-108`, i.e. `2^-125` after the `17`-bit grind;
* each level with a next one: its batching `λ`, `(t + 2) L' ≤ 2^17` (`2^-125` after the `14`-bit
  grind), and the next level's out-of-domain points, `L'² κ² ≤ 2^131` (`L'² (κ/|E|)² ≤ 2^-125`,
  no grind, a bound twice the Annex's `C(L', 2)`), with `1 ≤ κ`;
* level `0`: its rate is the shape's and it folds the `2^6` lanes (`k₀ = 6`), the threshold covers the degree (`2^κ₀ ≤ A₀`),
  its list bound is at most `166`, the stacked opening's batching with the ring's map,
  `513 L₀ ≤ 2^17`, and the commitment's out-of-domain sample, `C(L₀, 2) μ ≤ 2^18` (`2^-125` after
  its `15`-bit grind).

`shapeOK_all`: every admissible shape passes, by kernel evaluation.
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Whir.AffineCombiner

@[expose] public section

/-- A level of the fold certificate: `(κ, R, k, Aend, rounds)`. -/
abbrev Lv : Type := ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)

/-- The levels of a shape. -/
def levelsOf (μ R : ℕ) : List Lv := (foldTable.getD (R - 1) []).getD (μ - 15) []

/-- The threshold a level starts on, `A₀ = Aend − k`. -/
def thrStart (lv : Lv) : ℕ := lv.2.2.2.1 - lv.2.2.1

/-- Level 0's threshold of a shape. -/
def thr0Of (μ R : ℕ) : ℕ := thrStart ((levelsOf μ R).headD (0, 1, 0, 1, []))

/-- The list bound a level starts on, `jl(n, A₀, d₀)`. -/
def jlStart (lv : Lv) : ℕ := jl (2 ^ (lv.1 + lv.2.1)) (lv.2.2.2.1 - lv.2.2.1) (2 ^ lv.1 - 1)

/-- One level's checks against its ladder level, `κprev` the variables before its folds. -/
def levelChecks (κprev : ℕ) (lv : Lv) (cfg : Whir.Level) : Bool :=
  let κ := lv.1
  let R := lv.2.1
  let k := lv.2.2.1
  let A := lv.2.2.2.1
  decide (κ + k = κprev) && decide (cfg.fold = k) && decide (cfg.logInvRate = R) &&
    decide (κ + R ≤ 64) && decide (1 ≤ R) && decide (1 ≤ k) && decide (k ≤ 2 ^ κ) &&
    decide (k < A) && levelOK foldBudget lv &&
    decide ((A - 1) ^ cfg.queries * 2 ^ 108 ≤ (2 ^ (κ + R)) ^ cfg.queries) &&
    decide (2 ^ (κ + R) * (2 ^ κ - 1) < (A - k) * (A - k))

/-- The levels' checks, and between consecutive levels the batching and out-of-domain rows. -/
def chainChecks : ℕ → List Lv → List Whir.Level → Bool
  | κprev, [lv], [cfg] => levelChecks κprev lv cfg
  | κprev, lv :: lv' :: rest, cfg :: cfg' :: crest =>
    levelChecks κprev lv cfg && decide ((cfg.queries + 2) * jlStart lv' ≤ 2 ^ 17) &&
      decide (jlStart lv' ^ 2 * lv.1 ^ 2 ≤ 2 ^ 131) && decide (1 ≤ lv.1) &&
      chainChecks lv.1 (lv' :: rest) (cfg' :: crest)
  | _, _, _ => false

/-- **The check of a shape.** -/
def shapeOK (μ R : ℕ) : Bool :=
  match Whir.ladder μ R, levelsOf μ R with
  | some cfg, lv :: rest =>
    chainChecks μ (lv :: rest) cfg && decide (lv.2.1 = R) && decide (lv.2.2.1 = 6) &&
      decide (2 ^ lv.1 ≤ lv.2.2.2.1 - lv.2.2.1) && decide (jlStart lv ≤ 166) &&
      decide (513 * jlStart lv ≤ 2 ^ 17) && decide ((jlStart lv).choose 2 * μ ≤ 2 ^ 18)
  | _, _ => false

/-- **Every admissible shape passes.** -/
theorem shapeOK_all : ∀ μ < Whir.maxLogStack + 1, ∀ R < 5, Whir.Admissible μ R →
    shapeOK μ R = true := by
  decide +kernel

end
end LeanVM.Protocol.Whir.Params
