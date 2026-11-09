module

public import FORS.Reduction.CostProgram
public import FORS.Reduction.Memo
public import FORS.Reduction.SeedFreeGame

@[expose] public section

/-! The budgeted win value of a graph-view cost program on a fixed answer function, and the
comparisons it supports: monotonicity in the budget, averaging a family of continuations, and
lifted private randomness. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.DetValue

variable [Params]

open HiddenCost GraphView Stop

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable (g : HashInput → HashOutput) (c : HiddenGraph.Table)

/-! ### Averaging uniform tables -/

omit g c in
/-- Splitting one coordinate off a uniform table. -/
theorem tsum_uniform_update {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (i : D) (G : (D → R) → ℝ≥0∞) :
    ∑' table, Pr{let x ← ($ᵗ (D → R) : ProbComp (D → R))}[x = table] * G table =
      ∑' a, Pr{let x ← ($ᵗ R : ProbComp R)}[x = a] * ∑' table, Pr{let x ← ($ᵗ (D → R) : ProbComp (D → R))}[x = table] *
        G (Function.update table i a) := by
  have h := uniformSample_bind_update_evalDistEq (D := D) (R := R) i
  calc
    _ = ∑' table, Pr{let x ← (do
          let u ← ($ᵗ R : ProbComp R)
          let table ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (Function.update table i u))}[x = table] * G table := by
      refine tsum_congr fun table => ?_
      rw [(h.symm).prEvent_eq _]
    _ = _ := by
      rw [OracleComp.tsum_prEvent_bind_mul]
      refine tsum_congr fun a => ?_
      rw [OracleComp.tsum_prEvent_bind_mul]
      simp only [OracleComp.tsum_prEvent_pure_mul]

omit g c in
theorem tsum_prob_mul_le {ρ : Type} (p : ProbComp ρ) (C : ℝ≥0∞) :
    ∑' x, Pr{let y ← p}[y = x] * C ≤ C := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left bot_le (OracleComp.tsum_prEvent_le_one _)

/-! ### One message: a derived randomizer base read once is a fresh uniform start -/

/-! ### The adversary's interaction as a cost program -/

open Internalize ForsPotential

attribute [local irreducible] digestAttemptLimit

noncomputable instance rtableSampleable : SampleableType Det.RTable := SampleableType.ofFintype Det.RTable

noncomputable instance ltableSampleable : SampleableType Det.LTable := SampleableType.ofFintype Det.LTable

/-! ### The deterministic signer is deterministic on a fixed answer function -/

attribute [local irreducible] ReferenceChoice.search encodingAttemptLimit

/-! ### Memoizing at the cost level -/

open Memo in
/-! ### Game level -/

end FORS.Security.DetValue
