module

public import FORS.LargeBudget.WeightedPotential
public import FORS.LazyRun.Expose
public import FORS.CoverPotential.StartValue
public import FORS.Reduction.SeedElimination
public import FORS.CoverPotential.FairCoin
public import FORS.Classification.Targeting

@[expose] public section

/-! The large-budget route with the weighted baseline. The saturation pays each digest query the
baseline times the current survival weight, and the one-coin FORS potential is weighted by the
same survival weight, so the baseline is the plain budget decrement `(2 (N - q) + 1) / N^2`
instead of `(2 (N - q) + 1) (N - 2q) / (N (N - q)^2)`. A hit or a FORS cover then has probability
at most `E[(1 - w_end) + w_end 1[cover]]`, which both sides pay. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

/-! ### The weighted baseline as a rational threshold -/

/-- Rational form of the weighted baseline at budget `qb`: `(2 (2^128 - qb) + 1) / 2^256`. -/
def betaWQ (qb : ℕ) : ℚ := (2 * ((2 : ℚ) ^ 128 - qb) + 1) / 2 ^ 256

theorem baselineW_eq_betaWQ (q : ℕ) : HiddenDebt.baselineW q = ENNReal.ofReal (betaWQ q : ℝ) := by
  unfold HiddenDebt.baselineW HiddenDebt.spaceReal betaWQ
  congr 1
  push_cast
  ring

/-- The weighted baseline at budget `q` is at least the rational threshold at any `qb ≥ q`. -/
theorem baselineW_ge (q qb : ℕ) (hq : q ≤ qb) :
    ENNReal.ofReal (betaWQ qb : ℝ) ≤ HiddenDebt.baselineW q := by
  rw [baselineW_eq_betaWQ]
  apply ENNReal.ofReal_le_ofReal
  unfold betaWQ
  push_cast
  have h : (q : ℝ) ≤ qb := by exact_mod_cast hq
  have h2 : (0 : ℝ) < 2 ^ 256 := by positivity
  rw [div_le_div_iff_of_pos_right h2]
  linarith

/-! ### The rest of the game, weighted -/

section RestW

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A hit or a FORS cover of one interpreted outcome has probability at most the missing survival
weight plus the weighted final value. -/
theorem hit_or_cover_le (out : Run HashInput Coordinate HiddenBridge.Outcome × State) :
    Pr{let r ← (fun table => (table, out)) <$> completion out.2.known}[Hit tg initial r.1 r.2.2 ∨ CoverOf parameter data r.2] ≤
      (1 - weight tg initial out.2) + weight tg initial out.2 * finalValue parameter data tg initial [] out := by
  rw [prEvent_map]
  by_cases hc : CoverOf parameter data out ∧ ¬Realized tg initial out.2
  · obtain ⟨⟨outcome, hres, hfc⟩, hreal⟩ := hc
    have h1 : finalValue parameter data tg initial [] out = 1 := by
      unfold finalValue
      rw [hres]
      simp only [Option.elim, List.nil_append]
      rw [ite_eq_left ⟨hfc, hreal⟩]
    rw [h1, mul_one, tsub_add_cancel_of_le (weight_le_one tg initial out.2)]
    exact (prEvent_le_one _)
  · refine le_trans ?_ le_self_add
    have hsub : Pr{let x ← completion out.2.known}[((fun r : (Coordinate → Digest) × Run HashInput Coordinate HiddenBridge.Outcome × State =>
          Hit tg initial r.1 r.2.2 ∨ CoverOf parameter data r.2) ∘ (fun table => (table, out))) x] ≤ Pr{let table ← completion out.2.known}[Hit tg initial table out.2] := by
      refine prEvent_mono_of_support _ _ _ fun table _ hp => ?_
      rcases hp with hh | hcov
      · exact hh
      · exact Or.inl (not_not.1 fun hr => hc ⟨hcov, hr⟩)
    refine le_trans hsub ?_
    have hsplit : Pr{let table ← completion out.2.known}[Hit tg initial table out.2]
        + Pr{let table ← completion out.2.known}[¬Hit tg initial table out.2] = 1 := by
      rw [OracleComp.prEvent_not_eq_one_sub]
      exact add_tsub_cancel_of_le (prEvent_le_one _)
    have hle := weight_le_noHit tg initial out.2
    calc Pr{let table ← completion out.2.known}[Hit tg initial table out.2]
        = 1 - Pr{let table ← completion out.2.known}[¬Hit tg initial table out.2] :=
          ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)) hsplit
      _ ≤ _ := tsub_le_tsub_left hle _

end RestW

section ChainW

open HiddenBridge Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize

/-- The targeting facts at every prepared sample of a parameter set. -/
def TargetingAll : Prop :=
  ∀ parameterOutput fixed highs remaining prepared,
    prepared ∈ support (preparation parameterOutput fixed highs remaining) →
    TargetingFor parameterOutput fixed highs remaining prepared

/-- Every prepared sample has a targeting, given a top layer of positive kept height, which a full
key (`Params.full`) always has. -/
theorem targetingAll (hb : 0 < keptHeight topLayer) : TargetingAll := by
  intro parameterOutput fixed highs remaining prepared hprepared
  obtain ⟨tg, htrunc, hcompat, hmsg, hhit⟩ :=
    exists_targeting hb parameterOutput fixed highs remaining prepared hprepared
  exact ⟨tg, hcompat, uniformTruncation_of_trunc tg htrunc, hmsg, hhit⟩

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

end ChainW

end FORS.Security.ForsPotential
