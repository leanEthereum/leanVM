module

public import FORS.SmallBudget.Closing
public import FORS.SmallBudget.SampleBound
public import FORS.Reduction.SeedEliminationAdv

@[expose] public section

/-! **Small budgets with the honest signer, at the adversary's own hash-call count.** The sample
bound of the honest game (`sample_boundF`) averaged over the prepared samples, given the program
bridge from the seed-free honest experiment to the interpreted honest game (`SmallBridgeH`:
`seedFree_le_exposeP` followed by `stopped_le_interp_exposeV`); then the
forgery advantage through `forgeAdvantage_le_seedFree` at the budget
`Q = keygenHashCost + q + V`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
  FORS.Base.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

section CloseH

open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize

/-- **The program bridge of the small route, the signer honest**: the seed-free win of the honest
game is at most the mean, over the prepared samples with the above-word values exposed, of a
correct guess or the refined bad event of the interpreted honest game. -/
def SmallBridgeH (adversary : Adversary) (q : ℕ) (steps : Message → Randomness) : Prop :=
  Pr{let z ← AdvCount.seedFreeExperiment adversary q steps}[Win z] ≤
    ∑' parameterOutput, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = parameterOutput] *
    ∑' fixed, Pr{let x ← ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)}[x = fixed] *
    ∑' highs, Pr{let x ← ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)}[x = highs] *
    ∑' remaining, Pr{let x ← ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)}[x = remaining] *
    ∑' prepared, Pr{let x ← preparation parameterOutput fixed highs remaining}[x = prepared] *
    ∑' known, Pr{let x ← (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed))}[x = known] *
      Pr{let x ← (interp (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
          (sampleModel parameterOutput highs)
          (costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps) adversary)
          q (DebtState.start prepared.2 known) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known)}[CorrectGuess x.1 x.2.2 ∨
          badAV parameterOutput fixed highs remaining prepared.1 x.1 (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache)]

set_option maxRecDepth 100000 in
/-- **Small budgets, seed-free win of the honest game.** -/
theorem small_seedFree_boundF (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (steps : Message → Randomness) (hbridge : SmallBridgeH (internalize adversary) q steps)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) ≤ (κ : ℝ))
    (H b k a N : ℕ) (hHH : totalHeight = H) (hbb : subtreeHeight = b) (hkk : forsTrees = k)
    (haa : forsHeight = a) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate H b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOpt H b k a t o = true) (hon : H0.checkOptN H k a t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128) :
    Pr{let z ← AdvCount.seedFreeExperiment (internalize adversary) q steps}[Win z] ≤
      (smallMainFF ρ q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost)) + smallFailF q * expectedFail := by
  refine le_trans hbridge ?_
  set A := smallMainFF ρ q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) +
    2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) with hA
  set C := smallFailF q with hC
  have hκ1R : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ1
  refine le_trans (tsum_bound_le _ _ A C (fun parameterOutput => ∑' fixed, Pr{let x ← ($ᵗ HiddenGraph.Table :
    ProbComp HiddenGraph.Table)}[x = fixed] *
    ∑' highs, Pr{let x ← ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)}[x = highs] *
    ∑' remaining, Pr{let x ← ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)}[x = remaining] *
    ∑' prepared, Pr{let x ← preparation parameterOutput fixed highs remaining}[x = prepared] *
      failMass (failSet prepared.1)) fun parameterOutput _ => ?_) le_rfl
  refine tsum_bound_le _ _ A C _ fun fixed _ => ?_
  refine tsum_bound_le _ _ A C _ fun highs _ => ?_
  refine tsum_bound_le _ _ A C _ fun remaining _ => ?_
  refine tsum_bound_le _ _ A C _ fun prepared hprepared => ?_
  refine le_trans (tsum_bound_le _ _ A C (fun _ => failMass (failSet prepared.1))
    fun known hk => ?_) ?_
  · refine le_trans (sample_boundF adversary hnr q parameterOutput fixed highs remaining steps prepared
      hprepared known hk ρ hN (κ : ℝ) hκ hκ1R H b k a N hHH hbb hkk haa hNN t o on hpt qtop hrt hqtop ho hon
      hcthr) (le_of_eq ?_)
    rw [hA, hC]
    unfold smallMainFF smallFailF
    rw [Rat.cast_mul, ENNReal.ofReal_mul (Rat.cast_nonneg.2 hκ0)]
    ring
  · refine add_le_add le_rfl (mul_le_mul_right ?_ _)
    rw [ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

/-- **Small budgets with the honest signer, every steps**: the seed-free bound `hB` of
`forgeAdvantage_le_seedFree`, for the memoized adversary. -/
theorem small_seedFree_allFH (adversary : Adversary) (Q : ℕ)
    (hbridge : ∀ steps, SmallBridgeH (internalize (Memo.memoAdv adversary)) Q steps)
    (ρ : ℝ) (hN : Numeric ρ (((Q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + ((Q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) ≤ (κ : ℝ))
    (H b k a N : ℕ) (hHH : totalHeight = H) (hbb : subtreeHeight = b) (hkk : forsTrees = k)
    (haa : forsHeight = a) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate H b N qtop t = true) (hqtop : Q - keygenCost ≤ qtop)
    (ho : H0.checkOpt H b k a t o = true) (hon : H0.checkOptN H k a t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (steps : Message → Randomness) :
    Pr{let z ← AdvCount.seedFreeExperiment (internalize (Memo.memoAdv adversary)) Q steps}[Win z] ≤
      smallMainFF ρ Q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) + smallFailF Q * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        2 * lam (H0.LmaxOf (Q - keygenCost)) 0 (Q - keygenCost) := by
  refine le_trans (small_seedFree_boundF (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) Q steps
    (hbridge steps) ρ hN κ hκ0 hκ1 hκ H b k a N hHH hbb hkk haa hNN t o on hpt qtop hrt hqtop ho hon hcthr) ?_
  rw [add_right_comm]
  exact add_le_add (add_le_add le_rfl (mul_le_mul_right expectedFail_le _)) le_rfl

/-- **Small budgets with the honest signer, at the adversary's own hash-call count**: an adversary
making at most `q` hash calls on every path, against a verifier making at most `V`, forges with
chance at most the small-budget bound at `Q = keygenHashCost + q + V`. -/
theorem det_smallF (adversary : Adversary) (q V : ℕ)
    (hq : ∀ pk, (adversary.main pk).IsQueryBoundP AdvCount.AdvHash q)
    (hV : ∀ pk message signature,
      (Concrete.verify pk message signature : OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) V)
    (hbridge : ∀ steps, SmallBridgeH (internalize (Memo.memoAdv adversary)) (Prefix.keygenHashCost + q + V) steps)
    (ρ : ℝ) (hN : Numeric ρ ((((Prefix.keygenHashCost + q + V) - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + (((Prefix.keygenHashCost + q + V) - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) ≤ (κ : ℝ))
    (H b k a N : ℕ) (hHH : totalHeight = H) (hbb : subtreeHeight = b) (hkk : forsTrees = k)
    (haa : forsHeight = a) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate H b N qtop t = true) (hqtop : (Prefix.keygenHashCost + q + V) - keygenCost ≤ qtop)
    (ho : H0.checkOpt H b k a t o = true) (hon : H0.checkOptN H k a t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128) :
    forgeAdvantage adversary ≤
      smallMainFF ρ (Prefix.keygenHashCost + q + V) o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) +
        smallFailF (Prefix.keygenHashCost + q + V) * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        2 * lam (H0.LmaxOf ((Prefix.keygenHashCost + q + V) - keygenCost)) 0
          ((Prefix.keygenHashCost + q + V) - keygenCost) +
        3 * (((Prefix.keygenHashCost + q + V : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine le_trans (AdvCount.forgeAdvantage_le_seedFree adversary q V hq hV _
    (small_seedFree_allFH adversary _ hbridge ρ hN κ hκ0 hκ1 hκ H b k a N hHH hbb hkk haa hNN t o on hpt qtop hrt
      hqtop ho hon hcthr)) (add_le_add le_rfl ?_)
  gcongr
  norm_num

end CloseH

end FORS.Security.ForsPotential
