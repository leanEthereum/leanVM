module

public import XmssSecurity.Proof.OwnFirstLane
public import XmssSecurity.Proof.OwnSecondLane

@[expose] public section

/-!
# The model at the adversary's own count

Both lanes charge the adversary's own hash calls once each, the verification's and lane 1's probes:
the model's forgery probability is at most two units per own call plus a constant, over `2^128`. No
bound on the whole game's calls is needed: the signer's calls are never charged.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- The model's constant: the verification's calls in each lane and lane 1's forgery probes. -/
def ownModelSlack : Nat := 2 * verifyHashCalls + CappedChain.forgeryProbeCount

theorem ownModelSlack_eq : ownModelSlack = 1058 := by
  simp [ownModelSlack, verifyHashCalls, layerVerifyHashCalls, CappedChain.forgeryProbeCount, numChains, chainLength,
    winternitzBits, treeHeight]

/-- **The model at the adversary's own count.** -/
theorem concreteScheme_security (q : Nat) (adversary : Adversary) (hown : OwnHashBound adversary q)
    (hq : q < 2 ^ 127) :
    forgeAdvantage Concrete.scheme adversary ≤
      ((2 * q + ownModelSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine (capped_forgeAdvantage_le_exactFirstLane_add_secondLane adversary).trans ?_
  refine (add_le_add (CappedChain.exactFirstLane_probability_le q adversary hown)
    (hasSecondLaneBound q adversary hown hq)).trans ?_
  rw [← ENNReal.add_div, show digestBits = 128 from rfl]
  refine ENNReal.div_le_div ?_ le_rfl
  exact_mod_cast (show q + verifyHashCalls + CappedChain.forgeryProbeCount + (q + verifyHashCalls) ≤
    2 * q + ownModelSlack by simp only [ownModelSlack]; omega)

end XmssSecurity
