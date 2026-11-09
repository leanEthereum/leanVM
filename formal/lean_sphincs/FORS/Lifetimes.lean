module

public import FORS.Certificates.H26
public import FORS.Certificates.ClosingAdv

@[expose] public section

/-! **Proof of the proved lifetime**: `ForsPotential.det_bitsF` applied to the configuration's
certificates (`Certificates/H26.lean`). `Main.lean` states it again, independently of this file, and
proves it with the theorem here. Small budgets use the linear potential, the one-coin cover potential
at baseline `ρ / 2^128` and the contact bound A4 of the FORS leaves; large budgets use the one-coin
covers at the survival-weighted baseline. -/

namespace FORS.Lifetimes

open Security ForsPotential ENNReal

/-- The deployed configuration. -/
abbrev h26Params : Params := .layered 26 3 8 24 10 1182000000

section Adversary

attribute [local instance] h26Params

/-- The verifier makes at most 879 hash calls. -/
theorem h26_verifyCalls : Concrete.verifyCalls = 879 := by decide

/-- **127 bits at the adversary's own count**, in the deployed configuration: an adversary making at
most `q` hash calls on every path forges with chance at most `(q + 265072) / 2^127`, where
`265072 = keygenHashCost + verifyCalls = 264193 + 879`. -/
theorem h26_layered_adversary (adversary : Security.Adversary) (q : ℕ)
    (hq : ∀ pk, (adversary.main pk).IsQueryBoundP Security.AdvCount.AdvHash q) :
    Security.forgeAdvantage adversary ≤ ((q : ℝ≥0∞) + ((265072 : ℕ) : ℝ≥0∞)) / ((2 ^ 127 : ℕ) : ℝ≥0∞) :=
  det_bitsF (by decide) 26 26 24 10 264193 1182000000
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 512487451133699472151040029945233408
    H0.rho_h26_b26 H0.tab_h26_b26 H0.small_h26_b26 H0.near_h26_b26 H0.tab_h26_b26_ok H0.rate_h26_b26_ok H0.small_h26_b26_ok
    H0.near_h26_b26_ok H0.check_h26_b26_ok [H0.cover_h26_b26_0] [] H0.covers_h26_L_ok 879
    (fun pk message signature => h26_verifyCalls ▸ Concrete.verify_calls pk message signature) adversary q hq

end Adversary

end FORS.Lifetimes
