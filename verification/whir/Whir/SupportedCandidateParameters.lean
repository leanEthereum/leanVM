import Whir.UniqueRadiusSampling

/-! Exact initial-root source-profile cutoff. Query counts vary with rate and
size: 56 is used only at rate four. The extraction cutoff is not 128-bit. -/
namespace Whir.SupportedCandidateExtraction

def initialRadiusLoss (profile : ParameterBounds.Profile) : ℚ :=
  let c := ParameterBounds.config profile
  UniqueRadiusSampling.queryLoss
    (c.logN - c.folds[0]! + c.rates[0]!) (2 ^ (c.logN - c.folds[0]!)) c.queries[0]!

def radiusEnvelope : ℚ := (17 / 32) ^ 56
def extractionCutoff : ℚ := 1 / 2 ^ 50

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Kernel certificate on ALL actual production profiles, not a substituted
rate-four query count. Finite-size parity corrections are retained. -/
theorem production_initialRadiusLoss : ∀ profile : ParameterBounds.Profile,
    initialRadiusLoss profile ≤ radiusEnvelope := by
  decide +kernel

theorem extractionCutoff_gap (profile : ParameterBounds.Profile) :
    (1 / 2 ^ 51 : ℚ) < extractionCutoff - initialRadiusLoss profile := by
  have bound := production_initialRadiusLoss profile
  have envelope := UniqueRadiusSampling.rate_four_envelope_bits.2
  change radiusEnvelope < (1 / 2 ^ 51 : ℚ) at envelope
  unfold extractionCutoff
  norm_num at *
  linarith

#print axioms production_initialRadiusLoss
#print axioms extractionCutoff_gap
end Whir.SupportedCandidateExtraction
