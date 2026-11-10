/-
  LeanVM.Protocol.Whir.Params.Threshold

  The extractor's Johnson threshold is the deployed level 0's, checked on every admissible shape
  by kernel evaluation.
-/

module

public import LeanVM.Protocol.Whir.Params.Check
public import LeanVM.Protocol.Extraction.Extractor

/-!
# The extractor's threshold

`Extraction.johnsonThreshold μ R`, the agreement the extractor list-decodes at, computed from its
slack table, is level 0's threshold `A₀ = Aend − k` of the fold certificate (`thr0Of`) at every
admissible shape (`johnsonThreshold_eq_thr0Of`).
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters

@[expose] public section

/-- **The extractor's threshold is level 0's.** -/
theorem johnsonThreshold_eq_thr0Of {μ R : ℕ} (h : Whir.Admissible μ R) :
    LeanVM.Extraction.johnsonThreshold μ R = thr0Of μ R := by
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ R < 5, Whir.Admissible μ R →
      LeanVM.Extraction.johnsonThreshold μ R = thr0Of μ R := by
    decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) R (Nat.lt_succ_of_le h.2.2.2) h

end
end LeanVM.Protocol.Whir.Params
