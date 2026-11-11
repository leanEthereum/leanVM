/-
  LeanVM.Protocol.Verifier.WhirTarget

  The WHIR opening's program as the proofs unfold it: the stacked opening's steps and the ladder's
  totals.
-/

module

public import LeanVM.Parameters.Whir

/-!
# The WHIR opening's program

`Statement/LeanVmVerifier.lean` transcribes `verify_whir` (`crates/verifier/src/whir.rs:223-343`)
with its running claim threaded through every fold round (`WhirState.claim`), the form the proofs
reason on directly; the threaded copy of the opening this module held for the protocol before
`f128` is gone. What is left:

* `verifyStackedOpening_eq`: the stacked opening's three steps, the claim count's check, the
  batching challenge, then `verifyWhir` on the batched claim;
* `ladder_sum_lt`: every ladder leaves its final level at least one variable, so the tail sumcheck
  has a round and `subspaceAt` a factor for the final level (checked on the 56 admissible pairs).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Compile

@[expose] public section

/-- **The stacked opening's steps.** -/
theorem verifyStackedOpening_eq (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    verifyStackedOpening stackLog logInvRate claims =
      (VerifierProgram.require (claims.length ≤ maxStackedClaims)).bind fun _ ↦
        VerifierProgram.sampleChallenge.bind fun c ↦
          verifyWhir stackLog logInvRate (dot (powers c claims.length) (claims.map (·.2)))
            fun point ↦ dot (powers c claims.length) (claims.map fun cl ↦ cl.1 point) :=
  rfl

/-- **Every ladder leaves its final level at least one variable.** -/
theorem ladder_sum_lt {μ r : ℕ} {levels : List Whir.Level} (h : Whir.ladder μ r = some levels) :
    (levels.map (·.fold)).sum < μ := by
  have hadm : Whir.Admissible μ r := by
    unfold Whir.ladder at h
    split at h
    · assumption
    · cases h
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
      ∀ levels, Whir.ladder μ r = some levels → (levels.map (·.fold)).sum < μ := by
    decide +kernel
  have hb : μ < Whir.maxLogStack + 1 ∧ r < 5 := by
    unfold Whir.Admissible at hadm
    omega
  exact key μ hb.1 r hb.2 hadm levels h

end

end LeanVM.Protocol.Verifier
