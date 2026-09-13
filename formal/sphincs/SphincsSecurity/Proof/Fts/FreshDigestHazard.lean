import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestAttemptExpectation
import SphincsSecurity.Proof.Fts.FewTimeTargetCompletion
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop

def FreshDigestAttempt (reference : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (result : DigestAttemptResult) : Prop :=
  reference (tweakableHashInput key.parameter .message (messageDigestPayload key.root message result.1)) = none ∧
    result.2.1 ≠ none

private theorem probEvent_digestContinuation_fresh_eq
    (attempts : Nat) (key : SecretKey) (message : Message)
    (reference : QueryCache HashSpec) (result : DigestAttemptResult) :
    Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
      signDigestLoopContinuation attempts key message result.1 result.2] =
      (if FreshDigestAttempt reference key message result then 1 else 0) +
        if result.2.1 = none then
          Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
            (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  cases hr : result.2.1 with
  | none => simp only [signDigestLoopContinuation, FreshDigestAttempt, hr, ne_eq, not_true_eq_false,
      and_false, if_false, if_true, zero_add]
  | some selected =>
      obtain ⟨index, leaves⟩ := selected
      by_cases hc : reference (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message result.1)) = none
      · simp [signDigestLoopContinuation, FreshDigestAttempt, freshSelectedLoopView?, hr, hc]
      · simp [signDigestLoopContinuation, FreshDigestAttempt, freshSelectedLoopView?, hr, hc]

theorem probEvent_signDigestLoop_fresh_recurrence
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec) :
    Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
      (simulateQ romImpl (signDigestLoop (attempts + 1) key message)).run cache] =
      Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] +
        ∑' result, Pr[= result | signDigestAttemptPrefix key message cache] *
          if result.2.1 = none then
            Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
              (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  rw [signDigestLoop_run_succ_eq_attemptPrefix, probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  rw [probEvent_digestContinuation_fresh_eq]
  split_ifs <;> ring

end SphincsSecurity.Concrete
