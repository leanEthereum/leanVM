import XmssSecurity.Proof.Deterministic.Preparation
import XmssSecurity.Proof.Deterministic.MemoLog

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {Request Answer : Type} [DecidableEq Request]

def loggedRun {α : Type} (sign : Request → OracleComp OracleWorld Answer)
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) :
    OracleComp OracleWorld (α × QueryLog (Request →ₒ Answer)) :=
  (simulateQ ((fun input => liftM (liftM (OracleWorld.query input) : OracleComp OracleWorld _)) + QueryImpl.withLogging sign) computation).run

omit [DecidableEq Request] in
theorem runSigning_withRequestLog {α : Type} (sign : Request → OracleComp HashSpec Answer)
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) :
    runSigning sign (withRequestLog computation) = loggedRun (fun request => liftM (sign request)) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [withRequestLog_base, runSigning, simulateQ_bind, simulateQ_spec_query,
            QueryImpl.add_apply_inl, loggedRun, WriterT.run_bind, WriterT.run_liftM, bind_map_left]
          change ((liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= _) =
            ((liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= _)
          apply bind_congr
          intro answer
          simpa [loggedRun, runSigning] using ih answer
      | inr input =>
          simp only [withRequestLog_request, runSigning, simulateQ_bind, simulateQ_spec_query,
            QueryImpl.add_apply_inr, simulateQ_map, loggedRun, WriterT.run_bind,
            QueryImpl.run_withLogging_apply, bind_assoc, pure_bind]
          change (liftM (sign input) >>= _) = (liftM (sign input) >>= _)
          apply bind_congr
          intro answer
          simpa only [runSigning, loggedRun, List.singleton_append] using
            congrArg (fun computation : OracleComp OracleWorld (α × QueryLog (Request →ₒ Answer)) =>
              (fun result => (result.1, ⟨input, answer⟩ :: result.2)) <$> computation) (ih answer)

end XmssSecurity.Seeded
