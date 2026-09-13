import XmssSecurity.Proof.Deterministic.TranscriptReduction
import XmssSecurity.Proof.Deterministic.TrialSampling

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

def runWorldSigning {α : Type} (sign : SignRequest → OracleComp OracleWorld (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) : OracleComp OracleWorld α :=
  simulateQ (QueryImpl.ofLift OracleWorld (OracleComp OracleWorld) + sign) computation

theorem runWorldSigning_withRequestLog {α : Type} (sign : SignRequest → OracleComp OracleWorld (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    runWorldSigning sign (withRequestLog computation) = loggedRun sign computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [withRequestLog_base, runWorldSigning, simulateQ_bind, simulateQ_spec_query,
            QueryImpl.add_apply_inl, loggedRun, WriterT.run_bind, WriterT.run_liftM, bind_map_left]
          change ((liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= _) =
            ((liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= _)
          apply bind_congr
          intro answer
          simpa [loggedRun, runWorldSigning] using ih answer
      | inr input =>
          simp only [withRequestLog_request, runWorldSigning, simulateQ_bind, simulateQ_spec_query,
            QueryImpl.add_apply_inr, simulateQ_map, loggedRun, WriterT.run_bind,
            QueryImpl.run_withLogging_apply, bind_assoc, pure_bind]
          apply bind_congr
          intro answer
          simpa only [runWorldSigning, loggedRun, List.singleton_append] using
            congrArg (fun computation : OracleComp OracleWorld (α × QueryLog SigningSpec) =>
              (fun result => (result.1, ⟨input, answer⟩ :: result.2)) <$> computation) (ih answer)

theorem runWorldSigning_sourceGame (secretKey : XmssSecurity.SecretKey)
    (publicKey : PublicKey) (adversary : Adversary) :
    runWorldSigning (fun (request : SignRequest) => Concrete.precomputedCappedSign secretKey request.epoch request.message) (sourceGame publicKey adversary) =
      gameRest Concrete.scheme adversary publicKey secretKey := by
  unfold sourceGame
  rw [runWorldSigning, simulateQ_bind]
  change (runWorldSigning (fun (request : SignRequest) => Concrete.precomputedCappedSign secretKey request.epoch request.message) (withRequestLog (adversary.main publicKey)) >>=
    fun result => runWorldSigning (fun (request : SignRequest) => Concrete.precomputedCappedSign secretKey request.epoch request.message) (baseLift (finishGame publicKey result))) = _
  rw [runWorldSigning_withRequestLog]
  have hlift (result) : runWorldSigning (fun (request : SignRequest) => Concrete.precomputedCappedSign secretKey request.epoch request.message) (baseLift (finishGame publicKey result)) =
      finishGame publicKey result := by
    rw [runWorldSigning, simulateQ_baseLift, simulateQ_ofLift_eq_self]
  simp_rw [hlift]
  unfold loggedRun gameRest finishGame transcriptWin
  rfl

theorem simulateQ_runWorldSigning {α State : Type}
    (handler : QueryImpl OracleWorld (StateT State ProbComp))
    (sign : SignRequest → OracleComp OracleWorld (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ handler (runWorldSigning sign computation) =
      simulateQ (handler + fun message => simulateQ handler (sign message)) computation := by
  rw [runWorldSigning, ← QueryImpl.simulateQ_compose]
  apply congrArg (fun implementation => simulateQ implementation computation)
  funext input
  cases input with
  | inl input =>
      change simulateQ handler (liftM (OracleWorld.query input) : OracleComp OracleWorld _) = handler input
      exact simulateQ_spec_query handler input
  | inr input => rfl

end XmssSecurity.Seeded
