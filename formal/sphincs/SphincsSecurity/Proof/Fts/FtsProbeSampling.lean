import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeProbability
import SphincsSecurity.Proof.Fts.FewTimeSource
import SphincsSecurity.Proof.Fts.FtsProbeOrigin
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace Concrete.FtsProbeSimulation

attribute [local semireducible] sampleFtsSecrets

abbrev RetainedRestResult := (Forgery × QueryLog SigningSpec) × Bool

noncomputable def retainedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) RetainedRestResult := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure ((forgery, log), verified)

theorem retainedGameRestComputation_verdict_projection
    (adversary : Adversary) (publicKey : PublicKey) :
    (fun result : RetainedRestResult =>
      decide (SigningTranscript.Valid result.1.2 ∧
        ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2) <$>
        retainedGameRestComputation adversary publicKey =
      tracedGameRestComputation adversary publicKey := by
  simp [retainedGameRestComputation, tracedGameRestComputation]

theorem simulateQ_expanded_retainedGameRestComputation_isQueryBoundP
    (adversary : Adversary) (secretKey : SecretKey) (q : Nat)
    (hbound : (gameRest scheme adversary
      ⟨secretKey.root, secretKey.parameter⟩ secretKey).IsQueryBoundP
        (· matches Sum.inr _) q) :
    (simulateQ (expandedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary
        ⟨secretKey.root, secretKey.parameter⟩)).IsQueryBoundP
          (· matches Sum.inr _) q := by
  let verdict := fun result : RetainedRestResult =>
        decide (SigningTranscript.Valid result.1.2 ∧
          ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2
  have heq : verdict <$>
        simulateQ (expandedAdversaryImpl secretKey)
          (retainedGameRestComputation adversary
            ⟨secretKey.root, secretKey.parameter⟩) =
      simulateQ (expandedAdversaryImpl secretKey)
        (tracedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩) := by
            rw [← retainedGameRestComputation_verdict_projection]
            simp [verdict]
  have hmap : (verdict <$>
      simulateQ (expandedAdversaryImpl secretKey)
        (retainedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩)).IsQueryBoundP
            (· matches Sum.inr _) q := by
    rw [heq, simulateQ_expanded_tracedGameRestComputation adversary secretKey]
    exact hbound
  exact (isQueryBoundP_map_iff _ verdict q).mp hmap

end Concrete.FtsProbeSimulation

end SphincsSecurity
