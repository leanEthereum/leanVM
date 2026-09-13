import XmssSecurity.Proof.Execution
import XmssSecurity.Proof.ConsistentQueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

structure GameOutcome where
  publicKey : PublicKey
  secretKey : SecretKey
  forgery : Forgery
  signingLog : QueryLog SigningSpec
  verified : Bool

def GameOutcome.won (outcome : GameOutcome) : Bool :=
  decide (SigningTranscript.Valid outcome.signingLog ∧
    ¬SigningTranscript.Contains outcome.signingLog outcome.forgery) && outcome.verified

theorem GameOutcome.won_eq_true_iff (outcome : GameOutcome) :
    outcome.won = true ↔
      SigningTranscript.Valid outcome.signingLog ∧
      ¬SigningTranscript.Contains outcome.signingLog outcome.forgery ∧
      outcome.verified = true := by
  classical
  simp [GameOutcome.won, and_assoc]

noncomputable def detailedGameAfterKeygen (scheme : Scheme SecretKey) (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) : OracleComp OracleWorld GameOutcome := do
  let ((forgery, signingLog) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme secretKey)
      (adversary.main publicKey)).run
  let verified ← scheme.verify publicKey forgery.epoch forgery.message forgery.signature
  return ⟨publicKey, secretKey, forgery, signingLog, verified⟩

noncomputable def detailedGameCore (scheme : Scheme SecretKey) (adversary : Adversary) :
    OracleComp OracleWorld GameOutcome := do
  let (publicKey, secretKey) ← scheme.keygen
  detailedGameAfterKeygen scheme adversary publicKey secretKey

theorem gameCore_eq_map_detailedGameCore (scheme : Scheme SecretKey) (adversary : Adversary) :
    gameCore scheme adversary = GameOutcome.won <$> detailedGameCore scheme adversary := by
  classical
  simp [gameCore, detailedGameCore, detailedGameAfterKeygen, GameOutcome.won]

noncomputable def detailedGameWithCache (scheme : Scheme SecretKey) (adversary : Adversary) :
    ProbComp (GameOutcome × QueryCache HashSpec) :=
  (simulateQ romImpl (detailedGameCore scheme adversary)).run ∅

theorem gameWithCache_eq_map_detailedGameWithCache
    (scheme : Scheme SecretKey) (adversary : Adversary) :
    gameWithCache scheme adversary =
      (fun outcome : GameOutcome × QueryCache HashSpec =>
        (outcome.1.won, outcome.2)) <$> detailedGameWithCache scheme adversary := by
  unfold gameWithCache detailedGameWithCache
  rw [gameCore_eq_map_detailedGameCore, simulateQ_map]
  rfl

theorem forgeAdvantage_eq_detailedGameWithCache
    (scheme : Scheme SecretKey) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun outcome : GameOutcome × QueryCache HashSpec => outcome.1.won = true |
        detailedGameWithCache scheme adversary] := by
  rw [forgeAdvantage_eq_gameWithCache, gameWithCache_eq_map_detailedGameWithCache,
    probEvent_map]
  rfl

/-- Retaining the detailed outcome does not change the hash-query count. -/
theorem hasHashQueryBound_iff_detailedGameCore
    (scheme : Scheme SecretKey) (adversary : Adversary) (q : Nat) :
    HasHashQueryBound scheme adversary q ↔
      HashQueryBound (detailedGameCore scheme adversary) ∅ q := by
  rw [hasHashQueryBound_iff, gameCore_eq_map_detailedGameCore, hashQueryBound_map_iff]

end XmssSecurity
