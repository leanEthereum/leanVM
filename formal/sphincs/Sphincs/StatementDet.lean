import Sphincs.Statement

/-!
The SUF-CMA target for the signer of the Rust implementation, `Seeded.sign`: randomizers are
derived from the master seed and the message, so a repeated request returns the same signature.
The adversary, transcript tests and counted oracle are those of `Statement`; this module adds the
forgery advantage, the hash-query budget and the security-bits target.
-/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Det

variable [Params]

noncomputable def signingOracleDet (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request : OracleComp HashSpec (Option Signature))

noncomputable def gameCoreDet (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracleDet sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def experimentDet (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCoreDet adversary)).run.run' ∅

noncomputable def forgeAdvantageDet (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experimentDet adversary]

def HasHashQueryBoundDet (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experimentDet adversary), result.2 ≤ q

def HasClassicalSecurityBitsDet (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBoundDet adversary q →
    forgeAdvantageDet adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Sphincs.Security.Det
