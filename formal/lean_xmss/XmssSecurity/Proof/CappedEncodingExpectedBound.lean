import XmssSecurity.Proof.CappedEncodingQueryBound
import XmssSecurity.Proof.ExpectedQueryCount
import XmssSecurity.Proof.EncodingTargetMap

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedEncodingMonitor

def IsEncodingHashQuery (parameter : PublicParameter) :
    OracleWorld.Domain → Prop
  | .inr input => (encodingInputLeafIndex? parameter input).isSome
  | _ => False

theorem IsEncodingHashQuery_inr (parameter : PublicParameter) (input : HashInput) :
    IsEncodingHashQuery parameter (.inr input) =
      (encodingInputLeafIndex? parameter input).isSome := rfl

noncomputable instance (parameter : PublicParameter) :
    DecidablePred (IsEncodingHashQuery parameter) :=
  Classical.decPred _

theorem cappedUnloggedMappedAdversaryImpl_eq_source_compose
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedUnloggedMappedAdversaryImpl publicKey secretKey =
      romImpl ∘ₛ
        cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput =>
      simp [cappedUnloggedMappedAdversaryImpl,
        cappedSourceUnloggedMappedAdversaryImpl]
  | inr request => rfl

theorem cappedUnloggedMappedAdversary_simulateQ_run_eq_source
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run cache =
      (simulateQ romImpl
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
          computation)).run cache := by
  rw [cappedUnloggedMappedAdversaryImpl_eq_source_compose,
    QueryImpl.simulateQ_compose]

noncomputable def expectedPostKeygenEncodingQueries
    (adversary : Adversary) : ENNReal :=
  ∑' keyResult,
    Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[x = keyResult] *
      expectedSimulatedQueryCount romImpl
        (IsEncodingHashQuery keyResult.1.2.parameter)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2) keyResult.2

end XmssSecurity.CappedEncodingMonitor
