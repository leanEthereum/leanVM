module

public import XmssSecurity.Proof.CappedUnloggedSource
public import XmssSecurity.Proof.EncodingTargetMap
public import XmssSecurity.Proof.CappedSigningCacheTrace

@[expose] public section

/-!
# Encoding hash queries and the capped source implementation

`IsEncodingHashQuery parameter` holds the hash queries at an encoding input of some leaf index
(`encodingInputLeafIndex?`). The capped adversary's implementation
`cappedUnloggedMappedAdversaryImpl` is `romImpl` composed with
`cappedSourceUnloggedMappedAdversaryImpl` (`cappedUnloggedMappedAdversaryImpl_eq_source_compose`,
`cappedUnloggedMappedAdversary_simulateQ_run_eq_source`). `CappedUnifiedExpectedDigest`,
`OwnSecondLane` and the `Scan` modules use them.
-/

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

theorem cappedUnloggedMappedAdversary_simulateQ_run_eq_source {α : Type _}
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

end XmssSecurity.CappedEncodingMonitor
