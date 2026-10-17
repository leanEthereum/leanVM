import XmssSecurity.Proof.CappedSigningCacheTrace

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable def cappedSourceUnloggedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp OracleWorld) := by
  intro input
  cases input with
  | inl worldInput => exact liftM (OracleWorld.query worldInput)
  | inr request =>
      exact Concrete.scheme.sign secretKey request.leafIndex request.message

theorem cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment =
      (forwardOracles + signingOracle Concrete.scheme secretKey) := by
  funext input
  cases input with
  | inl worldInput =>
      apply WriterT.ext
      simp [cappedSourceUnloggedMappedAdversaryImpl, signingLogFragment, forwardOracles]
      rfl
  | inr request =>
      simp [cappedSourceUnloggedMappedAdversaryImpl, signingLogFragment, signingOracle]

noncomputable def cappedSourceUnloggedDetailedGameAfterKeygen
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    OracleComp OracleWorld (Forgery × Bool) := do
  let forgery ← simulateQ
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)
  let verified ← Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
    forgery.signature
  pure (forgery, verified)

theorem cappedDetailedGameAfterKeygen_unloggedProjection
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (fun outcome : GameOutcome => (outcome.forgery, outcome.verified)) <$>
        detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey =
      cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey := by
  let loggedAdversary :=
    (simulateQ
      ((cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment) (adversary.main publicKey)).run
  let unloggedAdversary := simulateQ
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) := fun forgery => do
    let verified ← Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
      forgery.signature
    pure (forgery, verified)
  have hprojection : Prod.fst <$> loggedAdversary = unloggedAdversary := by
    exact QueryImpl.fst_map_run_withTraceAppend
      (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
      signingLogFragment (adversary.main publicKey)
  rw [detailedGameAfterKeygen, ←
    cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq]
  change (fun outcome : GameOutcome => (outcome.forgery, outcome.verified)) <$>
      (loggedAdversary >>= fun result => do
        let verified ← Concrete.scheme.verify publicKey result.1.leafIndex
          result.1.message result.1.signature
        pure ⟨publicKey, secretKey, result.1, result.2, verified⟩) = _
  simp only [map_bind, map_pure]
  unfold cappedSourceUnloggedDetailedGameAfterKeygen
  change (loggedAdversary >>= fun result => finish result.1) =
    unloggedAdversary >>= finish
  rw [← bind_map_left, hprojection]

end XmssSecurity
