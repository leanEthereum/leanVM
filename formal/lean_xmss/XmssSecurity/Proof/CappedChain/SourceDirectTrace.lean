import XmssSecurity.Proof.CappedChain.ChainInputTrace
import XmssSecurity.Proof.StateLens

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def sourceDirectMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) :=
  unloggedMappedAdversaryImpl publicKey secretKey

theorem sourceDirectMappedAdversaryImpl_eq_compose
    (publicKey : PublicKey) (secretKey : SecretKey) :
    sourceDirectMappedAdversaryImpl publicKey secretKey =
      romImpl ∘ₛ sourceUnloggedMappedAdversaryImpl publicKey secretKey := by
  funext input
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rfl
    · simp [sourceDirectMappedAdversaryImpl, unloggedMappedAdversaryImpl,
        sourceUnloggedMappedAdversaryImpl, QueryImpl.apply_compose, romImpl]
  · rfl

abbrev SourceTracedState := QueryCache HashSpec × AttackerActionTrace

noncomputable def actionTracedStateImpl
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (fragment : (input : spec.Domain) → spec.Range input →
      AttackerActionTrace) :
    QueryImpl spec (StateT (σ × AttackerActionTrace) ProbComp) :=
  fun input => StateT.mk fun state => do
    let result ← (impl input).run state.1
    pure (result.1, (result.2, state.2 ++ fragment input result.1))

noncomputable def sourceDirectTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT SourceTracedState ProbComp) :=
  actionTracedStateImpl
    (sourceDirectMappedAdversaryImpl publicKey secretKey)
    attackerActionFragment

theorem sourceDirectTracedMappedAdversaryImpl_query_run_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        (cache, trace) =
      (fun result =>
        (result.1.1, (result.2, trace ++ result.1.2))) <$>
        (simulateQ romImpl
          (sourceActionTracedMappedAdversaryImpl publicKey secretKey input).run
            ).run cache := by
  unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl
    sourceActionTracedMappedAdversaryImpl
  rw [sourceDirectMappedAdversaryImpl_eq_compose]
  simp [QueryImpl.apply_compose, QueryImpl.withTraceAppend_apply,
    map_eq_bind_pure_comp]

set_option maxRecDepth 1000000 in
theorem sourceDirectTracedMappedAdversaryImpl_run_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (cache, trace) =
      (fun result =>
        (result.1.1, (result.2, trace ++ result.1.2))) <$>
        (simulateQ romImpl
          (simulateQ (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
            computation).run).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache trace with
  | pure value => simp
  | query_bind input next ih =>
      simp only [StateT.run_bind, WriterT.run_bind', simulateQ_bind, map_bind,
        simulateQ_spec_query]
      rw [sourceDirectTracedMappedAdversaryImpl_query_run_eq]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      simpa [List.append_assoc] using
        (ih head.1.1 head.2 (trace ++ head.1.2))

noncomputable abbrev sourceDirectTracedHashVerifierImpl
    (hashInput : HashInput) : StateT SourceTracedState ProbComp HashOutput :=
  StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (randomOracle hashInput).run state.1

noncomputable def sourceDirectTracedVerifierImpl :
    QueryImpl OracleWorld (StateT SourceTracedState ProbComp) :=
  fun input =>
    match input with
    | .inl n => StateT.mk fun state =>
        (fun result => (result.1, (result.2, state.2))) <$>
          (romImpl (.inl n)).run state.1
    | .inr hashInput => sourceDirectTracedHashVerifierImpl hashInput

theorem sourceDirectTracedVerifierImpl_query_run_eq
    (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (sourceDirectTracedVerifierImpl input).run (cache, trace) =
      (fun result => (result.1, (result.2, trace))) <$>
        (romImpl input).run cache := by
  rcases input with n | hashInput <;> rfl

theorem sourceDirectTracedVerifierImpl_run_eq
    (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (simulateQ sourceDirectTracedVerifierImpl computation).run (cache, trace) =
      (fun result => (result.1, (result.2, trace))) <$>
        (simulateQ romImpl computation).run cache := by
  exact (StateLens.fst : StateLens SourceTracedState (QueryCache HashSpec)
    ).simulateQ_run_eq sourceDirectTracedVerifierImpl romImpl
    (fun input state => sourceDirectTracedVerifierImpl_query_run_eq
      input state.1 state.2) computation (cache, trace)

end XmssSecurity.CappedChain
