module

public import XmssSecurity.Proof.CappedChain.ChainInputTrace
public import XmssSecurity.Proof.StateLens

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def sourceDirectMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) :=
  unloggedMappedAdversaryImpl publicKey secretKey

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
