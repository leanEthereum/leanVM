module

public import XmssSecurity.Proof.CappedChain.ChainInputTrace
public import XmssSecurity.Proof.StateLens
public import VCVio.OracleComp.QueryTracking.SubSpec

@[expose] public section

/-!
# The source game's oracles with an action trace

`unloggedMappedAdversaryImpl` answers the adversary's oracle queries with `romImpl` and its signing
requests with the scheme's signer, keeping no signing log. `actionTracedStateImpl` adds an
attacker's action trace to a stateful implementation, which gives
`sourceDirectTracedMappedAdversaryImpl`; the verifier's `sourceDirectTracedVerifierImpl` leaves the
trace unchanged and runs as `romImpl` on the cache (`sourceDirectTracedVerifierImpl_run_eq`).
-/

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def unloggedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) := by
  classical
  intro input
  cases input with
  | inl worldInput =>
      exact romImpl worldInput
  | inr request =>
      exact simulateQ romImpl
        (Concrete.scheme.sign secretKey request.leafIndex request.message)

theorem unloggedMappedAdversaryImpl_apply_inl
    (publicKey : PublicKey) (secretKey : SecretKey)
    (worldInput : OracleWorld.Domain) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inl worldInput) =
      romImpl worldInput := by
  rfl

theorem unloggedMappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      (simulateQ romImpl
        (Concrete.scheme.sign secretKey request.leafIndex request.message) :
          StateT (QueryCache HashSpec) ProbComp (Option Signature)) := by
  rfl

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

theorem sourceDirectTracedVerifierImpl_run_eq {α : Type _}
    (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    (simulateQ sourceDirectTracedVerifierImpl computation).run (cache, trace) =
      (fun result => (result.1, (result.2, trace))) <$>
        (simulateQ romImpl computation).run cache :=
  (StateLens.fst : StateLens SourceTracedState (QueryCache HashSpec)
    ).simulateQ_run_eq sourceDirectTracedVerifierImpl romImpl
    (fun input state => sourceDirectTracedVerifierImpl_query_run_eq
      input state.1 state.2) computation (cache, trace)

end XmssSecurity.CappedChain
