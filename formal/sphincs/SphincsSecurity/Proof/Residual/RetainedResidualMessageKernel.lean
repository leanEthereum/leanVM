import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.PrefixEncodingRisk
import SphincsSecurity.Proof.Residual.RetainedResidualHashTrace
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def messageState (parameter : PublicParameter) {inputs : Finset HashInput}
    (state : State inputs) (input : inputs) (answer : HashOutput) : State inputs :=
  let external := storeReply { state.memory.external with hashCalls := state.memory.external.hashCalls + 1 } input.val answer
  ⟨state.candidates,
    if state.memory.external.cache input.val = none then Function.update state.rows input (some answer) else state.rows,
    ({ state.memory with external := external } : Memory).observeMessage
        parameter input.val answer⟩

theorem messageState_cache (parameter : PublicParameter) {inputs : Finset HashInput}
    (state : State inputs) (input : inputs) (answer : HashOutput) :
    (messageState parameter state input answer).memory.external.cache =
      Function.update state.memory.external.cache input.val (some answer) := by
  simp only [messageState, observeMessage_external, storeReply]

theorem messageState_rowsCovered (parameter : PublicParameter) {inputs : Finset HashInput}
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (input : inputs) (answer : HashOutput)
    (hanswer : state.memory.external.cache input.val = none ∨ state.memory.external.cache input.val = some answer) :
    ResidualByteFrontend.RowsCovered inputs (project (messageState parameter state input answer)) := by
  intro other output hrow
  change (messageState parameter state input answer).memory.external.cache other.val = some output
  rw [messageState_cache]
  change (if state.memory.external.cache input.val = none then Function.update state.rows input (some answer)
    else state.rows) other = some output at hrow
  rcases hanswer with hfresh | hcached
  · rw [if_pos hfresh] at hrow
    by_cases heq : other = input
    · subst other
      rw [Function.update_self, Option.some.injEq] at hrow
      subst output
      exact Function.update_self ..
    · rw [Function.update_of_ne heq] at hrow
      rw [Function.update_of_ne (fun h => heq (Subtype.ext h))]
      exact hcovered other output hrow
  · rw [if_neg (by rw [hcached]; simp)] at hrow
    rw [← hcached, Function.update_eq_self]
    exact hcovered other output hrow

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_prepare_bind {Result : Type} (routing : Routing)
    (input : inputs) (next : Action inputs → OracleComp (World inputs) Result) (state : State inputs) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (embed inputs routing (.inl (.prepare input)) >>= next) state =
      let prepared := prepareState parameter inputs hencoding words publicReplies selections rows routing input state
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows) (next prepared.1) prepared.2 := by
  rw [embed, lazyRun, runWith_query_bind]
  simp only [lazyImpl, environment, ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk,
    PMF.pure_map, SPMF.lift_pure, pure_bind, Option.elim_some, lazyRun, prepareState, project]

theorem lazyRun_hashQuery_message (routing : Routing) (input : inputs)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input.val) (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) (ResidualByteFrontend.hashQuery input)) state =
      (fun result => (some result.1, messageState parameter state input result.1)) <$>
        𝒟[(randomOracle (spec := HashSpec) input.val).run state.memory.external.cache] := by
  have hdecode : decodePosition parameter input.val = none := by
    obtain ⟨payload, heq⟩ := hmessage
    rw [← heq]
    exact decodePosition_message parameter payload
  rw [ResidualByteFrontend.hashQuery, simulateQ_bind, simulateQ_spec_query, lazyRun_prepare_bind]
  cases hcache : state.memory.external.cache input.val with
  | some answer =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hcache]
      simp only [prepareState, ResidualByteFrontend.prepare, hcache, afterControl, ResidualByteFrontend.execute,
        simulateQ_pure, lazyRun, runWith_pure, evalDist_pure, map_pure, messageState,
        reduceCtorEq, if_false, charge, Nat.add_zero]
      congr 2
      unfold storeReply
      rw [← hcache, Function.update_eq_self]
  | none =>
      have hrow := ResidualByteFrontend.rowsCovered_fresh inputs (project state) hcovered input hcache
      change state.rows input = none at hrow
      rw [randomOracle, QueryImpl.withCaching_run_none _ hcache]
      simp only [prepareState, ResidualByteFrontend.prepare, hcache,
        freshPrefix_message parameter inputs hencoding words publicReplies selections rows routing input hmessage,
        afterControl, ResidualByteFrontend.execute, simulateQ_spec_query, embed, lazyRun, runWith,
        simulateQ_spec_query, lazyImpl, OptionT.run_mk, StateT.run_mk, ResidualTableCompletion.reply,
        hrow, readState, environment, messageState, if_true, charge, route, hdecode,
        Option.elim_none, Nat.add_zero]
      simp only [uniformSampleImpl, map_eq_bind_pure_comp, evalDist_bind, evalDist_pure,
        evalDist_uniformSample, bind_assoc, Function.comp_apply, pure_bind]

theorem checkedHashQuery_message (routing : Routing) (input : inputs)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input.val) :
    ResidualByteFrontend.checkedHashQuery
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input =
      ResidualByteFrontend.hashQuery input := by
  have hreject (answer : HashOutput) :
      ¬PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections input.val answer := by
    rintro ⟨position, hat, _⟩
    exact ResidualByteFrontend.message_not_encoding parameter input.val hmessage position hat
  simp only [ResidualByteFrontend.checkedHashQuery, hreject, if_false, bind_pure]

theorem randomOracle_messageState (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (input : inputs)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((randomOracle input.val).run state.memory.external.cache)) :
    (messageState parameter state input result.1).memory.external.cache = result.2 ∧
      ResidualByteFrontend.RowsCovered inputs (project (messageState parameter state input result.1)) := by
  cases hcache : state.memory.external.cache input.val with
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hcache, support_map] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      exact ⟨messageState_cache parameter state input answer,
        messageState_rowsCovered parameter state hcovered input answer (Or.inl hcache)⟩
  | some answer =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hcache, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      constructor
      · rw [messageState_cache, ← hcache, Function.update_eq_self]
      · exact messageState_rowsCovered parameter state hcovered input answer (Or.inr hcache)

theorem lazyRun_bind {A B : Type} (computation : OracleComp (World inputs) A)
    (next : A → OracleComp (World inputs) B) (state : State inputs) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows) (computation >>= next) state =
      (lazyRun (environment parameter inputs hencoding words publicReplies selections rows) computation state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer =>
          lazyRun (environment parameter inputs hencoding words publicReplies selections rows) (next answer) result.2)) := by
  simp only [lazyRun, runWith, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

end SphincsSecurity.Concrete.RetainedResidual
