import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.CausalPublicSigning
import SphincsSecurity.Proof.Residual.RetainedResidualMessageKernel
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def cacheResult {Result : Type} {inputs : Finset HashInput} (result : Option Result × State inputs) :
    Option Result × QueryCache HashSpec := (result.1, result.2.memory.external.cache)

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

noncomputable def lazyByteRun {Result : Type} (routing : Routing)
    (computation : OracleComp OracleWorld Result) (state : State inputs) : SPMF (Option Result × State inputs) :=
  lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
    (simulateQ (embed inputs routing) (simulateQ (ResidualByteFrontend.checkedTranslate inputs
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)) computation)) state

theorem lazyByteRun_pure {Result : Type} (routing : Routing) (value : Result) (state : State inputs) :
    lazyByteRun parameter inputs hencoding words publicReplies selections rows routing (pure value) state =
      pure (some value, state) := by
  simp only [lazyByteRun, simulateQ_pure, lazyRun, runWith_pure]

theorem lazyByteRun_random_bind {Result : Type} (routing : Routing) (input : unifSpec.Domain)
    (next : unifSpec.Range input → OracleComp OracleWorld Result) (state : State inputs) :
    lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query (.inl input)) >>= next) state =
      ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= fun answer =>
        lazyByteRun parameter inputs hencoding words publicReplies selections rows routing (next answer) state) := by
  simp only [lazyByteRun, simulateQ_bind, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, embed]
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, environment, ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk,
    ← PMF.monad_map_eq_map, liftM_map, bind_map_left, bind_assoc, pure_bind, Option.elim_some, afterControl]
  rfl

theorem lazyByteRun_message_bind {Result : Type} (routing : Routing) (input : HashInput) (hin : input ∈ inputs)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input)
    (next : HashOutput → OracleComp OracleWorld Result) (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query (.inr input)) >>= next) state =
      (𝒟[(randomOracle (spec := HashSpec) input).run state.memory.external.cache] >>= fun result =>
        lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
          (next result.1) (messageState parameter state ⟨input, hin⟩ result.1)) := by
  simp only [lazyByteRun, simulateQ_bind, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, dif_pos hin]
  rw [checkedHashQuery_message parameter inputs words selections routing ⟨input, hin⟩ hmessage,
    lazyRun_bind, lazyRun_hashQuery_message parameter inputs hencoding words publicReplies selections rows routing
      ⟨input, hin⟩ hmessage state hcovered, bind_map_left]
  rfl

theorem lazyByteRun_message_rom {Result : Type} (routing : Routing)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (hmessage : ResidualByteFrontend.MessageOnly parameter computation) (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    cacheResult <$> lazyByteRun parameter inputs hencoding words publicReplies selections rows routing computation state =
      Prod.map some id <$> 𝒟[(simulateQ romImpl computation).run state.memory.external.cache] := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [lazyByteRun_pure, simulateQ_pure, StateT.run_pure, evalDist_pure, map_pure]
      rfl
  | query_bind input next ih =>
      have hnext : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      have hmnext : ∀ answer, ResidualByteFrontend.MessageOnly parameter (next answer) :=
        fun answer row hrow => hmessage row ((hashInputs_next_subset input next answer) hrow)
      cases input with
      | inl input =>
          have hrun : (romImpl (.inl input)).run state.memory.external.cache =
              (fun answer => (answer, state.memory.external.cache)) <$>
                (liftM (unifSpec.query input) : ProbComp _) := rfl
          rw [lazyByteRun_random_bind]
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hrun,
            evalDist_bind, evalDist_query, bind_map_left, map_bind]
          apply congrArg ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= ·)
          funext answer
          exact ih answer (hnext answer) (hmnext answer) state hcovered
      | inr input =>
          change HashOutput → OracleComp OracleWorld Result at next
          have hin := hinputs (mem_hashInputs_hash_bind input next)
          have hm := hmessage input (mem_hashInputs_hash_bind input next)
          rw [lazyByteRun_message_bind parameter inputs hencoding words publicReplies selections rows routing input hin hm next state hcovered]
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
            evalDist_bind, map_bind]
          apply RetainedObservation.bind_congr
          intro result hresult
          have hs : result ∈ support ((randomOracle input).run state.memory.external.cache) :=
            (mem_support_iff _ _).mpr hresult
          obtain ⟨hcache, hrows⟩ := randomOracle_messageState parameter inputs state hcovered ⟨input, hin⟩ result hs
          rw [ih result.1 (hnext result.1) (hmnext result.1) _ hrows, hcache]

theorem lazyByteRun_message_support {Result : Type} (routing : Routing)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (hmessage : ResidualByteFrontend.MessageOnly parameter computation) (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (result : Option Result × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing computation state result ≠ 0) :
    (∃ value, result.1 = some value) ∧ result.2.candidates = state.candidates := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [lazyByteRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact ⟨⟨value, rfl⟩, rfl⟩
  | query_bind input next ih =>
      have hnext : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      have hmnext : ∀ answer, ResidualByteFrontend.MessageOnly parameter (next answer) :=
        fun answer row hrow => hmessage row ((hashInputs_next_subset input next answer) hrow)
      cases input with
      | inl input =>
          rw [lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨answer, _, hresult⟩ := hresult
          exact ih answer (hnext answer) (hmnext answer) state hcovered result hresult
      | inr input =>
          change HashOutput → OracleComp OracleWorld Result at next
          have hin := hinputs (mem_hashInputs_hash_bind input next)
          have hm := hmessage input (mem_hashInputs_hash_bind input next)
          rw [lazyByteRun_message_bind parameter inputs hencoding words publicReplies selections rows routing input hin hm next state hcovered,
            RetainedObservation.bind_nonzero] at hresult
          obtain ⟨reply, hreply, hresult⟩ := hresult
          obtain ⟨_, hrows⟩ := randomOracle_messageState parameter inputs state hcovered ⟨input, hin⟩ reply
            ((mem_support_iff _ _).mpr hreply)
          exact ih reply.1 (hnext reply.1) (hmnext reply.1) _ hrows result hresult

end SphincsSecurity.Concrete.RetainedResidual
