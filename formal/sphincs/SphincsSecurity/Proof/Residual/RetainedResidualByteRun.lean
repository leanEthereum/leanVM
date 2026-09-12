import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualCheckedTrace
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def forgetState {Result : Type} {inputs : Finset HashInput} (result : Option Result × State inputs) : Option Result × Memory :=
  (result.1, result.2.memory)

theorem afterReply_external (parameter : PublicParameter) (memory : Memory) (input : HashInput)
    (answer : Option HashOutput) (external : ExternalMemory) :
    (memory.afterReply parameter input answer external).external = external := by
  cases answer with
  | none => rfl
  | some answer => exact observeMessage_external parameter _ _ _

noncomputable def fixedByteImpl (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) : QueryImpl OracleWorld (OptionT (StateT Memory SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun memory =>
      (liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= fun answer => pure (some answer, memory)
  | .inr input => OptionT.mk <| StateT.mk fun memory => pure (fixedHashStep parameter words selections routing actual oracle input memory)

noncomputable def fixedByteRun {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld Result) (memory : Memory) :
    SPMF (Option Result × Memory) :=
  (OptionT.run (simulateQ (fixedByteImpl parameter words selections routing actual oracle) computation)).run memory

theorem fixedByteRun_pure {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (value : Result) (memory : Memory) :
    fixedByteRun parameter words selections routing actual oracle (pure value) memory = pure (some value, memory) := by
  simp only [fixedByteRun, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

theorem fixedByteRun_query_bind {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) (memory : Memory) :
    fixedByteRun parameter words selections routing actual oracle (liftM (OracleWorld.query input) >>= next) memory =
      ((fixedByteImpl parameter words selections routing actual oracle input).run.run memory >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer => fixedByteRun parameter words selections routing actual oracle (next answer) result.2)) := by
  simp only [fixedByteRun, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

theorem fixedHashStep_external (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : HashInput) (memory : Memory) :
    (fixedHashStep parameter words selections routing actual oracle input memory).2.external =
      (ResidualByteFrontend.fixedStep parameter words routing.disclosed routing.known actual oracle input memory.external).2 := by
  exact afterReply_external parameter memory input _ _

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

noncomputable def byteRun {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp OracleWorld Result) (state : State inputs) :=
  observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
    (simulateQ (embed inputs routing) (simulateQ (ResidualByteFrontend.checkedTranslate inputs
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)) computation)) state

theorem byteRun_pure {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (value : Result) (state : State inputs) :
    byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed (pure value) state = pure (some value, state) := by
  simp only [byteRun, simulateQ_pure, observedRun, runWith_pure]

theorem byteRun_random_bind {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : unifSpec.Domain) (next : unifSpec.Range input → OracleComp OracleWorld Result) (state : State inputs) :
    byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed (liftM (OracleWorld.query (.inl input)) >>= next) state =
      ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= fun answer =>
        byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed (next answer) state) := by
  simp only [byteRun, simulateQ_bind, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, embed]
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, environment, ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk,
    ← PMF.monad_map_eq_map, liftM_map, bind_map_left, bind_assoc, pure_bind, Option.elim_some,
    afterControl, project]
  rfl

theorem byteRun_hash_bind {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : HashInput) (hin : input ∈ inputs) (next : HashOutput → OracleComp OracleWorld Result) (state : State inputs) :
    byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed (liftM (OracleWorld.query (.inr input)) >>= next) state =
      let result := checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
      result.1.elim (pure (none, result.2)) (fun answer =>
        byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed (next answer) result.2) := by
  simp only [byteRun, simulateQ_bind, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, dif_pos hin]
  rw [observedRun_bind, observedRun_checkedHashQuery, pure_bind]
  rfl

theorem checkedHashResult_rowsCovered (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (input : inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    ResidualByteFrontend.RowsCovered inputs (project
      (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2) := by
  have h := ResidualByteFrontend.hashQueryResult_rowsCovered parameter inputs words routing.disclosed routing.known
    (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
    actual seed (project state) hcovered input
  have heq := congrArg Prod.snd (hashResult_project parameter inputs hencoding words publicReplies selections rows routing actual seed input state)
  rw [← heq] at h
  exact h

theorem byteRun_eq_fixed {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (oracle : QueryImpl HashSpec Id)
    (hfresh : ∀ input : inputs, ResidualByteAction.eval actual seed
      (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input) =
      ResidualByteFrontend.fixedAnswer parameter words routing.disclosed actual oracle input.val)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs) (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches oracle state.memory.external.cache)
    (hclean : CacheClean parameter words routing.disclosed actual state.memory.external.cache) :
    forgetState <$> byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed computation state =
      fixedByteRun parameter words selections routing actual oracle computation state.memory := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [byteRun_pure, fixedByteRun_pure, map_pure, forgetState]
  | query_bind input next ih =>
      have hnext : ∀ answer, hashInputs (next answer) ⊆ inputs := fun answer => (hashInputs_next_subset input next answer).trans hinputs
      cases input with
      | inl input =>
          rw [byteRun_random_bind, fixedByteRun_query_bind]
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some, map_bind]
          apply congrArg (_ >>= ·)
          funext answer
          exact ih answer (hnext answer) state hcovered hmatches hclean
      | inr input =>
          change HashOutput → OracleComp OracleWorld Result at next
          have hin : input ∈ inputs := hinputs (mem_hashInputs_hash_bind input next)
          rw [byteRun_hash_bind parameter inputs hencoding words publicReplies selections rows routing actual seed input hin, fixedByteRun_query_bind]
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, pure_bind]
          have hstep := checkedHashResult_eq_fixed parameter inputs hencoding words publicReplies selections rows routing actual seed
            oracle ⟨input, hin⟩ state (hfresh ⟨input, hin⟩) hcovered hmatches hclean
          dsimp only at hstep
          have hafter := ResidualByteFrontend.fixedStep_preserves parameter words routing.disclosed routing.known actual oracle input state.memory.external hmatches hclean
          rw [← fixedHashStep_external parameter words selections routing actual oracle input state.memory, ← hstep] at hafter
          rw [← hstep]
          have hcovered' := checkedHashResult_rowsCovered parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state hcovered
          generalize hresult : checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state = result at *
          rcases result with ⟨answer, after⟩
          cases answer with
          | none => simp only [Option.elim_none, map_pure, forgetState]
          | some answer => exact ih answer (hnext answer) after hcovered' hafter.1 hafter.2.1

end SphincsSecurity.Concrete.RetainedResidual
