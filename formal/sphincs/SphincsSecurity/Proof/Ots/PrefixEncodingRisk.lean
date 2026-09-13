import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.PrefixByteRun
import SphincsSecurity.Proof.Reference.ReferenceJointPrior
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

def ReplyClean (reject : HashInput → HashOutput → Prop) (cache : ExternalCache) : Prop :=
  ∀ input answer, cache input = some answer → ¬reject input answer

theorem replyClean_empty (reject : HashInput → HashOutput → Prop) : ReplyClean reject (fun _ => none) := by
  intro input answer hcache
  cases hcache

theorem replyClean_store (reject : HashInput → HashOutput → Prop) (cache : ExternalCache)
    (hclean : ReplyClean reject cache) (input : HashInput) (answer : HashOutput) (hsafe : ¬reject input answer) :
    ReplyClean reject (Function.update cache input (some answer)) := by
  intro other value hcache
  by_cases heq : other = input
  · subst other
    rw [Function.update_self, Option.some.injEq] at hcache
    subst value
    exact hsafe
  · rw [Function.update_of_ne heq] at hcache
    exact hclean other value hcache

theorem checkedFixedStep_replyClean (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (reject : HashInput → HashOutput → Prop) (oracle : HashInput → HashOutput)
    (input : HashInput) (memory : ExternalMemory) (hclean : ReplyClean reject memory.cache)
    (answer : HashOutput)
    (hanswer : (checkedResult reject input (fixedStep parameter words disclosed known actual oracle input memory)).1 = some answer) :
    ReplyClean reject (checkedResult reject input (fixedStep parameter words disclosed known actual oracle input memory)).2.cache := by
  unfold checkedResult fixedStep at hanswer ⊢
  cases hfixed : fixedAnswer parameter words disclosed actual oracle input with
  | none => simp only [hfixed, Option.bind_none, reduceCtorEq] at hanswer
  | some output =>
      simp only [hfixed, Option.bind_some, Option.elim_some] at hanswer ⊢
      split at hanswer
      · contradiction
      · rename_i hsafe
        exact replyClean_store reject memory.cache hclean input output hsafe

def ReturnedMatch {Memory : Type} (reject : HashInput → HashOutput → Prop) (input : HashInput)
    (result : Option HashOutput × Memory) : Prop :=
  ∃ answer, result.1 = some answer ∧ reject input answer

theorem returnedMatch_some {Memory : Type} (reject : HashInput → HashOutput → Prop)
    (input : HashInput) (answer : HashOutput) (memory : Memory) :
    ReturnedMatch reject input (some answer, memory) ↔ reject input answer := by
  simp [ReturnedMatch]

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem lazyRun_prepare_bind {Result : Type} (input : inputs)
    (next : Action inputs → OracleComp (World inputs) Result) (state : State inputs) :
    AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions)
      (liftM ((World inputs).query (.inl (.prepare input))) >>= next) state =
        let prepared := prepare parameter inputs words disclosed known actions input state.memory
        AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions)
          (next prepared.1) { state with memory := prepared.2 } := by
  rw [AdaptiveResidualLabels.lazyRun, AdaptiveResidualLabels.runWith_query_bind]
  simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
    SPMF.lift_pure, pure_bind, Option.elim_some, AdaptiveResidualLabels.lazyRun]

theorem lazyRun_execute_known (answer : HashOutput) (state : State inputs) :
    AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions)
      (execute (.known answer)) state = pure (some answer, state) := by
  exact AdaptiveResidualLabels.runWith_pure _ answer state

theorem lazyRun_execute_read (input : inputs) (state : State inputs) :
    AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions)
      (execute (.read input)) state =
        (fun answer => (some answer, AdaptiveResidualLabels.readState
          (environment parameter inputs words disclosed known actions) state input answer)) <$>
          ResidualTableCompletion.reply state.rows input := by
  simp only [AdaptiveResidualLabels.lazyRun, execute, AdaptiveResidualLabels.runWith, simulateQ_spec_query,
    AdaptiveResidualLabels.lazyImpl, OptionT.run_mk, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def]

theorem lazyImpl_rowsCovered (input : (World inputs).Domain) (state : State inputs) (hcovered : RowsCovered inputs state)
    (result : Option ((World inputs).Range input) × State inputs)
    (hresult : (AdaptiveResidualLabels.lazyImpl (environment parameter inputs words disclosed known actions) input).run.run state result ≠ 0) :
    RowsCovered inputs result.2 := by
  cases input with
  | inl input =>
      cases input with
      | prepare input =>
          simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
            SPMF.lift_pure, pure_bind, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact prepare_rowsCovered parameter inputs words disclosed known actions state hcovered input
      | random input =>
          simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
            ← PMF.monad_map_eq_map, liftM_map, bind_map_left] at hresult
          obtain ⟨answer, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
      | stop =>
          simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
            SPMF.lift_pure, pure_bind, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
      | account cost =>
          simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
            SPMF.lift_pure, pure_bind, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
  | inr input =>
      cases input with
      | read input =>
          simp only [AdaptiveResidualLabels.lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨answer, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact rowsCovered_store inputs state hcovered state.candidates input answer
      | probe input test =>
          simp only [AdaptiveResidualLabels.lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
          cases hrow : state.rows input with
          | some answer =>
              simp only [hrow, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
              subst result
              exact rowsCovered_store inputs state hcovered state.candidates input answer
          | none =>
              rw [hrow] at hresult
              rcases (RetainedObservation.observe_nonzero _ _ _ _).mp hresult with ⟨_, hstop⟩ | ⟨answer, _, hnext⟩
              · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstop
                subst result
                exact hcovered
              · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
                subst result
                exact rowsCovered_store inputs state hcovered (test.restrict state.candidates answer) input answer
      | disclose coordinate =>
          simp only [AdaptiveResidualLabels.lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨value, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered

omit actions in
theorem prefix_encoding_actions (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (input : inputs) (position : EncodingPosition) (hat : AtEncodingPosition parameter input.val position) :
    (∃ answer, freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows input = .known answer ∧
      ¬PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections input.val answer) ∨
    freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows input = .read input := by
  have hroute : route parameter words disclosed known input.val = .outside := by
    rw [route, (decodePosition_none_iff parameter input.val).mpr (fun other => hat.not_atPosition other)]
    rfl
  unfold freshPrefix
  rw [hroute]
  cases hrow : knownEncodingRowAt parameter inputs hencoding known input with
  | none => exact Or.inr rfl
  | some row =>
      simp only [Option.elim_some]
      by_cases hkept : FirstSuccessPrefix.familyKept selections row
      · simp only [if_pos hkept]
        apply Or.inl
        refine ⟨rows row, rfl, ?_⟩
        have heq := (knownEncodingRowAt_some parameter inputs hencoding known input row).mp hrow
        rw [← heq]
        exact PublicEncodingMatch.protected_not_match parameter inputs hencoding known words selections rows row (hselect row.1) hkept
      · exact Or.inr (if_neg hkept)

omit actions in
theorem prob_prefixHashQuery_encodingMatch_le (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (input : inputs) (state : State inputs) (hcovered : RowsCovered inputs state)
    (hclean : ReplyClean (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) state.memory.cache) :
    Pr[ReturnedMatch (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) input.val |
      AdaptiveResidualLabels.lazyRun
        (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows) (hashQuery input) state] ≤
      (Fintype.card Digest : ENNReal)⁻¹ := by
  by_cases hexists : ∃ position, AtEncodingPosition parameter input.val position
  · obtain ⟨position, hat⟩ := hexists
    rw [hashQuery, lazyRun_prepare_bind]
    cases hcache : state.memory.cache input.val with
    | some answer =>
        rw [prepare_cached parameter inputs words disclosed known _ input state.memory answer hcache, lazyRun_execute_known]
        simp only [probEvent_pure, returnedMatch_some, if_neg (hclean input.val answer hcache), zero_le]
    | none =>
        have hfresh := rowsCovered_fresh inputs state hcovered input hcache
        rcases prefix_encoding_actions parameter inputs words disclosed known hencoding publicReplies selections rows hselect input position hat with
          ⟨answer, haction, hsafe⟩ | haction
        · simp only [prepare, hcache, haction]
          rw [lazyRun_execute_known]
          simp only [probEvent_pure, returnedMatch_some, if_neg hsafe, zero_le]
        · simp only [prepare, hcache, haction]
          rw [lazyRun_execute_read]
          simp only [ResidualTableCompletion.reply, hfresh]
          simpa only [probEvent_map, Function.comp_def, returnedMatch_some] using
            PublicEncodingMatch.prob_match_le parameter (knownEncodingMessage known) words selections input.val
  · have hzero : Pr[ReturnedMatch (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) input.val |
        AdaptiveResidualLabels.lazyRun
          (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows) (hashQuery input) state] = 0 := by
      apply probEvent_eq_zero
      rintro result _ ⟨answer, _, position, hat, _⟩
      exact hexists ⟨position, hat⟩
    rw [hzero]
    exact bot_le

end SphincsSecurity.Concrete.ResidualByteFrontend
