import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualByteHazard
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem checkedResult_stopped_iff {Memory : Type} (reject : HashInput → HashOutput → Prop) (input : HashInput)
    (result : Option HashOutput × Memory) :
    (checkedResult reject input result).1 = none ↔ result.1 = none ∨ ReturnedMatch reject input result := by
  rcases result with ⟨answer, memory⟩
  cases answer with
  | none => simp [checkedResult, ReturnedMatch]
  | some answer =>
      by_cases hreject : reject input answer <;> simp [checkedResult, returnedMatch_some, hreject]

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem lazyRun_checkedHashQuery (reject : HashInput → HashOutput → Prop) (input : inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    lazyRun (environment parameter inputs words disclosed known actions) (checkedHashQuery reject input) state =
      checkedResult reject input.val <$>
        lazyRun (environment parameter inputs words disclosed known actions) (hashQuery input) state := by
  rw [← run_erasure _ _ state ha, ← run_erasure _ _ state ha]
  simp only [map_bind, observedRun_checkedHashQuery, observedRun_hashQuery, map_pure]

theorem prob_checkedHashQuery_stop_le_add (reject : HashInput → HashOutput → Prop) (input : inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    Pr[fun result => result.1 = none |
      lazyRun (environment parameter inputs words disclosed known actions) (checkedHashQuery reject input) state] ≤
      Pr[fun result => result.1 = none |
        lazyRun (environment parameter inputs words disclosed known actions) (hashQuery input) state] +
      Pr[ReturnedMatch reject input.val |
        lazyRun (environment parameter inputs words disclosed known actions) (hashQuery input) state] := by
  rw [lazyRun_checkedHashQuery parameter inputs words disclosed known actions reject input state ha, probEvent_map]
  simp only [Function.comp_def, checkedResult_stopped_iff]
  exact probEvent_or_le _ _ _

omit actions in
theorem prob_checkedPrefixHashQuery_stop_le (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (input : inputs) (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : RowsCovered inputs state) (hbound : HiddenCandidateBound words disclosed state)
    (hclean : ReplyClean (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) state.memory.cache) :
    Pr[fun result => result.1 = none |
      lazyRun (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows)
        (checkedHashQuery (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) input) state] ≤
      probeHazard state.memory.probes := by
  apply (prob_checkedHashQuery_stop_le_add parameter inputs words disclosed known _ _ input state ha).trans
  by_cases hexists : ∃ position, AtEncodingPosition parameter input.val position
  · obtain ⟨position, hat⟩ := hexists
    have hzero := prob_hashQuery_stop_le parameter inputs words disclosed known
      (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows) input state 0 hcovered
      (freshPrefix_local parameter inputs hencoding words disclosed known publicReplies selections rows input)
      (fun row test hprobe => by
        rcases prefix_encoding_actions parameter inputs words disclosed known hencoding publicReplies selections rows hselect input position hat with
          ⟨answer, hknown, _⟩ | hread
        · rw [hknown] at hprobe; cases hprobe
        · rw [hread] at hprobe; cases hprobe)
    have hencodingRisk := prob_prefixHashQuery_encodingMatch_le parameter inputs words disclosed known hencoding publicReplies selections rows
      hselect input state hcovered hclean
    exact (add_le_add hzero hencodingRisk).trans (by simpa only [zero_add] using digest_inverse_le_probeHazard state.memory.probes)
  · have hzero : Pr[ReturnedMatch (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) input.val |
        lazyRun (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows) (hashQuery input) state] = 0 := by
      apply probEvent_eq_zero
      rintro result _ ⟨answer, _, position, hat, _⟩
      exact hexists ⟨position, hat⟩
    rw [hzero, add_zero]
    exact prob_prefixHashQuery_stop_le parameter inputs words disclosed known hencoding publicReplies selections rows input state ha hcovered hbound

end SphincsSecurity.Concrete.ResidualByteFrontend
