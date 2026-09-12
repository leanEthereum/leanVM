import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.PrimitiveMessagePotential
import SphincsSecurity.Proof.Residual.RetainedResidualHazard
import SphincsSecurity.Proof.Residual.RetainedResidualProbeBudget
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
open ResidualByteFrontend (HiddenCandidateBound)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem prob_checkedHashQuery_message_stop (routing : Routing) (input : inputs) (state : State inputs)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input.val)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    Pr[fun result => result.1 = none |
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input)) state] = 0 := by
  rw [checkedHashQuery_message parameter inputs words selections routing input hmessage,
    lazyRun_hashQuery_message parameter inputs hencoding words publicReplies selections rows routing input hmessage state hcovered,
    probEvent_map]
  simp only [Function.comp_def, reduceCtorEq, probEvent_False]

theorem checkedHashQuery_joint_payment (routing : Routing) (input : inputs) (state : State inputs) (q : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory) (hquery : state.memory.external.hashCalls + 1 ≤ q)
    (hbudget : 2 * q ≤ 2 ^ digestBits) :
    let probability := (Pr[fun result => result.1 = none |
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input)) state]).toReal
    let afterProbes := (charge parameter words routing.disclosed routing.known input.val state.memory.external).probes
    probability + (1 - probability) *
      ((if FtsProbeSimulation.MessageHashInput parameter input.val then (2 ^ digestBits : ℝ)⁻¹ else 0) +
        PrimitiveMessagePotential.value (2 ^ digestBits) afterProbes ((q : ℝ) - (state.memory.external.hashCalls + 1))) ≤
      PrimitiveMessagePotential.value (2 ^ digestBits) state.memory.external.probes ((q : ℝ) - state.memory.external.hashCalls) := by
  have hspace : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hp : state.memory.external.probes ≤ state.memory.external.hashCalls := by
    exact (Nat.le_add_right _ _).trans hresources
  have hpReal : (state.memory.external.probes : ℝ) ≤ state.memory.external.hashCalls := by exact_mod_cast hp
  have hqReal : (state.memory.external.hashCalls : ℝ) + 1 ≤ q := by exact_mod_cast hquery
  have hbudgetReal : 2 * (q : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hremaining : (0 : ℝ) ≤ q - (state.memory.external.hashCalls + 1) := by linarith
  have hsum : (state.memory.external.probes : ℝ) + (q - (state.memory.external.hashCalls + 1)) + 1 < 2 ^ digestBits := by
    linarith
  have hmin : state.memory.external.probes < 2 ^ digestBits := by
    have hpos : 0 < 2 ^ digestBits := by positivity
    omega
  have hleft : ((q : ℝ) - (state.memory.external.hashCalls + 1)) + 1 = q - state.memory.external.hashCalls := by ring
  dsimp only
  by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input.val
  · rw [prob_checkedHashQuery_message_stop parameter inputs hencoding words publicReplies selections rows routing input state hmessage hcovered,
      ENNReal.toReal_zero, zero_add, sub_zero, one_mul, if_pos hmessage,
      charge_message_probes parameter words routing input.val hmessage state.memory.external]
    have h := PrimitiveMessagePotential.message_payment (2 ^ digestBits) state.memory.external.probes
      ((q : ℝ) - (state.memory.external.hashCalls + 1)) hspace (by positivity) hremaining (by linarith)
    simpa only [one_div, hleft] using h
  · rw [if_neg hmessage, zero_add]
    have hprob := prob_checkedHashQuery_stop_le parameter inputs hencoding words publicReplies selections rows routing input state
      hselect ha hcovered hcandidates hclean
    have hfinite : ResidualByteFrontend.probeHazard state.memory.external.probes ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) tsub_le_self
    have hprobReal := ENNReal.toReal_mono hfinite hprob
    rw [ResidualByteFrontend.probeHazard, PrimitiveMessagePotential.toReal_hazard _ _ hmin] at hprobReal
    have hspaceCast : ((2 ^ digestBits : Nat) : ℝ) = 2 ^ digestBits := by push_cast; rfl
    rw [hspaceCast] at hprobReal
    have hpaid : ((charge parameter words routing.disclosed routing.known input.val state.memory.external).probes : ℝ) ≤
        state.memory.external.probes + 1 := by
      exact_mod_cast charge_probes_le parameter words routing.disclosed routing.known input.val state.memory.external
    have h := PrimitiveMessagePotential.nonmessage_step (2 ^ digestBits) state.memory.external.probes _
      ((q : ℝ) - (state.memory.external.hashCalls + 1)) _ hremaining hpaid hsum hprobReal
    simpa only [hleft] using h

end SphincsSecurity.Concrete.RetainedResidual
