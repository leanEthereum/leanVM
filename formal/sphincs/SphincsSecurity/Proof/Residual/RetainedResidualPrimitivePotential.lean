import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualCandidateHistory
import SphincsSecurity.Proof.Residual.RetainedResidualEncodingHistory
import SphincsSecurity.Proof.Residual.RetainedResidualQueryPotential
import SphincsSecurity.Proof.Residual.RetainedResidualTerminalCoverage
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def primitiveContinuation (budget : Nat) (memory : Memory) : ENNReal :=
  ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ digestBits) memory.external.probes
    ((budget : ℝ) - memory.external.hashCalls))

noncomputable def primitiveLivePotential (budget : Nat) (memory : Memory) : ENNReal :=
  (memory.messageCalls.length : ENNReal) / 2 ^ digestBits + primitiveContinuation budget memory

noncomputable def primitiveResultPotential {Result : Type} {inputs : Finset HashInput}
    (budget : Nat) (result : Option Result × State inputs) : ENNReal :=
  (result.2.memory.messageCalls.length : ENNReal) / 2 ^ digestBits +
    result.1.elim 1 (fun _ => primitiveContinuation budget result.2.memory)

theorem primitiveLivePotential_applyBoundary_le (budget : Nat) (memory : Memory) (trace : SigningBoundaryTrace)
    (hresources : ProbeMessageBound memory) (hcost : memory.external.hashCalls + trace.hashCalls ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    primitiveLivePotential budget (memory.applyBoundary trace) ≤ primitiveLivePotential budget memory := by
  have hp : (memory.external.probes : ℝ) ≤ memory.external.hashCalls := by
    exact_mod_cast (show memory.external.probes ≤ memory.external.hashCalls from
      (Nat.le_add_right _ _).trans hresources)
  have hc : (memory.external.hashCalls : ℝ) + trace.hashCalls ≤ budget := by exact_mod_cast hcost
  have hb : 2 * (budget : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hr : (0 : ℝ) ≤ budget - (memory.external.hashCalls + trace.hashCalls) := by linarith
  have hs : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hpay := PrimitiveMessagePotential.work_payment (2 ^ digestBits) memory.external.probes
    ((budget : ℝ) - (memory.external.hashCalls + trace.hashCalls)) trace.messageCalls.length trace.hashCalls hs
    (by positivity) hr (List.length_filterMap_le _ _) (by linarith)
  have hrestore : (budget : ℝ) - (memory.external.hashCalls + trace.hashCalls) + trace.hashCalls =
      budget - memory.external.hashCalls := by ring
  rw [hrestore] at hpay
  have hbounds := PrimitiveMessagePotential.bounds (2 ^ digestBits) memory.external.probes
    ((budget : ℝ) - (memory.external.hashCalls + trace.hashCalls)) hr (by linarith)
  have hpayment := ENNReal.ofReal_le_ofReal hpay
  rw [ENNReal.ofReal_add (by positivity) hbounds.1, ENNReal.ofReal_div_of_pos hs,
    ENNReal.ofReal_natCast] at hpayment
  norm_num only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at hpayment
  change (memory.messageCalls ++ trace.messageCalls).length / (2 ^ digestBits : ENNReal) +
      ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ digestBits) memory.external.probes
        ((budget : ℝ) - (memory.external.hashCalls + trace.hashCalls : Nat))) ≤ _
  rw [List.length_append, Nat.cast_add, ENNReal.add_div, Nat.cast_add, add_assoc]
  exact add_le_add le_rfl hpayment

theorem primitiveLivePotential_recordSigning (budget : Nat) (memory : Memory) (message : Message) (record : SigningRecord) :
    primitiveLivePotential budget (memory.recordSigning message record) = primitiveLivePotential budget memory := rfl

private theorem expected_indicator_value_le {Result : Type} (law : SPMF Result) (event : Result → Prop) [DecidablePred event]
    (cost value : ENNReal) :
    (∑' result, Pr[= result | law] * (cost + if event result then 1 else value)) ≤
      cost + Pr[event | law] + (1 - Pr[event | law]) * value := by
  have hcomplement : Pr[fun result => ¬event result | law] ≤ 1 - Pr[event | law] := by
    apply ENNReal.le_sub_of_add_le_left probEvent_ne_top
    rw [probEvent_compl]
    exact tsub_le_self
  have hsplit : (∑' result, Pr[= result | law] * (if event result then 1 else value)) =
      Pr[event | law] + Pr[fun result => ¬event result | law] * value := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases he : event result <;> simp [he]
  simp only [mul_add, ENNReal.tsum_add]
  rw [hsplit, ENNReal.tsum_mul_right, ← add_assoc]
  exact add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl)
    (mul_le_mul' hcomplement le_rfl)

private theorem ennreal_mixture_le (probability : ENNReal) (hprobability : probability ≤ 1)
    (value bound : ℝ) (hvalue : 0 ≤ value) (hbound : 0 ≤ bound)
    (h : probability.toReal + (1 - probability.toReal) * value ≤ bound) :
    probability + (1 - probability) * ENNReal.ofReal value ≤ ENNReal.ofReal bound := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) hprobability
  have hs : 1 - probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) tsub_le_self
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hp, ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top⟩)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add hp (ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hprobability (by simp), ENNReal.toReal_one,
    ENNReal.toReal_ofReal hvalue, ENNReal.toReal_ofReal hbound]
  exact h

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyByteRun_hash_jointPotential (routing : Routing) (input : HashInput) (hin : input ∈ inputs)
    (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory) (hquery : state.memory.external.hashCalls + 1 ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query (.inr input))) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  let law := lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
    (liftM (OracleWorld.query (.inr input))) state
  let afterProbes := (charge parameter words routing.disclosed routing.known input state.memory.external).probes
  let nextValue := PrimitiveMessagePotential.value (2 ^ digestBits) afterProbes
    ((budget : ℝ) - (state.memory.external.hashCalls + 1))
  let increment : ℝ := if FtsProbeSimulation.MessageHashInput parameter input then (2 ^ digestBits : ℝ)⁻¹ else 0
  have hlaw : law = lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.checkedHashQuery
          (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) ⟨input, hin⟩)) state := by
    simp only [law, lazyByteRun, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, dif_pos hin]
  have hp : (state.memory.external.probes : ℝ) ≤ state.memory.external.hashCalls := by
    exact_mod_cast (show state.memory.external.probes ≤ state.memory.external.hashCalls from
      (Nat.le_add_right _ _).trans hresources)
  have hc : (state.memory.external.hashCalls : ℝ) + 1 ≤ budget := by exact_mod_cast hquery
  have hb : 2 * (budget : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hs : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hap : (afterProbes : ℝ) ≤ state.memory.external.probes + 1 := by
    exact_mod_cast charge_probes_le parameter words routing.disclosed routing.known input state.memory.external
  have hn : 0 ≤ nextValue := (PrimitiveMessagePotential.bounds (2 ^ digestBits) afterProbes
    ((budget : ℝ) - (state.memory.external.hashCalls + 1)) (by linarith) (by linarith)).1
  have hi : 0 ≤ increment := by unfold increment; split <;> positivity
  have hbefore := (PrimitiveMessagePotential.bounds (2 ^ digestBits) state.memory.external.probes
    ((budget : ℝ) - state.memory.external.hashCalls) (by linarith) (by linarith)).1
  have hscalar := checkedHashQuery_joint_payment parameter inputs hencoding words publicReplies selections rows routing
    ⟨input, hin⟩ state budget hselect ha hcovered hcandidates hclean hresources hquery hbudget
  dsimp only at hscalar
  rw [← hlaw] at hscalar
  change (Pr[fun result => result.1 = none | law]).toReal +
    (1 - (Pr[fun result => result.1 = none | law]).toReal) * (increment + nextValue) ≤ _ at hscalar
  have hpayment := ennreal_mixture_le (Pr[fun result => result.1 = none | law]) probEvent_le_one _ _
    (add_nonneg hi hn) hbefore hscalar
  change (∑' result, Pr[= result | law] * primitiveResultPotential budget result) ≤ _
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        ((state.memory.messageCalls.length : ENNReal) / 2 ^ digestBits +
          if result.1 = none then 1 else ENNReal.ofReal (increment + nextValue)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | law] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        obtain ⟨actual, seed, heq⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows
          routing input hin state ha result hr
        have hhash := checkedHashResult_hashCalls parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
        have hprobes := checkedHashResult_probes parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
        have hmemory := checkedHashResult_memory parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
        rw [← heq] at hhash hprobes hmemory
        have hmessages := congrArg (fun memory : Memory => memory.messageCalls.length) hmemory
        by_cases hnone : result.1 = none
        · simp only [hnone, Memory.afterReply, Option.elim_none] at hmessages
          simp only [primitiveResultPotential, hnone, Option.elim_none, hmessages, if_pos, le_refl]
        · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hnone
          simp only [hanswer, Memory.afterReply, Option.elim_some, Memory.observeMessage] at hmessages
          simp only [primitiveResultPotential, hanswer, Option.elim_some, reduceCtorEq, if_false,
            primitiveContinuation, hhash, Nat.cast_add, Nat.cast_one, hprobes]
          by_cases hm : FtsProbeSimulation.MessageHashInput parameter input
          · simp only [if_pos hm, List.length_append, List.length_singleton] at hmessages
            rw [hmessages, Nat.cast_add, Nat.cast_one, ENNReal.add_div, add_assoc]
            unfold increment
            rw [if_pos hm, ENNReal.ofReal_add (by positivity) hn]
            simp only [one_div, ENNReal.ofReal_inv_of_pos hs,
              ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, nextValue, afterProbes, le_refl]
          · simp only [if_neg hm] at hmessages
            rw [hmessages]
            simp only [increment, if_neg hm, zero_add, nextValue, afterProbes, le_refl]
    _ ≤ (state.memory.messageCalls.length : ENNReal) / 2 ^ digestBits +
        (Pr[fun result => result.1 = none | law] +
          (1 - Pr[fun result => result.1 = none | law]) * ENNReal.ofReal (increment + nextValue)) := by
      simpa only [add_assoc] using expected_indicator_value_le law (fun result => result.1 = none)
        ((state.memory.messageCalls.length : ENNReal) / 2 ^ digestBits) (ENNReal.ofReal (increment + nextValue))
    _ ≤ _ := add_le_add le_rfl hpayment

omit parameter hencoding in
theorem lazyRun_signingProgram_jointPotential (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs) (budget : Nat)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hresources : ProbeMessageBound state.memory)
    (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hcost : ∀ result, lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0 →
        result.2.memory.external.hashCalls ≤ budget) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  calc
    _ ≤ ∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state] * primitiveLivePotential budget state.memory := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (signingProgram inputs key.parameter key.root words selections message) state] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        have hc := hcost result hr
        rw [SPMF.probOutput_eq_apply] at hr
        rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
          map_eq_bind_pure_comp] at hr
        obtain ⟨raw, hraw, hr⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hr
        have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key
          state.memory.routing.known words selections message).trans hinputs
        rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
        obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
          state.memory.routing key.root message hloop state ha hcovered raw hraw
        simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        subst result
        change primitiveLivePotential budget (raw.2.memory.recordSigning message record) ≤ _
        rw [primitiveLivePotential_recordSigning, hmemory]
        change raw.2.memory.external.hashCalls ≤ budget at hc
        rw [hmemory] at hc
        exact primitiveLivePotential_applyBoundary_le budget state.memory record.2 hresources hc hbudget
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem lazyByteRun_world_jointPotential (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hquery : state.memory.external.hashCalls + (if input matches .inr _ then 1 else 0) ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query input)) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  cases input with
  | inr input =>
      have hin : input ∈ inputs := hinputs (by
        simpa only [bind_pure] using mem_hashInputs_hash_bind input pure)
      exact lazyByteRun_hash_jointPotential parameter inputs hencoding words publicReplies selections rows routing input hin state budget
        hselect ha hcovered hcandidates hclean hresources hquery hbudget
  | inl input =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, tsum_probOutput_bind_mul]
      simp only [lazyByteRun_pure, tsum_probOutput_pure_mul, primitiveResultPotential, Option.elim_some]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem lazyRun_supported_result {Result : Type} (computation : OracleComp (World inputs) Result)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    ∃ result, lazyRun (environment parameter inputs hencoding words publicReplies selections rows) computation state result ≠ 0 := by
  have h := lazyRun_bind_const (environment parameter inputs hencoding words publicReplies selections rows) computation state ha
    (pure () : SPMF Unit)
  have hh := congrArg (fun law : SPMF Unit => Pr[= () | law]) h
  simp only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] at hh
  by_contra hn
  simp only [not_exists, not_not] at hn
  simp only [SPMF.probOutput_eq_apply, hn, tsum_zero] at hh
  exact zero_ne_one hh

omit parameter hencoding in
theorem lazyRun_request_jointPotential (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory) (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hcost : ∀ result, lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0 →
        result.2.memory.external.hashCalls ≤ budget) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (adversaryImpl inputs key.parameter key.root words selections input) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  cases input with
  | inr message =>
      exact lazyRun_signingProgram_jointPotential inputs words publicReplies selections rows key hencoding message hinputs state budget
        ha hcovered hresources hbudget hcost
  | inl input =>
      obtain ⟨result, hr⟩ := lazyRun_supported_result key.parameter inputs hencoding words publicReplies selections rows
        (adversaryImpl inputs key.parameter key.root words selections (.inl input)) state ha
      have hc := hcost result hr
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hr
      rw [lazyRun_externalProgram] at hr
      have hh := lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing input hinputs state ha result hr
      rw [hh] at hc
      change (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state] * primitiveResultPotential budget result) ≤ _
      rw [lazyRun_externalProgram]
      exact lazyByteRun_world_jointPotential key.parameter inputs hencoding words publicReplies selections rows state.memory.routing input
        hinputs state budget hselect ha hcovered hcandidates hclean hresources (by cases input <;> exact hc) hbudget

omit parameter hencoding in
theorem lazyRun_request_hashCalls_mono (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) :
    state.memory.external.hashCalls ≤ result.2.memory.external.hashCalls := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      rw [lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing input hinputs state ha result hresult]
      exact Nat.le_add_right _ _
  | inr message =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0 at hresult
      rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
        map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key
        state.memory.routing.known words selections message).trans hinputs
      rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
      obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing key.root message hloop state ha hcovered raw hraw
      simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      change state.memory.external.hashCalls ≤ raw.2.memory.external.hashCalls
      rw [hmemory]
      exact Nat.le_add_right _ _

omit parameter hencoding in
theorem lazyRun_source_hashCalls_mono {Result : Type} (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs key computation ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (result : Option Result × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state result ≠ 0) :
    state.memory.external.hashCalls ≤ result.2.memory.external.hashCalls := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨middle, hmiddle, hresult⟩ := hresult
      have hm := lazyRun_request_hashCalls_mono inputs words publicReplies selections rows key hencoding input
        ((requestInputs_subset key input next).trans hinputs) state ha hcovered middle hmiddle
      have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
      have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hm
      | some answer =>
          exact hm.trans (ih answer ((sourceInputs_next_subset key input next answer).trans hinputs) after ha' hc' result hresult)

omit parameter hencoding in
theorem lazyRun_source_jointPotential {Result : Type} (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs key computation ⊆ inputs)
    (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory) (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hcost : ∀ result, lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state result ≠ 0 →
        result.2.memory.external.hashCalls ≤ budget) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, lazyRun, runWith_pure, tsum_probOutput_pure_mul,
        primitiveResultPotential, Option.elim_some, primitiveLivePotential, le_refl]
  | query_bind input next ih =>
      have hin := (requestInputs_subset key input next).trans hinputs
      have hnext : ∀ answer, sourceInputs key (next answer) ⊆ inputs :=
        fun answer => (sourceInputs_next_subset key input next answer).trans hinputs
      have hjoined (middle : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
          (hmiddle : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (adversaryImpl inputs key.parameter key.root words selections input) state middle ≠ 0)
          (result : Option Result × State inputs)
          (hresult : middle.1.elim (pure (none, middle.2)) (fun answer =>
            lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
              (simulateQ (adversaryImpl inputs key.parameter key.root words selections) (next answer)) middle.2) result ≠ 0) :
          result.2.memory.external.hashCalls ≤ budget := by
        apply hcost result
        rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, RetainedObservation.bind_nonzero]
        exact ⟨middle, hmiddle, hresult⟩
      have hstepcost (middle : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
          (hmiddle : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (adversaryImpl inputs key.parameter key.root words selections input) state middle ≠ 0) :
          middle.2.memory.external.hashCalls ≤ budget := by
        have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
        have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
        rcases middle with ⟨answer, after⟩
        cases answer with
        | none => exact hjoined (none, after) hmiddle (none, after) (by simp)
        | some answer =>
            obtain ⟨result, hr⟩ := lazyRun_supported_result key.parameter inputs hencoding words publicReplies selections rows
              (simulateQ (adversaryImpl inputs key.parameter key.root words selections) (next answer)) after ha'
            exact (lazyRun_source_hashCalls_mono inputs words publicReplies selections rows key hencoding (next answer)
              (hnext answer) after ha' hc' result hr).trans (hjoined (some answer, after) hmiddle result hr)
      apply le_trans ?_ (lazyRun_request_jointPotential inputs words publicReplies selections rows key hencoding input hin state budget
        hselect ha hcovered hcandidates hclean hresources hbudget hstepcost)
      rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, tsum_probOutput_bind_mul]
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : Pr[= middle | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (adversaryImpl inputs key.parameter key.root words selections input) state] = 0
      · simp only [hm, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hm
        have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hm
        have hp' := lazyRun_request_hiddenCandidateBound key inputs hencoding words publicReplies selections rows input hin state
          ha hcovered hcandidates middle hm
        have hr' := lazyRun_request_probeMessageBound inputs words publicReplies selections rows key hencoding input hin state
          ha hcovered hresources middle hm
        rcases middle with ⟨answer, after⟩
        cases answer with
        | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, primitiveResultPotential, Option.elim_none, le_refl]
        | some answer =>
            have he' := lazyRun_request_encodingClean inputs words publicReplies selections rows key hencoding input hin state
              ha hcovered hclean (some answer, after) hm (by simp)
            exact ih answer (hnext answer) after ha' hc' hp' he' hr' (hjoined (some answer, after) hm)

theorem stop_add_messages_le_expected_primitivePotential {Result : Type} {inputs : Finset HashInput}
    (budget : Nat) (law : SPMF (Option Result × State inputs)) :
    Pr[fun result => result.1 = none | law] +
      (∑' result, Pr[= result | law] * (result.2.memory.messageCalls.length : ENNReal)) / 2 ^ digestBits ≤
        ∑' result, Pr[= result | law] * primitiveResultPotential budget result := by
  rw [probEvent_eq_tsum_ite, div_eq_mul_inv, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [primitiveResultPotential, mul_add, div_eq_mul_inv, mul_assoc, add_comm]
  apply add_le_add le_rfl
  cases result.1 with
  | none => simp only [if_pos, Option.elim_none, mul_one, le_refl]
  | some answer => simp only [reduceCtorEq, if_false, zero_le]

theorem primitiveLivePotential_initial_le (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposed : InitialPublicLabels words) (budget : Nat) (hcost : 1212415 ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    primitiveLivePotential budget (initialState inputs words exposed).memory ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  have hc : (1212415 : ℝ) ≤ budget := by exact_mod_cast hcost
  have hb : 2 * (budget : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hs : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hm := PrimitiveMessagePotential.mono_remaining (2 ^ digestBits) 0 ((budget : ℝ) - 1212415) budget
    (by linarith) (by linarith) (by linarith)
  rw [PrimitiveMessagePotential.initial _ (budget : ℝ) hs.ne'] at hm
  simpa only [primitiveLivePotential, primitiveContinuation, initialState, initialMemory, List.length_nil,
    Nat.cast_zero, Nat.cast_ofNat, ENNReal.zero_div, zero_add] using ENNReal.ofReal_le_ofReal hm

omit parameter inputs hencoding words publicReplies selections rows in
theorem initialMonitoredSource_joint_primitive_messages (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127) :
    Pr[fun result => result.1 = none | initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped] +
      (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped] *
        (result.2.1.memory.messageCalls.length : ENNReal)) / 2 ^ digestBits ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  let inputs := gameInputs adversary
  let words := referenceFamilyWords encoding.selections dummy
  let publicReplies := coordinateGraphLabels (initialKnown words exposed) high
  let source := FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩
  let initial := initialState inputs words exposed
  let env := environment key.parameter inputs (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    words publicReplies encoding.selections encoding.rows
  let computation := simulateQ (adversaryImpl inputs key.parameter key.root words encoding.selections) source
  let native := lazyRun env computation initial
  have herasure : (fun result => (result.1, result.2.1)) <$>
      initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped = native := by
    exact monitoredRun_erasure key inputs (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
      words publicReplies encoding.selections encoding.rows budget required stopAfter source
      (initial, initialCertificateMonitor 1212415 stopped)
  have hnativeCost (result : Option (Forgery × Bool) × State inputs) (hr : native result ≠ 0) :
      result.2.memory.external.hashCalls ≤ budget := by
    rw [← herasure, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
    obtain ⟨full, hfull, hr⟩ := hr
    simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    subst result
    exact initialMonitoredSource_hashCalls_le key adversary encoding dummy exposed high budget required stopAfter stopped
      hparameter hencoding hroot hcost full hfull
  have ha : ∀ coordinate, (initial.candidates coordinate).Nonempty := initialAllowed_nonempty words exposed
  have hc : ResidualByteFrontend.RowsCovered inputs (project initial) := initialState_rowsCovered inputs words exposed
  have hin : sourceInputs key source ⊆ inputs := sourceInputs_unlogged_subset_gameInputs adversary key
  have hd : 2 * budget ≤ 2 ^ digestBits := by
    norm_num only [digestBits]
    omega
  have hpotential := lazyRun_source_jointPotential inputs words publicReplies encoding.selections encoding.rows key
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) source hin initial budget
    (referenceEncodingAuxiliary_select encoding hencoding) ha hc (initialState_hiddenCandidateBound inputs words exposed)
    (ResidualByteFrontend.replyClean_empty _) (Nat.zero_le _) hd hnativeCost
  obtain ⟨result, hr⟩ := lazyRun_supported_result key.parameter inputs
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) words publicReplies encoding.selections encoding.rows computation initial ha
  have hminimum : 1212415 ≤ budget :=
    (lazyRun_source_hashCalls_mono inputs words publicReplies encoding.selections encoding.rows key
      (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) source hin initial ha hc result hr).trans (hnativeCost result hr)
  have h := (stop_add_messages_le_expected_primitivePotential budget native).trans
    (hpotential.trans (primitiveLivePotential_initial_le inputs words exposed budget hminimum hd))
  rw [← herasure, probEvent_map, tsum_probOutput_map_mul] at h
  exact h

omit parameter inputs hencoding words publicReplies selections rows in
theorem initialMonitoredSource_primitive_add_full_count_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127) :
    Pr[fun result => result.1 = none |
      initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] +
      (∑' result, Pr[= result |
        initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] *
          certificateBankCount result.2.2.bank) ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * (11 / 2 ^ 144 : ENNReal) := by
  let law := initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped
  let messages : ENNReal := ∑' result, Pr[= result | law] * (result.2.1.memory.messageCalls.length : ENNReal)
  have hprimitive := initialMonitoredSource_joint_primitive_messages key adversary encoding dummy exposed high budget Finset.univ
    (proposalStop stopAfter) stopped hparameter hencoding hroot hcost hbudget
  have hcoverage := expected_initialMonitoredSource_full_unit_count_le key adversary encoding dummy exposed high budget
    stopAfter stopped hparameter hencoding hroot hcost hbudget
  calc
    _ ≤ Pr[fun result => result.1 = none | law] +
        ((2 ^ 128 : ENNReal)⁻¹ * messages + (budget : ENNReal) * (11 / 2 ^ 144 : ENNReal)) :=
      add_le_add le_rfl hcoverage
    _ = (Pr[fun result => result.1 = none | law] + messages / 2 ^ digestBits) +
        (budget : ENNReal) * (11 / 2 ^ 144 : ENNReal) := by
      simp only [div_eq_mul_inv, digestBits]
      rw [mul_comm (2 ^ 128 : ENNReal)⁻¹ messages, ← add_assoc]
    _ ≤ _ := add_le_add hprimitive le_rfl

end SphincsSecurity.Concrete.RetainedResidual
