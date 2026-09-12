import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateMonitor
import SphincsSecurity.Proof.Fts.DigestCompletionBank
import SphincsSecurity.Proof.Residual.RetainedResidualSigningLaw
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop bankedTargetEnvelope completedTargetBank targetCreationPrice targetCreationMultiplier
set_option backward.isDefEq.respectTransparency false

noncomputable def completedSigningBankValue (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (log : QueryLog SigningSpec) (bank : HashInput → Bool) (message : Message)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : ENNReal :=
  let after := (result.2, log ++ [⟨message, result.1.1⟩])
  bankedTargetEnvelope key reuse budget signatures required after (completedTargetBank key required after bank) false

def proposalOfSigningRecord (message : Message) (record : SigningRecord) (cache : QueryCache HashSpec) (index : Index) :
    ProposalExecutionRecord (.inr message) := ⟨record.1.1, cache, record.2, record.1.2, index⟩

theorem bankedProposalRecordValue_le_completedSigningBank (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (cover : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (record : ProposalExecutionRecord (.inr message)) (stopped : Bool) :
    bankedProposalRecordValue key reuse budget signatures required cover bank (.inr message) record stopped ≤
      completedSigningBankValue key reuse budget signatures required cover.2 bank message
        ((record.output, record.selectedView), record.cache) := by
  unfold bankedProposalRecordValue completedSigningBankValue proposalRecordLogState signingLogFragment
  apply (bankedTargetEnvelope_budget_mono key reuse signatures required _ _ stopped (Nat.sub_le budget record.trace.hashCalls)).trans
  unfold bankedTargetEnvelope
  exact bankedCacheWeight_discard_le _ _ _ _ _

theorem expected_digestCompletionValue_bank_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (cover : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (actual : Labels)
    (hsigned : SigningDigestsCached key.parameter cover.1 key.root cover.2)
    (hreuse : exactDigestReuseWeight key message cover.1 ≤ reuse) :
    (∑' result, Pr[= result | digestCompletionValue known words selections actual <$>
        (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cover.1] *
      completedSigningBankValue key reuse budget signatures required cover.2 bank message result) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required cover bank false +
        targetCreationMultiplier key cover.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required cover := by
  have h := expected_digestCompletion_bankedTarget_le key reuse budget signatures required cover bank message
    (fun loop => pure (digestCompletionValue known words selections actual loop)) id
    (by
      intro loop _ result hr
      rw [support_pure, Set.mem_singleton_iff] at hr
      subst result
      exact digestCompletionValue_preservesMessages key known words selections actual loop)
    (fun _ => false) hsigned hreuse
  change (∑' result, Pr[= result | digestCompletionValue known words selections actual <$>
    (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cover.1] *
    completedSigningBankValue key reuse budget signatures required cover.2 bank message result) ≤ _ at h
  conv at h =>
    rhs
    arg 2
    rw [← targetCreationMultiplier_sign_mul_price key reuse budget signatures required cover message]
  exact h.trans (add_le_add le_rfl (mul_le_mul' le_rfl
    (targetCreationPrice_signatures_mono key reuse budget required cover (Nat.le_succ _))))

attribute [local irreducible] lazyRun completedSigningBankValue digestCompletionValue environment ResidualByteFrontend.jointSigningProgram

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem expected_lazySigning_bank_le (routing : Routing) (key : SecretKey) (hparameter : key.parameter = parameter)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (cover : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs) (state : State inputs)
    (hcache : state.memory.external.cache = cover.1)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hsigned : SigningDigestsCached key.parameter cover.1 key.root cover.2)
    (hreuse : exactDigestReuseWeight key message cover.1 ≤ reuse) :
    (∑' result, Pr[= result | lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.jointSigningProgram inputs parameter key.root routing.known words selections message)) state] *
      result.1.elim 0 (fun record => completedSigningBankValue key reuse budget signatures required cover.2 bank message
        (record.1, result.2.memory.external.cache))) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required cover bank false +
        targetCreationMultiplier key cover.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required cover := by
  let weight : Option (Option Signature × Option FewTimeView) × QueryCache HashSpec → ENNReal := fun result =>
    result.1.elim 0 (fun value => completedSigningBankValue key reuse budget signatures required cover.2 bank message (value, result.2))
  have h := congrArg (fun law : SPMF (Option (Option Signature × Option FewTimeView) × QueryCache HashSpec) =>
    ∑' result, Pr[= result | law] * weight result)
      (lazyRun_jointSigningProgram_digestLaw parameter inputs hencoding words publicReplies selections rows routing key hparameter
        message hinputs state ha hcovered)
  rw [tsum_probOutput_map_mul, tsum_probOutput_map_mul, tsum_probOutput_bind_mul] at h
  simp only [tsum_probOutput_map_mul, weight, eraseSigningTrace, cacheResult, Option.elim_map,
    Prod.map_fst, Prod.map_snd, id_eq, Option.elim_some, Function.comp_def, hcache] at h
  rw [h]
  calc
    _ ≤ ∑' actual, Pr[= actual | UniformTableCompletion.complete state.candidates] *
        (bankedTargetEnvelope key reuse budget (signatures + 1) required cover bank false +
          targetCreationMultiplier key cover.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required cover) := by
      apply ENNReal.tsum_le_tsum
      intro actual
      apply mul_le_mul' le_rfl
      have hbound := expected_digestCompletionValue_bank_le key reuse budget signatures required cover bank message
        routing.known words selections actual hsigned hreuse
      generalize hcomputation : digestCompletionValue routing.known words selections actual <$>
        (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cover.1 = computation at hbound ⊢
      simpa only [Prod.mk.eta, probOutput_def, SPMF.evalDist_def] using hbound
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_lazySigning_certificateMonitor_le (routing : Routing) (key : SecretKey) (hparameter : key.parameter = parameter)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (message : Message)
    (monitor : CertificateMonitorState)
    (length : Option SigningRecord × State inputs → Nat) (index : Option SigningRecord × State inputs → Index)
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs) (state : State inputs)
    (hcache : state.memory.external.cache = monitor.1)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    (∑' result, Pr[= result | lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.jointSigningProgram inputs parameter key.root routing.known words selections message)) state] *
      result.1.elim 0 (fun record => certificateMonitorPotential key budget required
        (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) (.inr message) monitor (length result)
          (proposalOfSigningRecord message record result.2.memory.external.cache (index result))))) ≤
      certificateMonitorPotential key budget required monitor + certificateMonitorCharge key budget required (.inr message) monitor := by
  by_cases hactive : CertificateMonitorActive key budget (.inr message) monitor
  · have hdata := hactive
    obtain ⟨hlive, ⟨hsigned, hcapacity, _⟩, hvalid, _⟩ := hdata
    have hremaining : signatureLimit - (monitor.2.log.length + 1) + 1 = signatureLimit - monitor.2.log.length := by
      change monitor.2.log.length < signatureLimit at hvalid
      omega
    have hreuse := exactDigestReuseWeight_le_near_uniform_of_clean_cache key monitor.1 monitor.2.spent
      hcapacity.spent_le hcapacity.cache_le hcapacity.no_deficit message
    calc
      _ ≤ ∑' result, Pr[= result | lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
          (simulateQ (embed inputs routing)
            (ResidualByteFrontend.jointSigningProgram inputs parameter key.root routing.known words selections message)) state] *
        result.1.elim 0 (fun record => completedSigningBankValue key nearUniformDigestReuseWeight
          (budget - monitor.2.spent) (signatureLimit - (monitor.2.log.length + 1)) required monitor.2.log monitor.2.bank message
          (record.1, result.2.memory.external.cache)) := by
        apply ENNReal.tsum_le_tsum
        intro result
        apply mul_le_mul' le_rfl
        cases hrecord : result.1 with
        | none => exact le_rfl
        | some record =>
            simp only [Option.elim_some, certificateMonitorPotential_advance_active key budget required stopAfter
              (.inr message) monitor _ _ hactive, signingLogFragment, List.length_append, List.length_singleton]
            exact bankedProposalRecordValue_le_completedSigningBank key nearUniformDigestReuseWeight
              (budget - monitor.2.spent) (signatureLimit - (monitor.2.log.length + 1)) required (certificateMonitorCoverState monitor)
              monitor.2.bank message (proposalOfSigningRecord message record result.2.memory.external.cache (index result)) _
      _ ≤ _ := by
        have h := expected_lazySigning_bank_le parameter inputs hencoding words publicReplies selections rows routing key hparameter
          nearUniformDigestReuseWeight (budget - monitor.2.spent) (signatureLimit - (monitor.2.log.length + 1)) required
          (certificateMonitorCoverState monitor) monitor.2.bank message hinputs state hcache ha hcovered hsigned hreuse
        rw [hremaining] at h
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, hlive, certificateMonitorCharge, if_pos hactive] using h
  · rw [certificateMonitorCharge, if_neg hactive, add_zero]
    simp only [certificateMonitorPotential_advance_inactive key budget required stopAfter (.inr message) monitor _ _ hactive]
    calc
      _ ≤ ∑' result, Pr[= result | lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
          (simulateQ (embed inputs routing)
            (ResidualByteFrontend.jointSigningProgram inputs parameter key.root routing.known words selections message)) state] *
          certificateBankCount monitor.2.bank := by
        apply ENNReal.tsum_le_tsum
        intro result
        apply mul_le_mul' le_rfl
        cases result.1 <;> simp only [Option.elim_none, Option.elim_some, zero_le, le_refl]
      _ ≤ certificateBankCount monitor.2.bank := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one
      _ ≤ _ := by
        unfold certificateMonitorPotential bankedTargetEnvelope
        exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _

end SphincsSecurity.Concrete.RetainedResidual
