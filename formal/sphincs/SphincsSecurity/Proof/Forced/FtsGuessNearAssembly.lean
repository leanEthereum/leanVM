import SphincsSecurity.Proof.Forced.FtsGuessExceptionClassification
import SphincsSecurity.Proof.Residual.RetainedResidualTerminalCoverage
import SphincsSecurity.Proof.Fts.NearCertificateBound
import SphincsSecurity.Proof.Forced.Security127SmallBudgetArithmetic
/-!
The forced FTS near-certificate game is bounded slot by slot. One forced run is monitored by the certificate monitor of the retained residual chain, with the keygen debit, the fixed-length proposal word and the prefix stop rule, exactly as the original certificate games were. A near certificate on an unstopped monitor is a banked certificate, so its probability is at most the expected creation cost, which the proposal-word martingale bounds by the budget times the average terminal certificate price. A stopped monitor is a cache exception or a prefix exception, each of which is rare. The bound `nearCertificateBound` sums the two over the fourteen omitted trees.
-/

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State initialState)
open RetainedResidual (proposalStop signingInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  UniformTableCompletion.complete

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (hauxiliary : ∀ seed : inputs → HashOutput,
    (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

private theorem law_ne_zero_of_mem_support {α : Type} (law : SPMF α) (x : α) (h : x ∈ support law) : law x ≠ 0 :=
  (mem_support_iff_evalDist_apply_ne_zero _ _).mp h

private theorem pmf_mem_of_evalDist {Result : Type} (law : PMF Result) (result : Result)
    (hresult : result ∈ support 𝒟[law]) : result ∈ law.support := by
  change result ∈ (𝒟[law]).support at hresult
  simpa only [PMF.evalDist_eq, SPMF.support_liftM] using hresult

/-- The monitored start of a forced run: the empty cache, the fresh guess state and the keygen debit. -/
abbrev nearStart (spent : Nat) (stopped : Bool) : MonitoredState :=
  ((∅, initialState PUnit.unit), initialCertificateMonitor spent stopped)

/-- The forced run of the whole near game for fixed sampled parameters. -/
@[reducible] noncomputable def nearLaw (adversary : Adversary) : SPMF (Completed × CachedState) :=
  cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
    (completedRun parameter root labels adversary) (∅, initialState PUnit.unit)

/-- A near certificate whose covered trees omit exactly `omitted`. -/
def NearCertificateOmitting (omitted : FtsTree) (result : Completed) : Prop :=
  SigningTranscript.Valid result.1.1.1.2 ∧
    TargetCertificateAt (monitorKey parameter root) (Finset.univ.erase omitted)
      (hashRowsCache (result.1.1.2 * result.2.1.2).messageCalls, result.1.1.1.2)
      (signingInput (monitorKey parameter root) result.1.1.1.1.message result.1.1.1.1.signature)

theorem completedNearCertificate_exists (result : Completed) (hnear : completedNearCertificate parameter root result) :
    ∃ omitted, NearCertificateOmitting parameter root omitted result := by
  obtain ⟨hvalid, omitted, hcertificate⟩ := hnear
  exact ⟨omitted, hvalid, hcertificate⟩

theorem nearStart_valid (spent : Nat) (stopped : Bool) : Valid (nearStart spent stopped) :=
  fun _ => Finset.univ_nonempty

include hauxiliary in
theorem near_alive_le (budget : Nat) (adversary : Adversary) (omitted : FtsTree) (spent : Nat) (stopped : Bool) (total : Nat)
    (hbudget : budget ≤ 2 ^ 127) (hpool : stopped = false → 25313293 ≤ total)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) (nearStart spent stopped))
    (hwork : ∀ result : Completed × CachedState,
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary result ≠ 0 →
        completedWork result.1 ≤ budget) :
    Pr[fun result => NearCertificateOmitting parameter root omitted result.1 ∧ result.2.2.stopped = false |
        monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
          (proposalStop (fun _ _ _ _ => false)) adversary (nearStart spent stopped)] ≤
      (budget : ENNReal) *
        terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice (Finset.univ.erase omitted)) [] := by
  have hvalid := nearStart_valid spent stopped
  have heraseMon : (fun result => (result.1, result.2.1)) <$>
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
        (proposalStop (fun _ _ _ _ => false)) adversary (nearStart spent stopped) =
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary :=
    monitoredCompletedRun_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
      (proposalStop (fun _ _ _ _ => false)) adversary (nearStart spent stopped)
  have herase : Prod.map id Prod.snd <$>
      proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
        (proposalStop (fun _ _ _ _ => false)) adversary ([], nearStart spent stopped) =
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
        (proposalStop (fun _ _ _ _ => false)) adversary (nearStart spent stopped) :=
    proposalCompletedRun_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
      (proposalStop (fun _ _ _ _ => false)) adversary ([], nearStart spent stopped)
  have hcount : Pr[fun result => NearCertificateOmitting parameter root omitted result.1 ∧ result.2.2.stopped = false |
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
        (proposalStop (fun _ _ _ _ => false)) adversary (nearStart spent stopped)] ≤
      ∑' result, Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) adversary (nearStart spent stopped)] *
        certificateBankCount result.2.2.bank := by
    apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
    intro result hmem hevent
    have hresult := law_ne_zero_of_mem_support _ _ hmem
    obtain ⟨⟨_, hcertificate⟩, halive⟩ := hevent
    exact monitoredCompletedRun_certificate_count parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
      (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) hauxiliary adversary spent stopped hcovered result hresult halive _
      hcertificate
  have hcost := expected_monitoredCompletedRun_count_le_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot
    budget (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) hauxiliary adversary spent stopped hcovered
  have hinv : ProposalInvariant parameter root total ([], nearStart spent stopped) :=
    certificateProposalInvariant_initial (monitorKey parameter root) total spent ∅ stopped hpool
  have hmass := expected_proposalCompletedRun_creationCost_le_mass_terminalPotential parameter root otsSecret labels inputs hencoding
    selections rows dummy slot budget (Finset.univ.erase omitted) (fun _ _ _ _ => false) hauxiliary total adversary ([], nearStart spent stopped)
    hvalid hcovered hbudget hinv
  have hmartingale := expected_proposalCompletedRun_terminalPotential parameter root otsSecret labels inputs hencoding selections rows dummy
    slot budget (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) hauxiliary adversary ([], nearStart spent stopped) hvalid
    hcovered total (terminalCertificatePrice (Finset.univ.erase omitted))
  have hpoint : ∀ result : Completed × ProposalState,
      Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) adversary ([], nearStart spent stopped)] *
        (result.2.2.2.creationMass *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice (Finset.univ.erase omitted)) result.2.1) ≤
      Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) adversary ([], nearStart spent stopped)] *
        ((budget : ENNReal) *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice (Finset.univ.erase omitted)) result.2.1) := by
    intro result
    by_cases hzero : Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) adversary ([], nearStart spent stopped)] = 0
    · rw [hzero, zero_mul, zero_mul]
    · rw [SPMF.probOutput_eq_apply] at hzero
      have hmon := map_nonzero_of _ (Prod.map id Prod.snd) result hzero
      rw [herase] at hmon
      have hmassle := monitoredCompletedRun_creationMass_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) hauxiliary adversary spent stopped hcovered _ hmon
      have hlaw := map_nonzero_of _ (fun result => (result.1, result.2.1)) _ hmon
      rw [heraseMon] at hlaw
      have hwork' : completedWork result.1 ≤ budget := hwork _ hlaw
      have hmassle' : result.2.2.2.creationMass ≤ (completedWork result.1 : ENNReal) := hmassle
      exact mul_le_mul' le_rfl (mul_le_mul' (hmassle'.trans (by exact_mod_cast hwork')) le_rfl)
  calc
    _ ≤ _ := hcount
    _ ≤ _ := hcost
    _ = ∑' result, Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) adversary ([], nearStart spent stopped)] *
        result.2.2.2.creationCost := by
      rw [← herase, tsum_probOutput_map_mul]
      simp only [Prod.map_snd]
    _ ≤ ([], nearStart spent stopped).2.2.creationCost + _ := hmass
    _ = ∑' result, Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) adversary ([], nearStart spent stopped)] *
        (result.2.2.2.creationMass *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice (Finset.univ.erase omitted)) result.2.1) := by
      simp only [nearStart, initialCertificateMonitor, zero_add]
    _ ≤ _ := ENNReal.tsum_le_tsum hpoint
    _ = (budget : ENNReal) * ∑' result, Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy
        slot budget (Finset.univ.erase omitted) (proposalStop (fun _ _ _ _ => false)) adversary ([], nearStart spent stopped)] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice (Finset.univ.erase omitted)) result.2.1 := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      ring
    _ = _ := by rw [hmartingale]

include hauxiliary in
theorem near_stopped_le (budget : Nat) (adversary : Adversary) (required : Finset FtsTree) (total : Nat) (hbudget : budget ≤ 2 ^ 127)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) (nearStart 1212415 (decide (total < 25313293))))
    (hwork : ∀ result : Completed × CachedState,
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary result ≠ 0 →
        1212415 + completedWork result.1 ≤ budget) :
    Pr[fun result => SigningTranscript.Valid result.1.1.1.1.2 ∧ result.2.2.stopped = true |
        monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)))] ≤
      (if total < 25313293 then 1 else 0) + (budget : ENNReal) * certificateCacheExceptionRate + (2 ^ 700 : ENNReal)⁻¹ := by
  by_cases hshort : total < 25313293
  · rw [if_pos hshort]
    exact probEvent_le_one.trans (le_self_add.trans le_self_add)
  rw [if_neg hshort, zero_add]
  have hstopped : decide (total < 25313293) = false := decide_eq_false hshort
  have hvalid := nearStart_valid 1212415 (decide (total < 25313293))
  have heraseMon : (fun result => (result.1, result.2.1)) <$>
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293))) =
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary :=
    monitoredCompletedRun_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)))
  have herase : (fun result => (result.1, result.2.1)) <$>
      exceptionCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)), (false, false)) =
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293))) :=
    exceptionCompletedRun_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)), (false, false))
  have hsized : Sized (nearStart 1212415 (decide (total < 25313293))) :=
    ⟨0, by
      show QueryCache.enncard (∅ : QueryCache HashSpec) ≤ ((0 : Nat) : ENNReal)
      rw [QueryCache.enncard_empty]
      exact zero_le⟩
  have hcons : Consistent parameter root (nearStart 1212415 (decide (total < 25313293))) := by
    refine ⟨?_, ?_⟩
    · show QueryCache.enncard (∅ : QueryCache HashSpec) ≤ ((1212415 : Nat) : ENNReal)
      rw [QueryCache.enncard_empty]
      exact zero_le
    · intro entry hentry
      exact (List.not_mem_nil hentry).elim
  have halive : (nearStart 1212415 (decide (total < 25313293))).2.stopped = false := hstopped
  have hwork' : ∀ result : Completed × ExceptionState,
      exceptionCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)), (false, false)) result ≠ 0 →
        1212415 + completedWork result.1 ≤ budget := by
    intro result hresult
    have hmon := map_nonzero_of _ (fun result => (result.1, result.2.1)) result hresult
    rw [herase] at hmon
    have hlaw := map_nonzero_of _ (fun result => (result.1, result.2.1)) _ hmon
    rw [heraseMon] at hlaw
    exact hwork _ hlaw
  rw [← herase, probEvent_map]
  refine le_trans (probEvent_mono (q := fun result : Completed × ExceptionState => result.2.2.1 = true ∨ result.2.2.2 = true) ?_) ?_
  · intro result hmem hevent
    have hresult := law_ne_zero_of_mem_support _ _ hmem
    obtain ⟨hvalidLog, hstoppedTrue⟩ := hevent
    by_contra hflags
    have hclean : result.2.2 = (false, false) := by
      simp only [not_or, Bool.not_eq_true] at hflags
      exact Prod.ext hflags.1 hflags.2
    have hlog : result.1.1.1.1.2.length ≤ signatureLimit := hvalidLog
    have hunstopped := exceptionCompletedRun_unstopped parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      hauxiliary adversary (nearStart 1212415 (decide (total < 25313293)), (false, false)) hvalid hcovered hcons halive hbudget result hresult
      (hwork' result hresult) (by simpa only [initialCertificateMonitor, List.length_nil, zero_add] using hlog) hclean
    have hstoppedTrue' : result.2.1.2.stopped = true := hstoppedTrue
    rw [hunstopped] at hstoppedTrue'
    exact Bool.false_ne_true hstoppedTrue'
  refine (probEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
  · refine (exceptionCompletedRun_cache_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop (fun _ _ _ _ => false)) hauxiliary adversary (nearStart 1212415 (decide (total < 25313293)), (false, false)) hvalid hcovered
      hsized).trans ?_
    have hweight : cacheHistoryWeight parameter root (nearStart 1212415 (decide (total < 25313293)), (false, false)) = 0 := by
      simp only [cacheHistoryWeight, Bool.false_eq_true, if_false]
      exact certificateCacheExceptionWeight_initial _ _ (fun _ _ => rfl)
    rw [hweight, zero_add]
    apply mul_le_mul' ?_ le_rfl
    calc
      _ ≤ ∑' result, Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          required (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)))] * (budget : ENNReal) := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hzero : Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
            required (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)))] = 0
        · rw [hzero, zero_mul, zero_mul]
        · rw [SPMF.probOutput_eq_apply] at hzero
          have hlaw := map_nonzero_of _ (fun result => (result.1, result.2.1)) result hzero
          rw [heraseMon] at hlaw
          have hbound : 1212415 + completedWork result.1 ≤ budget := hwork _ hlaw
          exact mul_le_mul' le_rfl (by exact_mod_cast (show completedWork result.1 ≤ budget by omega))
      _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · refine (exceptionCompletedRun_prefix_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)), (false, false)) (Nat.zero_le _)).trans ?_
    simp only [prefixHistoryWeight, Bool.false_eq_true, if_false, initialCertificateMonitor, List.length_nil]
    exact proposalPrefixWeight_initial_le

include hauxiliary in
theorem near_omitting_total_le (budget : Nat) (adversary : Adversary) (omitted : FtsTree) (total : Nat) (hbudget : budget ≤ 2 ^ 127)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) (nearStart 1212415 (decide (total < 25313293))))
    (hwork : ∀ result : Completed × CachedState,
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary result ≠ 0 →
        1212415 + completedWork result.1 ≤ budget) :
    Pr[fun result => NearCertificateOmitting parameter root omitted result.1 |
        nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary] ≤
      (budget : ENNReal) *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice (Finset.univ.erase omitted)) [] +
        ((if total < 25313293 then 1 else 0) + (budget : ENNReal) * certificateCacheExceptionRate + (2 ^ 700 : ENNReal)⁻¹) := by
  have heraseMon : (fun result => (result.1, result.2.1)) <$>
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
        (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293))) =
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary :=
    monitoredCompletedRun_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget (Finset.univ.erase omitted)
      (proposalStop (fun _ _ _ _ => false)) adversary (nearStart 1212415 (decide (total < 25313293)))
  rw [← heraseMon, probEvent_map]
  refine le_trans (probEvent_mono (q := fun result : Completed × MonitoredState =>
    (NearCertificateOmitting parameter root omitted result.1 ∧ result.2.2.stopped = false) ∨
      (SigningTranscript.Valid result.1.1.1.1.2 ∧ result.2.2.stopped = true)) ?_) ?_
  · intro result _ hevent
    have hnear : NearCertificateOmitting parameter root omitted result.1 := hevent
    cases hstopped : result.2.2.stopped
    · exact Or.inl ⟨hnear, rfl⟩
    · exact Or.inr ⟨hnear.1, rfl⟩
  refine (probEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
  · exact near_alive_le parameter root otsSecret labels inputs hencoding selections rows dummy slot hauxiliary budget adversary omitted 1212415 _
      total hbudget (fun h => Nat.le_of_not_lt (of_decide_eq_false h)) hcovered (fun result h => by have := hwork result h; omega)
  · exact near_stopped_le parameter root otsSecret labels inputs hencoding selections rows dummy slot hauxiliary budget adversary
      (Finset.univ.erase omitted) total hbudget hcovered hwork

include hauxiliary in
theorem near_omitting_le (budget : Nat) (adversary : Adversary) (omitted : FtsTree) (hbudget : budget ≤ 2 ^ 127)
    (hcovered : ∀ monitor, CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩)
      ((∅, initialState PUnit.unit), monitor))
    (hwork : ∀ result : Completed × CachedState,
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary result ≠ 0 →
        1212415 + completedWork result.1 ≤ budget) :
    Pr[fun result => NearCertificateOmitting parameter root omitted result.1 |
        nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary] ≤
      (budget : ENNReal) * (((557 : ENNReal) / 14) / (2 ^ 128 : Nat)) +
        ((budget : ENNReal) * certificateCacheExceptionRate + (2 ^ 700 : ENNReal)⁻¹) := by
  have hcard : (Finset.univ.erase omitted).card = 13 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have h : Fintype.card FtsTree = 14 := Fintype.card_fin _
    rw [h]
  have h := near_omitting_total_le parameter root otsSecret labels inputs hencoding selections rows dummy slot hauxiliary budget
    adversary omitted fixedProposalLength hbudget (hcovered _) hwork
  rw [if_neg (show ¬ (fixedProposalLength < 25313293) from Nat.lt_irrefl _), zero_add, RetainedResidual.terminalProposalPotential_empty] at h
  exact h.trans (add_le_add (mul_le_mul' le_rfl (uniformWordAverage_nearPrice _ hcard)) le_rfl)

include hauxiliary in
theorem nearLaw_certificate_le (budget : Nat) (adversary : Adversary) (hbudget : budget ≤ 2 ^ 127)
    (hcovered : ∀ monitor, CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩)
      ((∅, initialState PUnit.unit), monitor))
    (hwork : ∀ result : Completed × CachedState,
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary result ≠ 0 →
        1212415 + completedWork result.1 ≤ budget) :
    Pr[fun result => completedNearCertificate parameter root result.1 |
        nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary] ≤ nearCertificateBound budget := by
  calc
    _ ≤ ∑ omitted : FtsTree, Pr[fun result => NearCertificateOmitting parameter root omitted result.1 |
        nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary] := by
      simp_rw [probEvent_eq_tsum_ite]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply ENNReal.tsum_le_tsum
      intro result
      split_ifs with hnear
      · obtain ⟨omitted, homitted⟩ := completedNearCertificate_exists parameter root result.1 hnear
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ omitted))
        rw [if_pos homitted]
      · exact zero_le
    _ ≤ ∑ _omitted : FtsTree, ((budget : ENNReal) * (((557 : ENNReal) / 14) / (2 ^ 128 : Nat)) +
        ((budget : ENNReal) * certificateCacheExceptionRate + (2 ^ 700 : ENNReal)⁻¹)) :=
      Finset.sum_le_sum fun omitted _ => near_omitting_le parameter root otsSecret labels inputs hencoding selections rows dummy slot
        hauxiliary budget adversary omitted hbudget hcovered hwork
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h : Fintype.card FtsTree = 14 := Fintype.card_fin _
      rw [h, nearCertificateBound]
      simp only [Nat.cast_ofNat]

end SphincsSecurity.Concrete.FtsGuessHash

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec ENNReal
open SecretGuessObservation (initialState)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition

theorem cachedNearGame_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hbudget : q ≤ 2 ^ 127) (slot : Nat) :
    Pr[fun hit => hit = true | cachedNearGame dummy adversary slot] ≤ nearCertificateBound q := by
  unfold cachedNearGame
  refine probEvent_bind_le_of_forall_le fun parameter _ => ?_
  refine probEvent_bind_le_of_forall_le fun otsSecret _ => ?_
  refine probEvent_bind_le_of_forall_le fun selections hselections => ?_
  refine probEvent_bind_le_of_forall_le fun rows hrows => ?_
  refine probEvent_bind_le_of_forall_le fun labels _ => ?_
  rw [probEvent_map]
  have hsel := pmf_mem_of_evalDist _ _ hselections
  have hrow := pmf_mem_of_evalDist _ _ hrows
  have hauxiliary : ∀ seed : canonicalGraphGameInputs adversary → HashOutput,
      (⟨selections, Function.uncurry rows, seed⟩ : ReferenceAuxiliary (canonicalGraphGameInputs adversary)) ∈
        (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support :=
    fun seed => referenceAuxiliary_mem_support _ selections hsel rows hrow seed
  have hcovered : ∀ monitor, CoveredRun parameter (canonicalGraphRoot labels) otsSecret (canonicalGraphGameInputs adversary)
      (adversary.main ⟨canonicalGraphRoot labels, parameter⟩) ((∅, initialState PUnit.unit), monitor) :=
    fun _ secrets _ =>
      coveredInputs_main_subset adversary ⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩
  have hwork : ∀ result : Completed × CachedState,
      nearLaw parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary parameter) selections (Function.uncurry rows) dummy slot adversary result ≠ 0 →
        1212415 + completedWork result.1 ≤ q := by
    intro result hresult
    have h := cachedForcedRun_original_budget dummy adversary q slot hbound parameter otsSecret labels
      ⟨selections, Function.uncurry rows, fun _ => Classical.arbitrary _⟩ (hauxiliary _)
    have hsel' : (⟨selections, Function.uncurry rows, fun _ => Classical.arbitrary _⟩ :
      ReferenceAuxiliary (canonicalGraphGameInputs adversary)).selections = selections := rfl
    have hrows' : (⟨selections, Function.uncurry rows, fun _ => Classical.arbitrary _⟩ :
      ReferenceAuxiliary (canonicalGraphGameInputs adversary)).rows = Function.uncurry rows := rfl
    rw [hsel', hrows'] at h
    exact (h result hresult).1
  have h := nearLaw_certificate_le parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter) selections (Function.uncurry rows) dummy slot hauxiliary q adversary
    hbudget hcovered hwork
  simpa only [Function.comp_def, decide_eq_true_eq] using h

theorem forcedNearGame_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hbudget : q ≤ 2 ^ 127) (slot : Nat) :
    Pr[fun hit => hit = true | forcedNearGame dummy adversary slot] ≤ nearCertificateBound q := by
  rw [forcedNearGame_cached]
  exact cachedNearGame_le dummy adversary q hbound hbudget slot

end SphincsSecurity.Concrete.FtsGuessHash
