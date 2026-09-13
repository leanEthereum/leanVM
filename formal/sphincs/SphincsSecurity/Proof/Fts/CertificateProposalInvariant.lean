import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ProposalPrefixStop
import SphincsSecurity.Proof.Fts.TerminalProposalEnvelope
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem originalProposalRecord_cache_le (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    cache ≤ record.cache := by
  have hm := (PMF.mem_support_map_iff (fun record : ProposalExecutionRecord input =>
    (record.output, record.cache)) _ _).mpr ⟨record, hr, rfl⟩
  rw [originalProposalRecord_project, originalAdversaryPMFImpl_run, probCompLift_support] at hm
  exact unloggedMappedAdversaryImpl_cache_le key input cache (record.output, record.cache) hm

theorem originalProposalRecord_sign_observed_index (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (record : ProposalExecutionRecord (.inr message))
    (hr : record ∈ (originalProposalRecord key (.inr message) cache).support) (view : FewTimeView)
    (hview : observedSigningView? (messageAnswers key.parameter record.cache) key.root
      ⟨message, record.output⟩ = some view) : record.index = view.1 := by
  rw [originalProposalRecord, PMF.mem_support_map_iff] at hr
  obtain ⟨source, hsource, rfl⟩ := hr
  have ht := (PMF.mem_support_map_iff Prod.fst _ _).mpr ⟨source, hsource, rfl⟩
  rw [completedSigningRecord_forget, probCompLift_support] at ht
  have hs : (source.1.1.1, source.1.2) ∈ support
      ((simulateQ romImpl (signWithView key message)).run cache) := by
    rw [← tracedSigningRun_forget (signingBoundaryTrace key.parameter), support_map]
    exact ⟨source.1, ht, rfl⟩
  cases hresponse : source.1.1.1.1 with
  | none => simp [observedSigningView?, hresponse] at hview
  | some signature =>
      have hs' : ((some signature, source.1.1.1.2), source.1.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run cache) := by
        simpa only [← hresponse] using hs
      obtain ⟨output, houtput, _, hselected⟩ :=
        signWithView_successful_cached_output key message cache source.1.2 signature source.1.1.1.2 hs'
      have hv : hashOutputFewTimeView output = view := by
        simpa [observedSigningView?, hresponse, messageAnswers, houtput] using hview
      exact (completedSigningRecord_selected_index (signingBoundaryTrace key.parameter) key message cache
        source.1 source.2 (hashOutputFewTimeView output) hsource hselected).trans (congrArg Prod.fst hv)

theorem originalProposalRecord_slots_le (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input state.1).support)
    (index : Index) :
    (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter record.cache)
      key.root (state.2 ++ signingLogFragment input record.output)) index).card ≤
        (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter state.1)
          key.root state.2) index).card +
        if input matches .inr _ then (if record.index = index then 1 else 0) else 0 := by
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root state.1 record.cache
    state.2 (originalProposalRecord_cache_le key input state.1 record hr) hsigned
  cases input with
  | inl world =>
      change (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter record.cache)
        key.root (state.2 ++ [])) index).card ≤ _ + 0
      rw [List.append_nil, hstable, Nat.add_zero]
  | inr message =>
      change _ ≤ _ + if record.index = index then 1 else 0
      unfold observedOptionalSigningViews
      change (signingSlotsAtIndex (fun slot => observedSigningView? (messageAnswers key.parameter record.cache)
        key.root ((state.2 ++ [(⟨message, record.output⟩ : SigningEntry)]).get slot)) index).card ≤ _
      rw [signingSlotsAtIndex_log_append_card]
      have heq := congrArg (fun views => (signingSlotsAtIndex views index).card) hstable
      apply Nat.add_le_add heq.le
      split_ifs with hobserved hindex hindex
      · exact le_rfl
      · obtain ⟨view, hview, hsource⟩ := hobserved
        exact False.elim (hindex ((originalProposalRecord_sign_observed_index key message state.1 record hr
          view hview).trans hsource))
      · exact Nat.zero_le _
      · exact le_rfl

theorem certificateProposalImpl_world_run (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (state : List Index × CertificateMonitorState) :
    (certificateProposalImpl key budget required stopAfter (.inl input)).run state =
      (originalProposalRecord key (.inl input) state.2.1).map (fun record =>
        (record.output, state.1, originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
          (.inl input) state.2 0 record)) := by
  simp only [certificateProposalImpl, originalProposalImpl, proposalRecordImpl, originalProposalActive,
    StateT.run_mk, Bool.false_eq_true, if_false]

theorem certificateProposalImpl_sign_run (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (message : Message)
    (state : List Index × CertificateMonitorState) :
    (certificateProposalImpl key budget required stopAfter (.inr message)).run state =
      if CertificateMonitorActive key budget (.inr message) state.2 then
        (recordProposalBridge (originalProposalRecord key (.inr message) state.2.1)
          (originalRejectedProposal key (fun state : CertificateMonitorState => state.2.spent) (.inr message) state.2)
          targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le).map
            (fun result => (result.2.output, state.1 ++ result.1 ++ [result.2.index],
              originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
                (.inr message) state.2 (result.1.length + 1) result.2))
      else (originalProposalRecord key (.inr message) state.2.1).map (fun record =>
        (record.output, state.1, originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
          (.inr message) state.2 0 record)) := by
  simp only [certificateProposalImpl, originalProposalImpl, proposalRecordImpl, StateT.run_mk,
    certificateMonitor_sign_proposals_active, decide_eq_true_eq]

structure CertificateProposalBounds (key : SecretKey) (total : Nat)
    (state : List Index × CertificateMonitorState) : Prop where
  log_le : state.2.2.log.length ≤ signatureLimit
  proposals_eq : state.2.2.proposals = state.1.length
  counts_le : ∀ index : Index,
    (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter state.2.1)
      key.root state.2.2.log) index).card ≤ state.1.count index
  prefix_le : (state.1.length : ENNReal) ≤ targetProposalOverhead * state.2.2.log.length + 131072
  total_le : 25313293 ≤ total

def CertificateProposalInvariant (key : SecretKey) (total : Nat)
    (state : List Index × CertificateMonitorState) : Prop :=
  state.2.2.stopped = false → CertificateProposalBounds key total state

theorem certificateProposalInvariant_initial (key : SecretKey) (total spent : Nat)
    (cache : QueryCache HashSpec) (stopped : Bool) (hpool : stopped = false → 25313293 ≤ total) :
    CertificateProposalInvariant key total ([], cache, initialCertificateMonitor spent stopped) := by
  intro hstopped
  refine ⟨Nat.zero_le _, rfl, ?_, ?_, hpool hstopped⟩
  · intro index
    simp [initialCertificateMonitor, observedOptionalSigningViews, signingSlotsAtIndex]
  · simp only [initialCertificateMonitor, List.length_nil, Nat.cast_zero, mul_zero, zero_add]
    exact bot_le

theorem certificateProposalInvariant_advance (key : SecretKey) (budget total : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateMonitorState)
    (suffix : List Index) (length : Nat) (record : ProposalExecutionRecord input)
    (hinv : CertificateProposalInvariant key total state)
    (hactive : CertificateMonitorActive key budget input state.2)
    (hlength : length = suffix.length)
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter record.cache)
        key.root (state.2.2.log ++ signingLogFragment input record.output)) index).card ≤
          (state.1 ++ suffix).count index) :
    CertificateProposalInvariant key total (state.1 ++ suffix, originalProposalAdvance
      (certificateMonitorUpdate key budget required
        (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record))
      input state.2 length record) := by
  intro hpost
  have hbefore := hinv hactive.1
  have hstop : proposalPrefixStop input state.2 length record = false := by
    simp only [originalProposalAdvance, certificateMonitorUpdate, if_pos hactive,
      Bool.or_eq_false_iff] at hpost
    exact hpost.1.1
  have hprefix : ((state.2.2.proposals + length : Nat) : ENNReal) ≤
      targetProposalOverhead * (state.2.2.log ++ signingLogFragment input record.output).length + 131072 := by
    simp only [proposalPrefixStop, decide_eq_false_iff_not] at hstop
    exact le_of_not_gt hstop
  have hlog : (state.2.2.log ++ signingLogFragment input record.output).length ≤ signatureLimit := by
    have hvalid := hactive.2.2.1
    cases input with
    | inl world => simpa only [ValidSigningStep, signingLogFragment, List.append_nil] using hvalid
    | inr message =>
        simpa only [signingLogFragment, List.length_append, List.length_singleton] using
          Nat.succ_le_of_lt hvalid
  constructor
  · simpa only [originalProposalAdvance, certificateMonitorUpdate, if_pos hactive, proposalRecordLogState] using hlog
  · simp only [originalProposalAdvance, certificateMonitorUpdate, if_pos hactive, List.length_append,
      hbefore.proposals_eq, hlength]
  · intro index
    change (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter record.cache)
      key.root (certificateMonitorUpdate key budget required
        (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record)
        input state.2 length record).log) index).card ≤ _
    rw [show (certificateMonitorUpdate key budget required
        (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record)
        input state.2 length record).log = state.2.2.log ++ signingLogFragment input record.output by
      simp only [certificateMonitorUpdate, if_pos hactive, proposalRecordLogState]]
    exact hcounts index
  · simpa only [originalProposalAdvance, certificateMonitorUpdate, if_pos hactive, proposalRecordLogState,
      List.length_append, hbefore.proposals_eq, hlength] using hprefix
  · exact hbefore.total_le

theorem certificateProposalImpl_invariant (key : SecretKey) (budget total : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateMonitorState)
    (hinv : CertificateProposalInvariant key total state)
    (result : (OracleWorld + SigningSpec).Range input × (List Index × CertificateMonitorState))
    (hr : result ∈ ((certificateProposalImpl key budget required
      (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record)
      input).run state).support) : CertificateProposalInvariant key total result.2 := by
  cases input with
  | inl world =>
      rw [certificateProposalImpl_world_run, PMF.mem_support_map_iff] at hr
      obtain ⟨record, hrecord, rfl⟩ := hr
      by_cases hactive : CertificateMonitorActive key budget (.inl world) state.2
      · have hbefore := hinv hactive.1
        have hcounts (index : Index) := originalProposalRecord_slots_le key (.inl world)
          (certificateMonitorCoverState state.2) hactive.2.1.1 record hrecord index
        have hafter : CertificateProposalInvariant key total (state.1 ++ [], originalProposalAdvance
            (certificateMonitorUpdate key budget required
              (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record))
            (.inl world) state.2 0 record) :=
          certificateProposalInvariant_advance key budget total required stopAfter (.inl world) state [] 0 record
            hinv hactive rfl (fun index => by
              have hc := hcounts index
              change _ ≤ _ + 0 at hc
              rw [Nat.add_zero] at hc
              simpa only [certificateMonitorCoverState, List.append_nil] using hc.trans (hbefore.counts_le index))
        simpa only [List.append_nil] using hafter
      · intro hpost
        simp only [originalProposalAdvance, certificateMonitorUpdate, if_neg hactive, Bool.true_eq_false] at hpost
  | inr message =>
      rw [certificateProposalImpl_sign_run] at hr
      by_cases hactive : CertificateMonitorActive key budget (.inr message) state.2
      · rw [if_pos hactive, PMF.mem_support_map_iff] at hr
        obtain ⟨source, hsource, rfl⟩ := hr
        have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source, hsource, rfl⟩
        rw [recordProposalBridge_record] at hrecord
        have hbefore := hinv hactive.1
        have hafter := certificateProposalInvariant_advance key budget total required stopAfter (.inr message)
          state (source.1 ++ [source.2.index]) (source.1.length + 1) source.2 hinv hactive
          (by simp only [List.length_append, List.length_singleton]) (fun index => by
            have hc := originalProposalRecord_slots_le key (.inr message) (certificateMonitorCoverState state.2)
              hactive.2.1.1 source.2 hrecord index
            change _ ≤ _ + if source.2.index = index then 1 else 0 at hc
            calc
              _ ≤ _ := hc
              _ ≤ state.1.count index + if source.2.index = index then 1 else 0 :=
                Nat.add_le_add_right (hbefore.counts_le index) _
              _ ≤ (state.1 ++ (source.1 ++ [source.2.index])).count index := by
                simp only [List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
                split_ifs <;> omega)
        simpa only [List.append_assoc] using hafter
      · rw [if_neg hactive, PMF.mem_support_map_iff] at hr
        obtain ⟨record, _, rfl⟩ := hr
        intro hpost
        simp only [originalProposalAdvance, certificateMonitorUpdate, if_neg hactive, Bool.true_eq_false] at hpost

theorem certificateMonitorCharge_le_terminalPrice_of_invariant (key : SecretKey) (budget total : Nat)
    (required : Finset FtsTree) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × CertificateMonitorState) (hbudget : budget ≤ 2 ^ 127)
    (hinv : CertificateProposalInvariant key total state) :
    certificateMonitorCharge key budget required input state.2 ≤
      certificateMonitorMass key budget input state.2 *
        terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1 := by
  by_cases hactive : CertificateMonitorActive key budget input state.2
  · have h := hinv hactive.1
    exact certificateMonitorCharge_le_terminalPrice key budget total required input state.2 state.1 hbudget
      h.log_le h.counts_le h.total_le h.prefix_le
  · simp only [certificateMonitorCharge, certificateMonitorMass, if_neg hactive, zero_mul, le_refl]

end SphincsSecurity.Concrete
