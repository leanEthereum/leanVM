import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateBoundaryInvariants
import SphincsSecurity.Proof.Fts.StoppedSigningLog
import SphincsSecurity.Proof.Fts.CertificateProposalPrefixException
import SphincsSecurity.Proof.Fts.CertificateStoppedState

/-! ## CertificateProposalPrefixPersistence -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

theorem certificateLength_run_prefixOverflow {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState)
    (hstop : state.2.stopped = true)
    (hbad : ProposalPrefixExceptional state.2.proposals state.2.log.length)
    (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.stopped = true ∧ ProposalPrefixExceptional result.2.2.proposals result.2.2.log.length := by
  rw [certificateLength_run_stopped key budget required stopAfter computation state hstop result hr]
  exact ⟨hstop, hbad⟩

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (withSigningLog withSigningLog_pure withSigningLog_query_bind)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem withSigningLog_run_length_le {σ α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ PMF))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec)
    (state : σ) (result : (α × QueryLog SigningSpec) × σ)
    (hr : result ∈ ((simulateQ impl (withSigningLog computation log)).run state).support) :
    log.length ≤ result.1.2.length := by
  induction computation using OracleComp.inductionOn generalizing log state result with
  | pure value =>
      simp only [withSigningLog_pure, simulateQ_pure, StateT.run_pure,
        PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [withSigningLog_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, _, hr⟩ := hr
      have htail := ih middle.1 (log ++ signingLogFragment input middle.1) middle.2 result hr
      rw [List.length_append] at htail
      omega

theorem certificateCacheLength_run_prefixOverflow {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateCacheMonitorState)
    (hstop : state.2.1.stopped = true)
    (hbad : ProposalPrefixExceptional state.2.1.proposals state.2.1.log.length)
    (result : α × CertificateCacheMonitorState)
    (hr : result ∈ ((simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run state).support) :
    ProposalPrefixExceptional result.2.2.1.proposals result.2.2.1.log.length := by
  have hm := (PMF.mem_support_map_iff (Prod.map id certificateCacheMonitorProject) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, simulateQ_certificateCacheLengthImpl_project] at hm
  exact (certificateLength_run_prefixOverflow key budget required stopAfter computation
    (certificateCacheMonitorProject state) hstop hbad _ hm).2

theorem certificateCacheLength_withSigningLog_clean {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches .inr _) q)
    (state : CertificateCacheMonitorState)
    (hready : CertificateMonitorReady key budget (certificateCacheMonitorProject state))
    (halive : state.2.1.stopped = false) (hroom : state.2.1.spent + q ≤ budget)
    (result : (α × QueryLog SigningSpec) × CertificateCacheMonitorState)
    (hr : result ∈ ((simulateQ (certificateCacheLengthImpl key budget required proposalPrefixStop)
      (withSigningLog computation state.2.1.log)).run state).support)
    (hvalid : SigningTranscript.Valid result.1.2) (hhit : result.2.2.2 = false)
    (hprefix : ¬ ProposalPrefixExceptional result.2.2.1.proposals result.2.2.1.log.length) :
    result.2.2.1.stopped = false ∧ result.2.2.1.log = result.1.2 ∧
      CertificateMonitorReady key budget (certificateCacheMonitorProject result.2) := by
  induction computation using OracleComp.inductionOn generalizing q state result with
  | pure value =>
      simp only [withSigningLog_pure, simulateQ_pure, StateT.run_pure,
        PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨halive, rfl, hready⟩
  | query_bind input next ih =>
      rw [withSigningLog_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateCacheLengthImpl_support key budget required proposalPrefixStop input state middle hmiddle
      let after := originalProposalAdvance (certificateCacheMonitorUpdate key budget required proposalPrefixStop)
        input state length record
      have hquery := originalProposalRecord_query_bound key input next q hbound state.1 record hrecord
      have hlogLength := withSigningLog_run_length_le
        (certificateCacheLengthImpl key budget required proposalPrefixStop) (next record.output)
        (state.2.1.log ++ signingLogFragment input record.output) after result hr
      have hstepValid : ValidSigningStep state.2.1.log input := by
        change result.1.2.length ≤ signatureLimit at hvalid
        cases input <;> simp only [ValidSigningStep, signingLogFragment, List.length_append,
          List.length_nil, List.length_singleton] at hlogLength ⊢ <;> omega
      have hmin := signingMacroHashCost_le_record key input state.1 record hrecord
      have hactive : CertificateMonitorActive key budget input (certificateCacheMonitorProject state) :=
        ⟨halive, hready, hstepValid, by change signingMacroHashCost input ≤ budget - state.2.1.spent; omega⟩
      have hafterHit : after.2.2 = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        have hfinal := certificateCacheLength_run_hit key budget required proposalPrefixStop
          (withSigningLog (next record.output) (state.2.1.log ++ signingLogFragment input record.output))
          after htrue result hr
        rw [hhit] at hfinal
        contradiction
      have hafterClean : ¬ CertificateCacheExceptional key record.cache := by
        intro hbad
        have htrue := certificateCacheMonitorUpdate_bad_after key budget required proposalPrefixStop
          input state length record hbad
        change after.2.2 = true at htrue
        rw [hafterHit] at htrue
        contradiction
      have hcost : state.2.1.spent + record.trace.hashCalls ≤ budget := by omega
      have hafterReady : CertificateMonitorReady key budget (certificateCacheMonitorProject after) :=
        certificateMonitorUpdate_ready key budget required proposalPrefixStop input
          (certificateCacheMonitorProject state) length record hrecord hactive hbudget hcost hafterClean
      have hstop : proposalPrefixStop input (certificateCacheMonitorProject state) length record = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        have hstopped : after.2.1.stopped = true := by
          simp only [after, originalProposalAdvance, certificateCacheMonitorUpdate,
            certificateMonitorUpdate, if_pos hactive, htrue, Bool.true_or]
        have hoverflow := htrue
        rw [proposalPrefixStop_eq_after_exception key budget required proposalPrefixStop input
          (certificateCacheMonitorProject state) length record hactive, decide_eq_true_eq] at hoverflow
        exact hprefix (certificateCacheLength_run_prefixOverflow key budget required proposalPrefixStop
          (withSigningLog (next record.output) (state.2.1.log ++ signingLogFragment input record.output))
          after hstopped hoverflow result hr)
      have hafterAlive : after.2.1.stopped = false := by
        change (certificateMonitorUpdate key budget required proposalPrefixStop input
          (certificateCacheMonitorProject state) length record).stopped = false
        rw [certificateMonitorUpdate_stopped_eq key budget required proposalPrefixStop input
          (certificateCacheMonitorProject state) length record hactive]
        change (proposalPrefixStop input (certificateCacheMonitorProject state) length record ||
          decide (¬ CertificateMonitorReady key budget (certificateCacheMonitorProject after))) = false
        simp only [hstop, hafterReady, not_true_eq_false, decide_false, Bool.false_or]
      have hafterLog : after.2.1.log = state.2.1.log ++ signingLogFragment input record.output := by
        change (certificateMonitorUpdate key budget required proposalPrefixStop input
          (certificateCacheMonitorProject state) length record).log = _
        simp only [certificateMonitorUpdate, if_pos hactive, proposalRecordLogState]
        rfl
      have hafterRoom : after.2.1.spent + (q - record.trace.hashCalls) ≤ budget := by
        change (certificateMonitorUpdate key budget required proposalPrefixStop input
          (certificateCacheMonitorProject state) length record).spent + (q - record.trace.hashCalls) ≤ budget
        rw [certificateMonitorUpdate_spent key budget required proposalPrefixStop input
          (certificateCacheMonitorProject state) length record hactive]
        change state.2.1.spent + record.trace.hashCalls + (q - record.trace.hashCalls) ≤ budget
        omega
      apply ih record.output (q - record.trace.hashCalls) hquery.2 after hafterReady hafterAlive hafterRoom result
      · simpa only [hafterLog] using hr
      · exact hvalid
      · exact hhit
      · exact hprefix

end SphincsSecurity.Concrete
