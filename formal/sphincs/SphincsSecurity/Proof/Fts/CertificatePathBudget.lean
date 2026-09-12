import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateMonitor
import SphincsSecurity.Proof.Fts.OriginalProposalBudget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem certificateLengthImpl_support (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (result : (OracleWorld + SigningSpec).Range input × CertificateMonitorState)
    (hr : result ∈ ((certificateLengthImpl key budget required stopAfter input).run state).support) :
    ∃ length record, record ∈ (originalProposalRecord key input state.1).support ∧
      result = (record.output, originalProposalAdvance
        (certificateMonitorUpdate key budget required stopAfter) input state length record) := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk] at hr
  split at hr
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨source, hsource, rfl⟩ := hr
    have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source, hsource, rfl⟩
    rw [recordLengthBridge_record] at hrecord
    exact ⟨source.1, source.2, hrecord, rfl⟩
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨record, hrecord, rfl⟩ := hr
    exact ⟨0, record, hrecord, rfl⟩

theorem certificateMonitorUpdate_le_hashCalls (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input state.1).support) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).spent ≤
        state.2.spent + record.trace.hashCalls ∧
      (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass ≤
        state.2.creationMass + record.trace.hashCalls := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · simp only [certificateMonitorUpdate, if_pos hactive]
    exact ⟨le_rfl, add_le_add le_rfl (targetCreationMultiplier_le_record_hashCalls key input state.1 record hr)⟩
  · simp only [certificateMonitorUpdate, if_neg hactive]
    exact ⟨Nat.le_add_right _ _, le_self_add⟩

theorem certificateLength_run_cost_le {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches .inr _) q)
    (state : CertificateMonitorState) (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.spent ≤ state.2.spent + q ∧ result.2.2.creationMass ≤ state.2.creationMass + q := by
  induction computation using OracleComp.inductionOn generalizing q state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨Nat.le_add_right _ _, le_self_add⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateLengthImpl_support key budget required stopAfter input state middle hmiddle
      have hquery := originalProposalRecord_query_bound key input next q hbound state.1 record hrecord
      have hstep := certificateMonitorUpdate_le_hashCalls key budget required stopAfter input state length record hrecord
      have htail := ih record.output _ hquery.2 _ result hr
      simp only [originalProposalAdvance] at htail
      constructor
      · omega
      · calc
          _ ≤ (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass +
              (q - record.trace.hashCalls : Nat) := htail.2
          _ ≤ (state.2.creationMass + record.trace.hashCalls) + (q - record.trace.hashCalls : Nat) :=
            add_le_add hstep.2 le_rfl
          _ = state.2.creationMass + q := by
            rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hquery.1]

theorem certificateProposal_run_cost_le {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches .inr _) q)
    (state : List Index × CertificateMonitorState) (result : α × (List Index × CertificateMonitorState))
    (hr : result ∈ ((simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.2.spent ≤ state.2.2.spent + q ∧
      result.2.2.2.creationMass ≤ state.2.2.creationMass + q := by
  have hprojection := simulateQ_certificateProposalImpl_length key budget required stopAfter computation state
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, hprojection] at hm
  exact certificateLength_run_cost_le key budget required stopAfter computation q hbound state.2 _ hm

end SphincsSecurity.Concrete
