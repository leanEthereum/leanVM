import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateCacheMonitor
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem certificateCacheMonitorUpdate_hit (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) (hhit : state.2.2 = true) :
    (certificateCacheMonitorUpdate key budget required stopAfter input state length record).2 = true := by
  simp only [certificateCacheMonitorUpdate, hhit, Bool.true_or]

theorem certificateCacheMonitorUpdate_bad_after (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hbad : CertificateCacheExceptional key record.cache) :
    (certificateCacheMonitorUpdate key budget required stopAfter input state length record).2 = true := by
  simp only [certificateCacheMonitorUpdate, hbad, decide_true, Bool.or_true]

theorem certificateCacheLengthImpl_support (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (result : (OracleWorld + SigningSpec).Range input × CertificateCacheMonitorState)
    (hr : result ∈ ((certificateCacheLengthImpl key budget required stopAfter input).run state).support) :
    ∃ length record, record ∈ (originalProposalRecord key input state.1).support ∧
      result = (record.output, originalProposalAdvance
        (certificateCacheMonitorUpdate key budget required stopAfter) input state length record) := by
  simp only [certificateCacheLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk] at hr
  split at hr
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨source, hsource, rfl⟩ := hr
    have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source, hsource, rfl⟩
    rw [recordLengthBridge_record] at hrecord
    exact ⟨source.1, source.2, hrecord, rfl⟩
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨record, hrecord, rfl⟩ := hr
    exact ⟨0, record, hrecord, rfl⟩

theorem certificateCacheLength_run_hit {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateCacheMonitorState)
    (hhit : state.2.2 = true) (result : α × CertificateCacheMonitorState)
    (hr : result ∈ ((simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.2 = true := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact hhit
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, _, rfl⟩ :=
        certificateCacheLengthImpl_support key budget required stopAfter input state middle hmiddle
      exact ih record.output _ (certificateCacheMonitorUpdate_hit key budget required stopAfter input state length record hhit) result hr

theorem proposalCacheBound_of_no_cache_exception (key : SecretKey) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (spent : Nat) (hspent : spent ≤ 2 ^ 127)
    (hcache : QueryCache.enncard cache ≤ spent) (hclean : ¬ CertificateCacheExceptional key cache) :
    ProposalCacheBound key cache spent :=
  ⟨hspent, hcache, fun h => hclean (Or.inl h),
    cachedIndex_bound_of_no_excess key.parameter cache hfinite spent hcache (fun h => hclean (Or.inr h))⟩

end SphincsSecurity.Concrete
