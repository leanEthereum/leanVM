import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateCachePersistence
import SphincsSecurity.Proof.Fts.OriginalProposalBudget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem boundaryRun_enncard_le {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : (α × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun parameter computation cache)) :
    QueryCache.enncard result.2 ≤ QueryCache.enncard cache + result.1.2.hashCalls := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [boundaryRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hr
      subst result
      simp only [SigningBoundaryTrace.hashCalls, FreeMonoid.toList_one, List.length_nil,
        Nat.cast_zero, add_zero, le_refl]
  | query_bind input next ih =>
      rw [boundaryRun_bind, boundaryRun_query, mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      rw [support_map] at hmiddle
      obtain ⟨source, hsource, rfl⟩ := hmiddle
      rw [support_map] at hr
      obtain ⟨last, hlast, rfl⟩ := hr
      have htail := ih source.1 source.2 last hlast
      rw [SigningBoundaryTrace.hashCalls_mul, signingBoundaryTrace_hashCalls_eq, Nat.cast_add]
      cases input with
      | inl sample =>
          simpa only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_add,
            romImpl_uniform_query_enncard_eq sample cache source hsource] using htail
      | inr input =>
          calc
            _ ≤ QueryCache.enncard source.2 + last.1.2.hashCalls := htail
            _ ≤ (QueryCache.enncard cache + 1) + last.1.2.hashCalls :=
              add_le_add (romImpl_hash_query_enncard_le input cache source hsource) le_rfl
            _ = _ := by simp only [↓reduceIte, Nat.cast_one, add_assoc]

theorem originalProposalRecord_enncard_le (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    QueryCache.enncard record.cache ≤ QueryCache.enncard cache + record.trace.hashCalls :=
  boundaryRun_enncard_le key.parameter (expandedAdversaryImpl key input) cache _
    (originalProposalRecord_boundary_support key input cache record hr)

theorem originalProposalRecord_signingDigestsCached (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input state.1).support) :
    SigningDigestsCached key.parameter record.cache key.root
      (state.2 ++ signingLogFragment input record.output) := by
  have hm := (PMF.mem_support_map_iff (fun record : ProposalExecutionRecord input =>
    (record.output, record.cache)) _ _).mpr ⟨record, hr, rfl⟩
  rw [originalProposalRecord_project, originalAdversaryPMFImpl_run, probCompLift_support] at hm
  apply logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned
    (record.output, record.cache, state.2 ++ signingLogFragment input record.output)
  rw [logTracedMappedAdversaryImpl_run_map, support_map]
  exact ⟨(record.output, record.cache), hm, rfl⟩

theorem signingMacroHashCost_le_record (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    signingMacroHashCost input ≤ record.trace.hashCalls := by
  cases input with
  | inl world =>
      rw [originalProposalRecord_world_hashCalls key world cache record hr]
      cases world <;> exact le_rfl
  | inr message =>
      exact (by decide : 1024 ≤ 28504).trans (originalProposalRecord_sign_hashCalls key message cache record hr)

theorem certificateMonitorUpdate_ready (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input state.1).support)
    (hactive : CertificateMonitorActive key budget input state) (hbudget : budget ≤ 2 ^ 127)
    (hcost : state.2.spent + record.trace.hashCalls ≤ budget)
    (hclean : ¬ CertificateCacheExceptional key record.cache) :
    CertificateMonitorReady key budget
      (record.cache, certificateMonitorUpdate key budget required stopAfter input state length record) := by
  have hcache := (originalProposalRecord_enncard_le key input state.1 record hr).trans
    (add_le_add hactive.2.1.2.1.cache_le le_rfl)
  have hcache' : QueryCache.enncard record.cache ≤ (state.2.spent + record.trace.hashCalls : Nat) := by
    simpa only [Nat.cast_add] using hcache
  have hsigned := originalProposalRecord_signingDigestsCached key input (state.1, state.2.log)
    hactive.2.1.1 record hr
  have hcap := proposalCacheBound_of_no_cache_exception key record.cache (Finite.of_enncard_le hcache')
    (state.2.spent + record.trace.hashCalls) (hcost.trans hbudget) hcache' hclean
  simpa only [CertificateMonitorReady, certificateMonitorUpdate, if_pos hactive, proposalRecordLogState] using
    And.intro hsigned (And.intro hcap hcost)

theorem certificateMonitorUpdate_stopped_eq (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).stopped =
      (stopAfter input state length record || decide (¬ CertificateMonitorReady key budget
        (record.cache, certificateMonitorUpdate key budget required stopAfter input state length record))) := by
  simp only [certificateMonitorUpdate, if_pos hactive, CertificateMonitorReady]
  apply congrArg (fun flag => stopAfter input state length record || flag)
  exact decide_eq_decide.mpr Iff.rfl

end SphincsSecurity.Concrete
