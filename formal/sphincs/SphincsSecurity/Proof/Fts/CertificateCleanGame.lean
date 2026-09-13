import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateCleanExecution
import SphincsSecurity.Proof.Fts.CertificateJointExceptions
import SphincsSecurity.Proof.Residual.RetainedWorldCoverBudget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation withSigningLog
  signingTraceComputation signingTraceComputation_fst unloggedRetainedRestComputation
  retainedGameRestComputation_eq_signingTrace arrangeRetainedTrace)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem initialCertificateMonitor_ready (key : SecretKey) (budget spent : Nat)
    (cache : QueryCache HashSpec) (stopped : Bool)
    (hbudget : budget ≤ 2 ^ 127) (hspent : spent ≤ budget)
    (hcache : QueryCache.enncard cache ≤ spent)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    CertificateMonitorReady key budget (cache, initialCertificateMonitor spent stopped) := by
  have hfinite := Finite.of_enncard_le hcache
  have hclean : ¬ CertificateCacheExceptional key cache := by
    intro hbad
    have hzero := certificateCacheExceptionPotential_initial_le key 0 (by omega) cache hnone
    have hone := certificateCacheExceptionPotential_bad key 0 cache hfinite hbad
    simp only [Nat.cast_zero, ENNReal.zero_div, add_zero] at hzero
    exact (not_le_of_gt (by norm_num : (0 : ENNReal) < 1)) (hone.trans hzero)
  refine ⟨?_, proposalCacheBound_of_no_cache_exception key cache hfinite spent
    (hspent.trans hbudget) hcache hclean, hspent⟩
  intro entry hentry
  simp only [initialCertificateMonitor, List.not_mem_nil] at hentry

theorem certificateCacheProposal_withSigningLog_clean {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : List Index × CertificateCacheMonitorState)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) computation) state.2.1 q)
    (hready : CertificateMonitorReady key budget (certificateCacheMonitorProject state.2))
    (halive : state.2.2.1.stopped = false) (hroom : state.2.2.1.spent + q ≤ budget)
    (result : (α × QueryLog SigningSpec) × (List Index × CertificateCacheMonitorState))
    (hr : result ∈ ((simulateQ (certificateCacheProposalImpl key budget required proposalPrefixStop)
      (withSigningLog computation state.2.2.1.log)).run state).support)
    (hvalid : SigningTranscript.Valid result.1.2) (hhit : result.2.2.2.2 = false)
    (hprefix : ¬ ProposalPrefixExceptional result.2.2.2.1.proposals result.2.2.2.1.log.length) :
    result.2.2.2.1.stopped = false ∧ result.2.2.2.1.log = result.1.2 ∧
      CertificateMonitorReady key budget (certificateCacheMonitorProject result.2.2) := by
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, simulateQ_certificateCacheProposalImpl_length] at hm
  exact certificateCacheLength_withSigningLog_clean key budget required hbudget computation q
    state.2 hbound hready halive hroom _ hm hvalid hhit hprefix

theorem certificateCacheProposal_rest_clean (adversary : Adversary) (publicKey : PublicKey)
    (key : SecretKey) (budget q : Nat) (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 127)
    (state : List Index × CertificateCacheMonitorState)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key)
      (retainedGameRestComputation adversary publicKey)) state.2.1 q)
    (hready : CertificateMonitorReady key budget (certificateCacheMonitorProject state.2))
    (halive : state.2.2.1.stopped = false) (hlog : state.2.2.1.log = [])
    (hroom : state.2.2.1.spent + q ≤ budget) (result : CertificateCacheGameResult)
    (hr : result ∈ ((simulateQ (certificateCacheProposalImpl key budget required proposalPrefixStop)
      (retainedGameRestComputation adversary publicKey)).run state).support)
    (hvalid : SigningTranscript.Valid result.1.1.2) (hclean : ¬ CertificateGameExceptional result) :
    result.2.2.2.1.stopped = false ∧ result.2.2.2.1.log = result.1.1.2 ∧
      CertificateMonitorReady key budget (certificateCacheMonitorProject result.2.2) := by
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, hashQueryBound_map_iff] at hbound
  have hforget : Prod.fst <$> simulateQ (expandedAdversaryImpl key)
      (signingTraceComputation (unloggedRetainedRestComputation adversary publicKey)) =
        simulateQ (expandedAdversaryImpl key) (unloggedRetainedRestComputation adversary publicKey) := by
    rw [← simulateQ_map, signingTraceComputation_fst]
  have hunlogged := (hashQueryBound_iff_of_map_eq hforget _ _).mp hbound
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hr
  obtain ⟨source, hsource, rfl⟩ := hr
  have htrace : withSigningLog (unloggedRetainedRestComputation adversary publicKey) state.2.2.1.log =
      signingTraceComputation (unloggedRetainedRestComputation adversary publicKey) := by
    simp only [withSigningLog, hlog, List.nil_append, Prod.mk.eta]
    exact id_map _
  have hresult := certificateCacheProposal_withSigningLog_clean key budget required hbudget
    (unloggedRetainedRestComputation adversary publicKey) q state hunlogged hready halive hroom source
    (by rwa [htrace]) hvalid (Bool.eq_false_iff.mpr (fun h => hclean (Or.inl h)))
    (fun h => hclean (Or.inr h))
  exact hresult

end SphincsSecurity.Concrete
