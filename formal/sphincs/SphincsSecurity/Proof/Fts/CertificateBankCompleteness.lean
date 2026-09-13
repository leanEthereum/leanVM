import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateCleanGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false

def CertificateBankComplete (key : SecretKey) (required : Finset FtsTree)
    (state : CertificateMonitorState) : Prop :=
  ∀ input, TargetCertificateAt key required (certificateMonitorCoverState state) input →
    state.2.bank input = true

theorem certificateMonitorUpdate_bank_complete (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (halive : (certificateMonitorUpdate key budget required stopAfter input state length record).stopped = false) :
    CertificateBankComplete key required
      (record.cache, certificateMonitorUpdate key budget required stopAfter input state length record) := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · intro query hcertificate
    simp only [certificateMonitorCoverState, certificateMonitorUpdate, if_pos hactive,
      proposalRecordLogState] at hcertificate ⊢
    exact completedTargetBank_of_certificate key required _ state.2.bank query hcertificate
  · rw [certificateMonitorUpdate_inactive key budget required stopAfter input state length record hactive] at halive
    contradiction

theorem certificateLength_run_bank_complete {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState)
    (hbank : state.2.stopped = false → CertificateBankComplete key required state)
    (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support)
    (halive : result.2.2.stopped = false) : CertificateBankComplete key required result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact hbank halive
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, _, rfl⟩ :=
        certificateLengthImpl_support key budget required stopAfter input state middle hmiddle
      exact ih record.output _ (fun h =>
        certificateMonitorUpdate_bank_complete key budget required stopAfter input state length record h) result hr halive

theorem certificateCacheProposal_run_bank_complete {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateCacheMonitorState)
    (hbank : state.2.2.1.stopped = false →
      CertificateBankComplete key required (certificateCacheMonitorProject state.2))
    (result : α × (List Index × CertificateCacheMonitorState))
    (hr : result ∈ ((simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state).support)
    (halive : result.2.2.2.1.stopped = false) :
    CertificateBankComplete key required (certificateCacheMonitorProject result.2.2) := by
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, simulateQ_certificateCacheProposalImpl_length] at hm
  have hm' := (PMF.mem_support_map_iff (Prod.map id certificateCacheMonitorProject) _ _).mpr
    ⟨(result.1, result.2.2), hm, rfl⟩
  rw [← PMF.monad_map_eq_map, simulateQ_certificateCacheLengthImpl_project] at hm'
  exact certificateLength_run_bank_complete key budget required stopAfter computation
    (certificateCacheMonitorProject state.2) hbank _ hm' halive

theorem initialCertificateMonitor_bank_complete (key : SecretKey) (spent : Nat)
    (required : Finset FtsTree) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    CertificateBankComplete key required (cache, initialCertificateMonitor spent stopped) := by
  rintro input ⟨output, houtput, hmessage, _⟩
  change cache input = some output at houtput
  rw [hnone input hmessage] at houtput
  contradiction

theorem certificateCacheProposal_rest_clean_certificate (adversary : Adversary) (publicKey : PublicKey)
    (key : SecretKey) (budget q spent : Nat) (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 127)
    (cache : QueryCache HashSpec)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key)
      (retainedGameRestComputation adversary publicKey)) cache q) (hroom : spent + q ≤ budget)
    (hcache : QueryCache.enncard cache ≤ spent)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (result : CertificateCacheGameResult)
    (hr : result ∈ ((simulateQ (certificateCacheProposalImpl key budget required proposalPrefixStop)
      (retainedGameRestComputation adversary publicKey)).run
        ([], cache, initialCertificateMonitor spent false, false)).support)
    (hvalid : SigningTranscript.Valid result.1.1.2) (hclean : ¬ CertificateGameExceptional result)
    (input : HashInput) (hcertificate : TargetCertificateAt key required (result.2.2.1, result.1.1.2) input) :
    1 ≤ certificateBankCount result.2.2.2.1.bank := by
  have hready := initialCertificateMonitor_ready key budget spent cache false hbudget (by omega) hcache hnone
  have hresult := certificateCacheProposal_rest_clean adversary publicKey key budget q required hbudget
    ([], cache, initialCertificateMonitor spent false, false) hbound hready rfl rfl hroom result hr hvalid hclean
  have hbank := certificateCacheProposal_run_bank_complete key budget required proposalPrefixStop
    (retainedGameRestComputation adversary publicKey) ([], cache, initialCertificateMonitor spent false, false)
    (fun _ => initialCertificateMonitor_bank_complete key spent required cache false hnone) result hr hresult.1
  apply one_le_certificateBankCount _ input
  apply hbank input
  change TargetCertificateAt key required (result.2.2.1, result.2.2.2.1.log) input
  rwa [hresult.2.1]

end SphincsSecurity.Concrete
