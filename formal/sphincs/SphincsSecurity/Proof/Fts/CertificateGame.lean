import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateMessagePayment
import SphincsSecurity.Proof.Fts.CertificatePathBudget
import SphincsSecurity.Proof.Ots.OtsProbeCanonicalChargeGame

/-! ## OtsProbeStartErasureBound -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

theorem simulateQ_unloggedMapped_eq_expanded (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (unloggedMappedAdversaryImpl secretKey) computation =
      simulateQ romImpl (simulateQ (expandedAdversaryImpl secretKey) computation) := by
  have hhandler : unloggedMappedAdversaryImpl secretKey = romImpl ∘ₛ expandedAdversaryImpl secretKey := by
    funext input
    exact unloggedMappedAdversaryImpl_eq_simulateQ_expanded secretKey input
  rw [hhandler, QueryImpl.simulateQ_compose]

end SphincsSecurity.Concrete.OtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem simulateQ_romImpl_sampling_bind_run {α β : Type} (computation : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld α) >>= next)).run cache =
      computation >>= fun value => (simulateQ romImpl (next value)).run cache := by
  rw [simulateQ_bind, StateT.run_bind,
    show simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ (unifFwdImpl HashSpec) computation from QueryImpl.simulateQ_add_liftM_left _ _ computation,
    unifFwdImpl.simulateQ_run, bind_map_left]

theorem keygen_cache_message_none (generated : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hg : generated ∈ support ((simulateQ romImpl scheme.keygen).run ∅)) :
    ∀ input, FtsProbeSimulation.MessageHashInput generated.1.2.parameter input → generated.2 input = none := by
  change generated ∈ support ((simulateQ romImpl keygen).run ∅) at hg
  rw [keygen, simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨parameter, _, hg⟩ := hg
  rw [simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨otsSecret, _, hg⟩ := hg
  rw [simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨ftsSecret, _, hg⟩ := hg
  rw [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM, mem_support_bind_iff] at hg
  obtain ⟨root, hroot, hg⟩ := hg
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hg
  subst generated
  rintro input ⟨payload, rfl⟩
  exact treeRoot_cache_message_none parameter topLayer rootTree (otsSecret topLayer rootTree)
    root.1 root.2 hroot payload

abbrev CertificateGameResult := RetainedRestResult × (List Index × CertificateMonitorState)

noncomputable def certificateGame (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) : PMF CertificateGameResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  (simulateQ (certificateProposalImpl key budget required (stopAfter key))
    (retainedGameRestComputation adversary generated.1.1.1)).run
      ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped)

theorem certificateGame_cost_le (adversary : Adversary) (q : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (hbound : HasHashQueryBound scheme adversary q) (result : CertificateGameResult)
    (hr : result ∈ (certificateGame adversary q required stopAfter stopped).support) :
    result.2.2.2.spent ≤ q ∧ result.2.2.2.creationMass ≤ q := by
  rw [certificateGame, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hgenerated, hr⟩ := hr
  rw [probCompLift_support] at hgenerated
  have hwhole : HashQueryBound (scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2)
      ∅ q := (hasHashQueryBound_iff scheme adversary q).mp hbound
  have hkeygen := boundaryRun_bind_query_bound 0 scheme.keygen
    (fun keys => gameRest scheme adversary keys.1 keys.2) q ∅ hwhole generated hgenerated
  have hrest := hkeygen.2
  rw [OtsProbeSimulation.gameRest_eq_map_retained, hashQueryBound_map_iff] at hrest
  have hcost := certificateProposal_run_cost_le generated.1.1.2 q required (stopAfter generated.1.1.2)
    (retainedGameRestComputation adversary generated.1.1.1) (q - generated.1.2.hashCalls)
    ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped) hrest result hr
  simp only [initialCertificateMonitor, zero_add] at hcost
  exact ⟨by omega, hcost.2.trans (Nat.cast_le.mpr (Nat.sub_le _ _))⟩

theorem expected_certificateGame_creationMass_le_messageCalls (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.creationMass) ≤
      ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.messageCalls := by
  rw [certificateGame, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro generated
  exact mul_le_mul' le_rfl (expected_certificateProposal_creationMass_le_messageCalls generated.1.1.2 budget
    generated.1.2.hashCalls required (stopAfter generated.1.1.2)
    (retainedGameRestComputation adversary generated.1.1.1) generated.2 stopped)

theorem expected_certificateGame_count_le_creationCost (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] *
        certificateBankCount result.2.2.2.bank) ≤
      ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.creationCost := by
  rw [certificateGame, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro generated
  by_cases hg : generated ∈ (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _).support
  · have hgenerated := hg
    rw [probCompLift_support] at hgenerated
    have hkeygen : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
      rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
      exact ⟨generated, hgenerated, rfl⟩
    have hnone := keygen_cache_message_none (generated.1.1, generated.2) hkeygen
    exact mul_le_mul' le_rfl (expected_certificateProposal_count_le_creationCost generated.1.1.2 budget
      generated.1.2.hashCalls required (stopAfter generated.1.1.2)
      (retainedGameRestComputation adversary generated.1.1.1) generated.2 stopped
      hnone)
  · have hzero : Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] = 0 := by
      rw [PMF.probOutput_eq_apply]
      exact (PMF.apply_eq_zero_iff _ _).mpr hg
    rw [hzero, zero_mul, zero_mul]

end SphincsSecurity.Concrete
