import SphincsSecurity.Proof.Fts.CertificateBankCompleteness
import SphincsSecurity.Proof.Fts.UnitCertificateCoverage
import SphincsSecurity.Proof.Fts.CertificateOriginalMessageCost
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] scheme signAfterDigest certificateCacheProposalImpl retainedGameRestComputation

abbrev CertificateContextResult := SecretKey × CertificateCacheGameResult
abbrev OriginalCertificateResult := SecretKey × RetainedRestResult × QueryCache HashSpec

noncomputable def originalCertificateSource (adversary : Adversary) : ProbComp OriginalCertificateResult := do
  let generated ← (simulateQ romImpl scheme.keygen).run ∅
  let result ← (simulateQ (unloggedMappedAdversaryImpl generated.1.2)
    (retainedGameRestComputation adversary generated.1.1)).run generated.2
  pure (generated.1.2, result)

noncomputable def certificateContextGame (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) : PMF CertificateContextResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  let result ← (simulateQ (certificateCacheProposalImpl key budget required (stopAfter key))
    (retainedGameRestComputation adversary generated.1.1.1)).run
      ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false)
  pure (key, result)

theorem certificateContextGame_project (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Prod.snd <$> certificateContextGame adversary budget required stopAfter stopped =
      certificateCacheGame adversary budget required stopAfter stopped := by
  simp only [certificateContextGame, certificateCacheGame, map_bind, map_pure, bind_pure]

theorem certificateCacheProposal_original {Result : Type} (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : List Index × CertificateCacheMonitorState) :
    (fun result => (result.1, result.2.2.1)) <$>
      (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state =
        (liftM ((simulateQ (unloggedMappedAdversaryImpl key) computation).run state.2.1) : PMF _) := by
  rw [certificateCacheProposalImpl]
  exact simulateQ_originalProposalImpl_original key _ _ _ computation state

def CertificateContextResult.original (result : CertificateContextResult) : OriginalCertificateResult :=
  (result.1, result.2.1, result.2.2.2.1)

theorem certificateContextGame_original (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    CertificateContextResult.original <$> certificateContextGame adversary budget required stopAfter stopped =
      (liftM (originalCertificateSource adversary) : PMF _) := by
  have hrest (generated : ((PublicKey × SecretKey) × SigningBoundaryTrace) × QueryCache HashSpec) :
      (fun result : CertificateCacheGameResult => (generated.1.1.2, result.1, result.2.2.1)) <$>
        (simulateQ (certificateCacheProposalImpl generated.1.1.2 budget required (stopAfter generated.1.1.2))
          (retainedGameRestComputation adversary generated.1.1.1)).run
          ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false) =
      (liftM (do
        let result ← (simulateQ (unloggedMappedAdversaryImpl generated.1.1.2)
          (retainedGameRestComputation adversary generated.1.1.1)).run generated.2
        pure (generated.1.1.2, result)) : PMF _) := by
    have h := congrArg (Functor.map (fun result => (generated.1.1.2, result)))
      (certificateCacheProposal_original generated.1.1.2 budget required (stopAfter generated.1.1.2)
        (retainedGameRestComputation adversary generated.1.1.1)
        ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false))
    simpa only [Functor.map_map, ← liftM_map (m := ProbComp) (n := PMF), bind_pure_comp] using h
  simp only [certificateContextGame, map_bind, bind_pure_comp, Functor.map_map, CertificateContextResult.original]
  simp_rw [hrest]
  rw [← liftM_bind (m := ProbComp) (n := PMF)]
  apply congrArg (fun computation : ProbComp OriginalCertificateResult => (liftM computation : PMF _))
  rw [originalCertificateSource, ← boundaryRun_forget 0 scheme.keygen ∅, bind_map_left]

def OriginalFullCertificate (result : OriginalCertificateResult) : Prop :=
  SigningTranscript.Valid result.2.1.1.2 ∧
    ∃ input, TargetCertificateAt result.1 Finset.univ (result.2.2, result.2.1.1.2) input

theorem certificateContextGame_full_count (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) (result : CertificateContextResult)
    (hr : result ∈ (certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false).support)
    (hfull : OriginalFullCertificate result.original) (hclean : ¬CertificateGameExceptional result.2) :
    1 ≤ certificateBankCount result.2.2.2.2.1.bank := by
  rw [certificateContextGame, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hgenerated, hr⟩ := hr
  rw [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨output, houtput, hr⟩ := hr
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
  subst result
  rw [probCompLift_support] at hgenerated
  have hwhole : HashQueryBound (scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2)
      ∅ q := (hasHashQueryBound_iff scheme adversary q).mp hbound
  have hkeygen := boundaryRun_bind_query_bound 0 scheme.keygen
    (fun keys => gameRest scheme adversary keys.1 keys.2) q ∅ hwhole generated hgenerated
  have hrest := hkeygen.2
  rw [OtsProbeSimulation.gameRest_eq_map_retained, hashQueryBound_map_iff] at hrest
  have hretained : OtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1 =
      retainedGameRestComputation adversary generated.1.1.1 := by
    unfold OtsProbeSimulation.retainedGameRestComputation retainedGameRestComputation
    rfl
  rw [hretained] at hrest
  have hcache := boundaryRun_enncard_le 0 scheme.keygen ∅ generated hgenerated
  simp only [QueryCache.enncard_empty, zero_add] at hcache
  have hg : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
    rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
    exact ⟨generated, hgenerated, rfl⟩
  dsimp only [OriginalFullCertificate, CertificateContextResult.original] at hfull
  obtain ⟨hvalid, input, hcertificate⟩ := hfull
  exact certificateCacheProposal_rest_clean_certificate adversary generated.1.1.1 generated.1.1.2
    q (q - generated.1.2.hashCalls) generated.1.2.hashCalls Finset.univ hbudget generated.2 hrest
    (Nat.add_sub_of_le hkeygen.1).le hcache (keygen_cache_message_none (generated.1.1, generated.2) hg) output houtput hvalid hclean input hcertificate

private theorem probOutput_probCompLift {Result : Type} (computation : ProbComp Result) (result : Result) :
    Pr[= result | (liftM computation : PMF Result)] = Pr[= result | computation] := rfl

private theorem expected_probCompLift_of_map_eq {Source Result : Type}
    (source : ProbComp Source) (result : ProbComp Result) (project : Source → Result)
    (hproject : project <$> source = result) (cost : Result → ENNReal) :
    (∑' value, Pr[= value | (liftM source : PMF Source)] * cost (project value)) =
      ∑' value, Pr[= value | result] * cost value := by
  rw [← hproject, tsum_probOutput_map_mul]
  simp only [probOutput_probCompLift]

private theorem probEvent_probCompLift {Result : Type} (computation : ProbComp Result) (event : Result → Prop) :
    Pr[event | (liftM computation : PMF Result)] = Pr[event | computation] := by
  simp only [probEvent_eq_tsum_ite]
  rfl

theorem originalCertificateSource_full_le_count_add_exception (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) :
    Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      (∑' result, Pr[= result | certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] *
        certificateBankCount result.2.2.2.2.1.bank) +
      Pr[fun result => CertificateGameExceptional result.2 |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] := by
  let law : SPMF CertificateContextResult := liftM (certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false)
  have hsource : Pr[OriginalFullCertificate | originalCertificateSource adversary] =
      Pr[fun result => OriginalFullCertificate result.original | law] := by
    have h := congrArg (fun source : PMF OriginalCertificateResult => Pr[OriginalFullCertificate | source])
      (certificateContextGame_original adversary q Finset.univ (fun _ => proposalPrefixStop) false)
    rw [probEvent_map, probEvent_probCompLift] at h
    simpa only [law, SPMF.probEvent_liftM, Function.comp_def] using h.symm
  rw [hsource]
  change Pr[fun result => OriginalFullCertificate result.original | law] ≤
    (∑' result, Pr[= result | law] * certificateBankCount result.2.2.2.2.1.bank) +
    Pr[fun result => CertificateGameExceptional result.2 | law]
  refine (probEvent_mono (q := fun result =>
    (OriginalFullCertificate result.original ∧ ¬CertificateGameExceptional result.2) ∨ CertificateGameExceptional result.2)
      (fun result _ h => by by_cases hc : CertificateGameExceptional result.2; exact Or.inr hc; exact Or.inl ⟨h, hc⟩)).trans
    ((probEvent_or_le law _ _).trans (add_le_add ?_ le_rfl))
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result hr h
  exact certificateContextGame_full_count adversary q hbudget hbound result (by simpa only [law, SPMF.support_eq_support, SPMF.support_liftM] using hr) h.1 h.2

theorem originalCertificateSource_full_le_message_add_exception (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) :
    Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      (2 ^ 128 : ENNReal)⁻¹ *
        (∑' result, Pr[= result | certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] *
          (result.2.2.2.2.1.messageCalls : ENNReal)) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      Pr[fun result => CertificateGameExceptional result.2 |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] := by
  have h := expected_certificateCacheGame_full_unit_count_le adversary q (fun _ _ _ _ _ => false) hbudget hbound
  dsimp only at h
  simp only [Bool.or_false] at h
  rw [← certificateContextGame_project adversary q Finset.univ (fun _ => proposalPrefixStop) false] at h
  simp only [tsum_probOutput_map_mul] at h
  exact (originalCertificateSource_full_le_count_add_exception adversary q hbudget hbound).trans (add_le_add h le_rfl)

noncomputable def originalCertificateMessageCost (adversary : Adversary) : ENNReal :=
  ∑' generated, Pr[= generated | (simulateQ romImpl scheme.keygen).run ∅] *
    expectedBoundaryMessageCalls generated.1.2.parameter
      (simulateQ (expandedAdversaryImpl generated.1.2) (retainedGameRestComputation adversary generated.1.1)) generated.2

theorem certificateContextGame_messageCalls_le_original (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateContextGame adversary budget required stopAfter stopped] *
      (result.2.2.2.2.1.messageCalls : ENNReal)) ≤ originalCertificateMessageCost adversary := by
  rw [certificateContextGame, tsum_probOutput_bind_mul]
  calc
    _ ≤ ∑' generated, Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
        expectedBoundaryMessageCalls generated.1.1.2.parameter
          (simulateQ (expandedAdversaryImpl generated.1.1.2)
            (retainedGameRestComputation adversary generated.1.1.1)) generated.2 := by
      apply ENNReal.tsum_le_tsum
      intro generated
      apply mul_le_mul' le_rfl
      rw [tsum_probOutput_bind_mul]
      simp only [tsum_probOutput_pure_mul]
      simpa only [initialCertificateMonitor, Nat.cast_zero, zero_add] using
        expected_certificateCacheProposal_messageCalls_le_original generated.1.1.2 budget required (stopAfter generated.1.1.2)
          (retainedGameRestComputation adversary generated.1.1.1)
          ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false)
    _ = _ := by
      exact expected_probCompLift_of_map_eq (boundaryRun 0 scheme.keygen ∅)
        ((simulateQ romImpl scheme.keygen).run ∅) (fun result => (result.1.1, result.2))
        (boundaryRun_forget 0 scheme.keygen ∅) (fun generated =>
          expectedBoundaryMessageCalls generated.1.2.parameter
            (simulateQ (expandedAdversaryImpl generated.1.2)
              (retainedGameRestComputation adversary generated.1.1)) generated.2)

theorem originalCertificateSource_full_le_original_message_add_exception (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) :
    Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      (2 ^ 128 : ENNReal)⁻¹ * originalCertificateMessageCost adversary + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      Pr[fun result => CertificateGameExceptional result.2 |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] :=
  (originalCertificateSource_full_le_message_add_exception adversary q hbudget hbound).trans
    (add_le_add (add_le_add (mul_le_mul' le_rfl
      (certificateContextGame_messageCalls_le_original adversary q Finset.univ (fun _ => proposalPrefixStop) false)) le_rfl) le_rfl)

end SphincsSecurity.Concrete
