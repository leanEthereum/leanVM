import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestCompletionCacheGrowth
import SphincsSecurity.Proof.Fts.ConcreteTargetShapeQuery
import SphincsSecurity.Proof.Fts.InterleavedCoverStep

/-! ## WorldTargetShapeEnvelope -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def observedTargetShapeVector (key : SecretKey) (payload : HashInput) (target : FewTimeView) (state : CoverLogState) : TargetShapeVector :=
  targetShapeMoments key state.1 state.2 payload target

theorem expected_fresh_targetShape_le (key : SecretKey) (payload : HashInput) (target : FewTimeView)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      observedTargetShapeVector key payload target (before.cacheQuery input output, log) groups remaining) ≤
        targetShapeQuery (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          (observedTargetShapeVector key payload target (before, log)) groups remaining := by
  have h := expected_randomOracle_targetShapeMoments_le key before log payload target groups remaining hvalid input hsigned
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul] at h
  exact h

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def reuseTargetMixedSigningEnvelope (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) (reuse : ENNReal) : ENNReal :=
  normalizedTargetCacheProduct key.parameter cache (tweakableHashInput key.parameter .message payload) target groups *
    (normalizedTargetLogProduct key cache log payload target required +
      (Fintype.card Index : ENNReal)⁻¹ * (∑ selected ∈ required.powerset.erase ∅, normalizedTargetLogProduct key cache log payload target (required \ selected)) +
      (∑ selected ∈ required.powerset.erase ∅,
        normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
          normalizedTargetLogProduct key cache log payload target (required \ selected)) * reuse) +
    (Fintype.card Index : ENNReal)⁻¹ *
      ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
        ∑ trees ∈ required.powerset,
          (∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected,
            normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target (groups slot)) *
              normalizedTargetLogProduct key cache log payload target (required \ trees)

theorem digestCompletion_normalizedTargetMixedMoment_eq_frozen_add_growth (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) :
    normalizedTargetMixedMoment key result.2 log payload target groups required =
      normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups *
        normalizedTargetLogProduct key result.2 log payload target required +
          targetMixedSigningGrowth key before result.2 log payload target groups required := by
  have hmono : normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups ≤
      normalizedTargetCacheProduct key.parameter result.2 (tweakableHashInput key.parameter .message payload) target groups := by
    apply Finset.prod_le_prod'
    intro slot _
    simp only [normalizedCachedTargetSubsetMatch_eq_weight]
    rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion]
    exact le_self_add
  unfold normalizedTargetMixedMoment targetMixedSigningGrowth
  rw [← add_mul, add_tsub_cancel_of_le hmono]

theorem expected_digestCompletion_normalizedTargetMixedMoment_le_of_exactReuse {α : Type} (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree)
    (hgroups : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hremaining : ∀ slot, Disjoint (groups slot) required)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      normalizedTargetMixedMoment key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required) ≤
      reuseTargetMixedSigningEnvelope key before log payload target groups required reuse := by
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      normalizedTargetMixedMoment key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required) =
      normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups *
        (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
          normalizedTargetLogProduct key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target required) +
      ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
        targetMixedSigningGrowth key before (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish)
    · rw [mem_support_bind_iff] at hresult
      obtain ⟨loop, hl, hr⟩ := hresult
      rw [digestCompletion_normalizedTargetMixedMoment_eq_frozen_add_growth key message before loop hl (record result)
        (hcompletion loop hl result hr) _ payload target groups required]
      ring
    · rw [probOutput_eq_zero_of_not_mem_support hresult]
      simp only [zero_mul, mul_zero, add_zero]
  rw [heq]
  apply add_le_add
  · exact mul_le_mul' le_rfl (expected_digestCompletion_normalizedTargetLogProduct_le_of_exactReuse key message before finish record hcompletion log payload target required hsigned reuse hreuse)
  · apply ((expected_digestCompletion_targetMixedGrowth_le_freshMass key message before finish record hcompletion
      log payload target groups required hsigned).trans
        (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before))).trans_eq
    exact expected_targetMixedGrowthPolynomial _ _ groups required target hgroups hdisjoint hremaining

theorem targetShapeSigning_eq_reuseIndexedEnvelope (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) (reuse : ENNReal) :
    targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ reuse
      (targetShapeMoments key cache log payload target) groups remaining =
        reuseTargetMixedSigningEnvelope key cache log payload target (targetGroupAt groups) remaining reuse := by
  unfold reuseTargetMixedSigningEnvelope
  rw [targetShapeMoments_cross_eq]
  simp only [normalizedTargetCacheProduct, prod_targetGroupAt]
  unfold targetShapeSigning
  rw [targetShapeMoments_reuse_eq key cache log payload target groups remaining hvalid]
  have htree : targetTreeLower (targetShapeMoments key cache log payload target) groups remaining =
      (∏ group ∈ groups, normalizedCachedTargetSubsetMatch key.parameter cache
        (tweakableHashInput key.parameter .message payload) target group) *
          ∑ trees ∈ remaining.powerset.erase ∅, normalizedTargetLogProduct key cache log payload target (remaining \ trees) := by
    simp only [targetTreeLower, targetShapeMoments, Finset.mul_sum]
  rw [htree]
  unfold targetShapeMoments
  ring

theorem expected_digestCompletion_targetShapeMoments_le_of_exactReuse {α : Type} (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      targetShapeMoments key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups remaining) ≤
        targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ reuse
          (targetShapeMoments key before log payload target) groups remaining := by
  simp only [targetShapeMoments_eq_indexed]
  rw [targetShapeSigning_eq_reuseIndexedEnvelope key before log payload target groups remaining hvalid reuse]
  exact expected_digestCompletion_normalizedTargetMixedMoment_le_of_exactReuse key message before finish record hcompletion log payload target (targetGroupAt groups) remaining
    (fun slot => hvalid.nonempty _ (targetGroupAt_mem groups slot))
    (fun i j hij => hvalid.disjoint _ (targetGroupAt_mem groups i) _ (targetGroupAt_mem groups j)
      (fun heq => hij (targetGroupAt_injective groups heq)))
    (fun slot => hvalid.remaining _ (targetGroupAt_mem groups slot)) hsigned reuse hreuse

theorem expected_signWithView_targetShapeMoments_le_of_exactReuse (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetShapeMoments key result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups remaining) ≤
        targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ reuse
          (targetShapeMoments key before log payload target) groups remaining := by
  rw [signWithView_run_eq_digestCompletion]
  exact expected_digestCompletion_targetShapeMoments_le_of_exactReuse key message before
    (originalDigestCompletion key) id (fun loop _ result hr => originalDigestCompletion_preservesMessages key loop result hr)
    log payload target groups remaining hvalid hsigned reuse hreuse

theorem expected_logTraced_sign_targetShape_le_of_exactReuse (key : SecretKey) (reuse : ENNReal)
    (payload : HashInput) (target : FewTimeView) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (message : Message) (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedTargetShapeVector key payload target result.2 groups remaining) ≤
        targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ reuse
          (observedTargetShapeVector key payload target state) groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  have heq := congrArg (fun computation : ProbComp (Option Signature × QueryCache HashSpec) =>
    ∑' result, Pr[= result | computation] *
      observedTargetShapeVector key payload target (result.2, state.2 ++ [⟨message, result.1⟩]) groups remaining) hrun
  rw [tsum_probOutput_map_mul] at heq
  exact heq.le.trans (expected_signWithView_targetShapeMoments_le_of_exactReuse key message state.1 state.2
    payload target groups remaining hvalid hsigned reuse hreuse)

end SphincsSecurity.Concrete
