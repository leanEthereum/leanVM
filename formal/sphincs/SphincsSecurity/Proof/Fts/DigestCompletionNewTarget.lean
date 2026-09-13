import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestCompletionCacheGrowth
import SphincsSecurity.Proof.Fts.FreshTargetEnvelope
import SphincsSecurity.Proof.Fts.FreshTargetPayload
import SphincsSecurity.Proof.Fts.NewTargetEnvelopeCharge
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop

theorem digestCompletion_new_targetShapeMoments_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves))
    (hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none)
    (target : FewTimeView) :
    targetShapeMoments key result.2 (log ++ [⟨message, result.1.1⟩]) (messageDigestPayload key.root message randomness) target =
      targetShapeMoments key before log (messageDigestPayload key.root message randomness) target := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  have heligible : eligibleSigningView? (messageAnswers key.parameter loop.2) key.root
      (messageDigestPayload key.root message randomness) ⟨message, result.1.1⟩ = none := by
    cases hs : result.1.1 with
    | none => simp [eligibleSigningView?]
    | some signature =>
        obtain ⟨otherIndex, otherLeaves, hother⟩ := hcompletion.1.2 signature hs
        have hr : signature.randomness = randomness := congrArg Prod.fst (Option.some.inj (hother.symm.trans hselected))
        simp [eligibleSigningView?, hr]
  have hlog (required : Finset FtsTree) :
      normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) (messageDigestPayload key.root message randomness) target required =
        normalizedTargetLogProduct key before log (messageDigestPayload key.root message randomness) target required := by
    have heq : normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩])
        (messageDigestPayload key.root message randomness) target required =
      normalizedTargetLogProduct key loop.2 (log ++ [⟨message, result.1.1⟩])
        (messageDigestPayload key.root message randomness) target required := by
      unfold normalizedTargetLogProduct normalizedTargetLogMatch
      rw [hcompletion.2]
    rw [heq]
    exact normalizedTargetLogProduct_append_none key before loop.2 log _ _ target required hcache hsigned heligible
  funext groups remaining
  unfold targetShapeMoments
  rw [hlog]
  congr 1
  apply Finset.prod_congr rfl
  intro group _
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion]
  simp only [selectedLoopInputWeight, hselected, hfresh, if_true, add_zero]

theorem digestCompletion_newTargetEnvelopeCharge_eq_selected
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining =
      selectedLoopInputWeight key message (fun input target => if before input = none then
        targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeMoments key before log (payloadOf input) target) groups remaining else 0) loop := by
  unfold newTargetEnvelopeCharge
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion,
    cacheMessageWeight_fresh_restriction, zero_add]
  cases hs : loop.1 with
  | none => simp only [selectedLoopInputWeight, hs]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
      · simp only [selectedLoopInputWeight, hs, hfresh, if_true, payloadOf_tweakableHashInput]
        rw [digestCompletion_new_targetShapeMoments_eq key message before loop hloop result hcompletion
          log hsigned randomness index leaves hs hfresh]
      · simp only [selectedLoopInputWeight, hs, if_neg hfresh]

theorem expected_digestCompletion_newTargetEnvelopeCharge_le_mass_mul {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        uniform reuse arrival queries signings groups remaining) ≤
      freshDigestSelectionProbability key message before *
        ((Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key before log) groups.card remaining.card) := by
  by_cases hexists : ∃ payload, before (tweakableHashInput key.parameter .message payload) = none
  · obtain ⟨reference, hreference⟩ := hexists
    let weight := fun source => targetShapeEnvelope uniform reuse arrival queries signings
      (targetShapeMoments key before log reference source) groups remaining
    have hbound := expected_digestCompletion_freshCost_le key message before finish
      (fun result => newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        uniform reuse arrival queries signings groups remaining) weight (by
          intro loop hl result hr
          rw [digestCompletion_newTargetEnvelopeCharge_eq_selected key message before loop hl (record result)
            (hcompletion loop hl result hr) log hsigned]
          cases hs : loop.1 with
          | none => simp only [selectedLoopInputWeight, hs, le_refl]
          | some selected =>
              obtain ⟨randomness, index, leaves⟩ := selected
              by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
              · simp only [selectedLoopInputWeight, hs, hfresh, if_true, payloadOf_tweakableHashInput, weight]
                rw [targetShapeMoments_fresh_payload_eq key before log _ reference hfresh hreference hsigned]
              · simp only [selectedLoopInputWeight, hs, if_neg hfresh, le_refl])
    apply hbound.trans_eq
    exact congrArg (fun value => freshDigestSelectionProbability key message before * value)
      (expected_fresh_targetShapeEnvelope key before log reference hreference hsigned
        uniform reuse arrival queries signings groups remaining hvalid)
  · have hzero (result : α) : newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        uniform reuse arrival queries signings groups remaining = 0 :=
      newTargetEnvelopeCharge_of_no_new key before (record result).2 _ uniform reuse arrival queries signings groups remaining
        (fun payload _ hfresh _ _ => hexists ⟨payload, hfresh⟩)
    simp only [hzero, mul_zero, tsum_zero, zero_le]

end SphincsSecurity.Concrete
