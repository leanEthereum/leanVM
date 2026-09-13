import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestCompletionLogGrowth
import SphincsSecurity.Proof.Fts.SingleMessageCacheGrowth

/-! ## SignerNewMessageUnique -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem signDigestLoop_new_payload_eq_selected (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    payload = messageDigestPayload key.root message randomness := by
  obtain ⟨selected, selectedIndex, selectedLeaves, hselected, hpayload⟩ := signDigestLoop_new_admissible_selected attempts key message
    before after (some (randomness, index, leaves)) hloop payload output hbefore hafter hadmissible
  have hrandomness : randomness = selected := congrArg Prod.fst (Option.some.inj hselected)
  exact hpayload.trans (congrArg _ hrandomness.symm)

end SphincsSecurity.Concrete

/-! ## TargetSigningCacheGrowth -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetMixedSigningGrowth (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) : ENNReal :=
  (normalizedTargetCacheProduct key.parameter after (tweakableHashInput key.parameter .message payload) target groups -
    normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups) *
      normalizedTargetLogProduct key after log payload target required

noncomputable def newTargetMixedGrowthWeight (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) (source : FewTimeView) : ENNReal :=
  targetMixedGrowthPolynomial
    (fun slot => normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot))
    (normalizedTargetLogMatch key before log payload target) groups required target source

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop

theorem signDigestLoop_cacheMessageWeight_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight key.parameter weight loop.2 = cacheMessageWeight key.parameter weight before +
      selectedLoopInputWeight key message (fun input source => if before input = none then weight input source else 0) loop := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  obtain ⟨selected, after⟩ := loop
  cases selected with
  | none =>
      simp only [selectedLoopInputWeight, add_zero]
      apply cacheMessageWeight_of_no_new key.parameter weight before after hcache
      intro input output hfresh hmessage hafter hadmissible
      obtain ⟨payload, rfl⟩ := hmessage
      obtain ⟨_, _, _, hselected, _⟩ := signDigestLoop_new_admissible_selected digestAttemptLimit key message
        before after none hloop payload output hfresh hafter hadmissible
      contradiction
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
      · obtain ⟨output, houtput, hadmissible, hview⟩ := signDigestLoop_selected_cached_output digestAttemptLimit key message
          before after randomness index leaves hloop
        simp only [selectedLoopInputWeight, hfresh, if_true]
        rw [← hview]
        apply cacheMessageWeight_of_single_new key.parameter weight before after hcache _ output hfresh
          ⟨messageDigestPayload key.root message randomness, rfl⟩ houtput hadmissible
        intro other answer hbefore hmessage hafter hgood
        obtain ⟨payload, rfl⟩ := hmessage
        exact congrArg (tweakableHashInput key.parameter .message)
          (signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before after randomness index leaves hloop
            payload answer hbefore hafter hgood)
      · simp only [selectedLoopInputWeight, if_neg hfresh, add_zero]
        apply cacheMessageWeight_of_no_new key.parameter weight before after hcache
        intro input output hbefore hmessage hafter hadmissible
        obtain ⟨payload, rfl⟩ := hmessage
        have hpayload := signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before after
          randomness index leaves hloop payload output hbefore hafter hadmissible
        exact hfresh (hpayload ▸ hbefore)

theorem digestCompletion_cacheMessageWeight_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight key.parameter weight result.2 = cacheMessageWeight key.parameter weight before +
      selectedLoopInputWeight key message (fun input source => if before input = none then weight input source else 0) loop := by
  rw [cacheMessageWeight_messageAnswers_congr key.parameter result.2 loop.2 hcompletion.2]
  exact signDigestLoop_cacheMessageWeight_eq key message before loop hloop weight

theorem digestCompletion_targetCacheProduct_le_of_fresh (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves))
    (hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) :
    normalizedTargetCacheProduct key.parameter result.2 targetInput target groups ≤
      normalizedTargetCacheProduct key.parameter before targetInput target groups +
        targetCacheArrivalPolynomial (fun slot => normalizedCachedTargetSubsetMatch key.parameter before targetInput target (groups slot))
          groups target (selectedFewTimeView index leaves) := by
  unfold normalizedTargetCacheProduct
  rw [targetCacheProduct_add_arrival]
  apply Finset.prod_le_prod'
  intro slot _
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion]
  simp only [selectedLoopInputWeight, hselected, hfresh, if_true]
  apply add_le_add le_rfl
  split_ifs; exact bot_le; exact le_rfl

theorem digestCompletion_targetLogProduct_le_view (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves)) :
    normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required ≤
      ∏ tree ∈ required, (normalizedTargetLogMatch key before log payload target tree +
        normalizedSourceSubsetMatch target (selectedFewTimeView index leaves) {tree}) := by
  let weight := fun input source => if input = tweakableHashInput key.parameter .message payload then 0
    else normalizedTargetLogIncrement key before log payload target required source
  calc
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        successfulSignerInputWeight key message weight result :=
      digestCompletion_normalizedTargetLogProduct_le_input key message before log payload target required hsigned loop hloop result hcompletion
    _ ≤ normalizedTargetLogProduct key before log payload target required + selectedLoopInputWeight key message weight loop :=
      add_le_add le_rfl (successfulSignerInputWeight_le_selectedLoopInputWeight key message weight loop result hcompletion.1)
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        normalizedTargetLogIncrement key before log payload target required (selectedFewTimeView index leaves) := by
      apply add_le_add le_rfl
      simp only [selectedLoopInputWeight, hselected, weight]
      split_ifs; exact bot_le; exact le_rfl
    _ = _ := normalizedTargetLogProduct_add_increment key before log payload target required (selectedFewTimeView index leaves)

theorem digestCompletion_targetMixedGrowth_le_freshInput (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) :
    targetMixedSigningGrowth key before result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups required ≤
      selectedLoopInputWeight key message (fun input source => if before input = none then
        newTargetMixedGrowthWeight key before log payload target groups required source else 0) loop := by
  by_cases hnew : ∃ randomness index leaves, loop.1 = some (randomness, index, leaves) ∧
      before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
  · obtain ⟨randomness, index, leaves, hselected, hfresh⟩ := hnew
    have hproduct := digestCompletion_targetCacheProduct_le_of_fresh key message before loop hloop result hcompletion
      randomness index leaves hselected hfresh (tweakableHashInput key.parameter .message payload) target groups
    have hlog := digestCompletion_targetLogProduct_le_view key message before log payload target required hsigned loop hloop result hcompletion
      randomness index leaves hselected
    simp only [selectedLoopInputWeight, hselected, hfresh, if_true]
    exact mul_le_mul' (tsub_le_iff_right.mpr (hproduct.trans_eq (add_comm _ _))) hlog
  · have hzero (weight : HashInput → FewTimeView → ENNReal) : selectedLoopInputWeight key message
        (fun input source => if before input = none then weight input source else 0) loop = 0 := by
      cases hs : loop.1 with
      | none => simp only [selectedLoopInputWeight, hs]
      | some selected =>
          obtain ⟨randomness, index, leaves⟩ := selected
          have hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ≠ none :=
            fun hc => hnew ⟨randomness, index, leaves, hs, hc⟩
          simp only [selectedLoopInputWeight, hs, if_neg hfresh]
    have hcounts (slot : Fin m) : normalizedCachedTargetSubsetMatch key.parameter result.2
        (tweakableHashInput key.parameter .message payload) target (groups slot) =
        normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot) := by
      simp only [normalizedCachedTargetSubsetMatch_eq_weight]
      rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion, hzero, add_zero]
    simp only [targetMixedSigningGrowth, normalizedTargetCacheProduct, hcounts, tsub_self, zero_mul, zero_le]

theorem expected_digestCompletion_targetMixedGrowth_le_freshMass {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      targetMixedSigningGrowth key before (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newTargetMixedGrowthWeight key before log payload target groups required source :=
  expected_digestCompletion_freshCost_le key message before finish _ _ (fun loop hl result hr =>
    digestCompletion_targetMixedGrowth_le_freshInput key message before log payload target groups required hsigned
      loop hl (record result) (hcompletion loop hl result hr))

end SphincsSecurity.Concrete
