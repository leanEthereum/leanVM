import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheMessageSignerWeight
import SphincsSecurity.Proof.Fts.CachedDigestRate
import SphincsSecurity.Proof.Fts.DigestLoopRecord
import SphincsSecurity.Proof.Fts.FewTimeFixedPrehit
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop

def selectedLoopInputWeight (key : SecretKey) (message : Message)
    (weight : HashInput → FewTimeView → ENNReal) (result : DigestLoopRecord) : ENNReal :=
  match result.1 with
  | none => 0
  | some (randomness, index, leaves) => weight
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness))
      (selectedFewTimeView index leaves)

theorem probEvent_signDigestLoop_fixedPrehit_le_exactWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (input : HashInput) (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView (onlyInputCache cache input) key message P |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] ≤
      exactDigestReuseWeight key message cache := by
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message
    (onlyInputCache cache input) cache (onlyInputCache_le cache input), cachedDigestAttemptRate_eq_count]
  calc
    _ = cachedMessageEntryCountWhere (onlyInputCache cache input) key.parameter key.root message P *
        exactDigestReuseWeight key message cache := by unfold exactDigestReuseWeight; ring
    _ ≤ 1 * exactDigestReuseWeight key message cache := mul_le_mul'
      (cachedMessageEntryCountWhere_onlyInput_le_one cache input key.parameter key.root message P) le_rfl
    _ = _ := one_mul _

theorem selectedLoopInputWeight_le_fresh_add_prehit
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (result : DigestLoopRecord)
    (hresult : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)) :
    selectedLoopInputWeight key message weight result ≤
      (∑' view, if FreshSelectedView before key message (· = view) result then uniformWeight view else 0) +
      (∑' input, if PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) result then
        cachedSignerInputWeight key message before weight input else 0) := by
  obtain ⟨selected, after⟩ := result
  cases selected with
  | none => simp only [selectedLoopInputWeight]; exact bot_le
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      let input := tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)
      let view := selectedFewTimeView index leaves
      change weight input view ≤ _
      cases hbefore : before input with
      | none =>
          have hfresh : FreshSelectedView before key message (· = view) (some (randomness, index, leaves), after) :=
            ⟨randomness, index, leaves, rfl, hbefore, rfl⟩
          apply (hweight input view).trans
          apply le_trans ?_ le_self_add
          exact (le_of_eq (if_pos hfresh).symm).trans (ENNReal.le_tsum view)
      | some output =>
          have hattempt := signDigestLoop_initial_cached_result digestAttemptLimit key message randomness
            index leaves before after output hbefore hresult
          have hview : view = hashOutputFewTimeView output := signAttemptResultOfOutput_view output index leaves hattempt
          have hadmissible : Admissible (truncateMessageDigest output) :=
            (signAttemptResultOfOutput_ne_none_iff output).mp (by rw [hattempt]; exact Option.some_ne_none _)
          have hsource : cachedSignerInputWeight key message before weight input = weight input view := by
            simp only [cachedSignerInputWeight, hbefore]
            rw [if_pos ⟨⟨randomness, rfl⟩, hadmissible⟩, ← hview]
          have hprehit : PrehitSelectedView (onlyInputCache before input) key message (fun _ => True)
              (some (randomness, index, leaves), after) := by
            refine ⟨randomness, index, leaves, rfl, output, ?_, hattempt, trivial⟩
            simpa [onlyInputCache, input] using hbefore
          apply le_trans ?_ (le_add_left le_rfl)
          rw [← hsource]
          exact (le_of_eq (if_pos hprehit).symm).trans (ENNReal.le_tsum input)

theorem expected_selectedLoopInputWeight_le_exactReuse
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
      selectedLoopInputWeight key message weight result) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
      (∑' input, cachedSignerInputWeight key message before weight input) * exactDigestReuseWeight key message before := by
  have hexpect {α : Type} (event : α → DigestLoopRecord → Prop) (value : α → ENNReal) :
      (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        ∑' index, if event index result then value index else 0) =
      ∑' index, Pr[event index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] * value index := by
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro index
    rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro result
    split_ifs <;> simp
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        ((∑' view, if FreshSelectedView before key message (· = view) result then uniformWeight view else 0) +
          ∑' input, if PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) result then
            cachedSignerInputWeight key message before weight input else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)
      · exact mul_le_mul' le_rfl (selectedLoopInputWeight_le_fresh_add_prehit key message before weight uniformWeight hweight result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' view, Pr[FreshSelectedView before key message (· = view) |
          (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] * uniformWeight view) +
        ∑' input, Pr[PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) |
          (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
            cachedSignerInputWeight key message before weight input := by
      simp only [mul_add, ENNReal.tsum_add, hexpect]
    _ ≤ (∑' view, (freshDigestSelectionProbability key message before *
          Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)]) * uniformWeight view) +
        ∑' input, exactDigestReuseWeight key message before * cachedSignerInputWeight key message before weight input := by
      apply add_le_add
      · apply ENNReal.tsum_le_tsum
        intro view
        apply mul_le_mul' _ le_rfl
        exact le_of_eq (by
          simpa only [probEvent_eq_eq_probOutput, freshDigestSelectionProbability] using
            (probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform digestAttemptLimit key message before before (· = view)
              (onlyRejectedNewMessageEntries_self before key message)))
      · exact ENNReal.tsum_le_tsum (fun input => mul_le_mul'
          (probEvent_signDigestLoop_fixedPrehit_le_exactWeight key message before input (fun _ => True)) le_rfl)
    _ = _ := by simp only [mul_assoc, ENNReal.tsum_mul_left]; rw [mul_comm (exactDigestReuseWeight key message before)]

theorem expected_freshSelectedLoopInputWeight_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : FewTimeView → ENNReal) :
    (∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
      selectedLoopInputWeight key message (fun input source => if before input = none then weight source else 0) loop) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source := by
  have hzero (input : HashInput) : cachedSignerInputWeight key message before
      (fun input source => if before input = none then weight source else 0) input = 0 := by
    unfold cachedSignerInputWeight
    cases hc : before input with
    | none => rfl
    | some output => simp only [hc, reduceCtorEq, if_false, ite_self]
  have hbound := expected_selectedLoopInputWeight_le_exactReuse key message before
    (fun input source => if before input = none then weight source else 0) weight (by
      intro input source
      split_ifs; exact le_rfl; exact bot_le)
  simpa only [hzero, tsum_zero, zero_mul, add_zero] using hbound

def DigestCompletionConsistent (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  result.1.2 = selectedLoopView? loop ∧
    ∀ signature, result.1.1 = some signature →
      ∃ index leaves, loop.1 = some (signature.randomness, index, leaves)

theorem successfulSignerInputWeight_le_selectedLoopInputWeight
    (key : SecretKey) (message : Message) (weight : HashInput → FewTimeView → ENNReal)
    (loop : DigestLoopRecord) (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : DigestCompletionConsistent loop result) :
    successfulSignerInputWeight key message weight result ≤ selectedLoopInputWeight key message weight loop := by
  cases hs : result.1.1 with
  | none => simp only [successfulSignerInputWeight, hs]; exact bot_le
  | some signature =>
      obtain ⟨index, leaves, hloop⟩ := hconsistent.2 signature hs
      simp only [successfulSignerInputWeight, hs, hconsistent.1, selectedLoopView?, hloop,
        Option.map_some, selectedLoopInputWeight, le_refl]

theorem expected_digestCompletion_cost_le_selected {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α) (cost : α → ENNReal)
    (weight : HashInput → FewTimeView → ENNReal)
    (hcost : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), cost result ≤ selectedLoopInputWeight key message weight loop) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] * cost result) ≤
      ∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        selectedLoopInputWeight key message weight loop := by
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro loop
  by_cases hl : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)
  · apply mul_le_mul' le_rfl
    calc
      _ ≤ ∑' result, Pr[= result | finish loop] * selectedLoopInputWeight key message weight loop := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (finish loop)
        · exact mul_le_mul' le_rfl (hcost loop hl result hr)
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · rw [probOutput_eq_zero_of_not_mem_support hl, zero_mul, zero_mul]

theorem expected_digestCompletion_successfulInputWeight_le_selected {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      ∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        selectedLoopInputWeight key message weight loop :=
  expected_digestCompletion_cost_le_selected key message before finish
    (fun result => successfulSignerInputWeight key message weight (record result)) weight
    (fun loop hl result hr => successfulSignerInputWeight_le_selectedLoopInputWeight
      key message weight loop (record result) (hconsistent loop hl result hr))

theorem expected_digestCompletion_freshCost_le {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α) (cost : α → ENNReal) (weight : FewTimeView → ENNReal)
    (hcost : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), cost result ≤
        selectedLoopInputWeight key message (fun input source => if before input = none then weight source else 0) loop) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] * cost result) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source :=
  (expected_digestCompletion_cost_le_selected key message before finish cost _ hcost).trans
    (expected_freshSelectedLoopInputWeight_le key message before weight)

theorem expected_digestCompletion_successfulInputWeight_le_exactReuse {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
      (∑' input, cachedSignerInputWeight key message before weight input) * exactDigestReuseWeight key message before :=
  (expected_digestCompletion_successfulInputWeight_le_selected key message before finish record hconsistent weight).trans
    (expected_selectedLoopInputWeight_le_exactReuse key message before weight uniformWeight hweight)

theorem expected_digestCompletion_successfulInputWeight_le_allMessage {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
      cacheMessageWeight key.parameter weight before * reuse :=
  (expected_digestCompletion_successfulInputWeight_le_exactReuse key message before finish record hconsistent
    weight uniformWeight hweight).trans (add_le_add le_rfl (mul_le_mul'
      (ENNReal.tsum_le_tsum (cachedSignerInputWeight_le_cacheMessageEntryWeight key message before weight)) hreuse))

end SphincsSecurity.Concrete
