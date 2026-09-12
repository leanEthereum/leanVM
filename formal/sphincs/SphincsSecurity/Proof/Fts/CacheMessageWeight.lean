import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeUniform
import SphincsSecurity.Proof.Fts.JointProbeMessageAnswers
import SphincsSecurity.Proof.Fts.JointProbeMessageReserve
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cacheMessageEntryWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  match cache input with
  | none => 0
  | some output => if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) then
      weight input (hashOutputFewTimeView output) else 0

noncomputable def cacheMessageWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) : ENNReal :=
  ∑' input, cacheMessageEntryWeight parameter weight cache input

theorem cacheMessageWeight_messageAnswers_congr (parameter : PublicParameter)
    (before after : QueryCache HashSpec) (hanswers : messageAnswers parameter before = messageAnswers parameter after)
    (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight parameter weight before = cacheMessageWeight parameter weight after := by
  apply tsum_congr
  intro input
  by_cases hm : MessageHashInput parameter input
  · obtain ⟨payload, rfl⟩ := hm
    have heq := congrFun hanswers payload
    change before (tweakableHashInput parameter .message payload) = after (tweakableHashInput parameter .message payload) at heq
    simp only [cacheMessageEntryWeight, heq]
  · unfold cacheMessageEntryWeight
    cases before input <;> cases after input <;> simp [hm]

theorem cacheMessageWeight_mono (parameter : PublicParameter)
    (first second : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec)
    (h : ∀ input target, first input target ≤ second input target) :
    cacheMessageWeight parameter first cache ≤ cacheMessageWeight parameter second cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  unfold cacheMessageEntryWeight
  cases cache input with
  | none => exact le_rfl
  | some output => simp only; split_ifs; exact h input _; exact le_rfl

theorem cacheMessageWeight_add (parameter : PublicParameter)
    (first second : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) :
    cacheMessageWeight parameter (fun input target => first input target + second input target) cache =
      cacheMessageWeight parameter first cache + cacheMessageWeight parameter second cache := by
  rw [cacheMessageWeight, cacheMessageWeight, cacheMessageWeight, ← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  unfold cacheMessageEntryWeight
  cases cache input <;> simp only
  · exact (add_zero _).symm
  · split_ifs <;> simp only [add_zero]

theorem cacheMessageWeight_mul_right (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) (factor : ENNReal) :
    cacheMessageWeight parameter (fun input view => weight input view * factor) cache =
      cacheMessageWeight parameter weight cache * factor := by
  unfold cacheMessageWeight
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro input
  unfold cacheMessageEntryWeight
  cases cache input with
  | none => exact (zero_mul _).symm
  | some output => simp only; split_ifs <;> simp only [zero_mul]

theorem cacheMessageWeight_sum {α : Type} [DecidableEq α] (parameter : PublicParameter) (indices : Finset α)
    (weight : α → HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) :
    cacheMessageWeight parameter (fun input source => ∑ index ∈ indices, weight index input source) cache =
      ∑ index ∈ indices, cacheMessageWeight parameter (weight index) cache := by
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, cacheMessageWeight, cacheMessageEntryWeight]
      apply ENNReal.tsum_eq_zero.mpr
      intro input
      cases cache input <;> simp
  | @insert index indices hnot ih =>
      simp only [Finset.sum_insert hnot, cacheMessageWeight_add, ih]

theorem cacheMessageWeight_of_no_message (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none) :
    cacheMessageWeight parameter weight cache = 0 := by
  unfold cacheMessageWeight
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases hcache : cache input with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood
      · rw [hnone input hgood.1] at hcache
        contradiction
      · rfl

theorem cacheMessageWeight_cacheQuery (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hfresh : cache input = none) :
    cacheMessageWeight parameter weight (cache.cacheQuery input output) =
      cacheMessageWeight parameter weight cache +
        (if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) then
          weight input (hashOutputFewTimeView output) else 0) := by
  unfold cacheMessageWeight
  rw [ENNReal.tsum_eq_add_tsum_ite (f := cacheMessageEntryWeight parameter weight (cache.cacheQuery input output)) input,
    ENNReal.tsum_eq_add_tsum_ite (f := cacheMessageEntryWeight parameter weight cache) input]
  simp only [cacheMessageEntryWeight, QueryCache.cacheQuery_self, hfresh, zero_add]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro other
  by_cases heq : other = input
  · simp only [heq, if_true]
  · simp only [heq, if_false, QueryCache.cacheQuery_of_ne cache output heq]

theorem expected_cacheMessageWeight {α : Type} (parameter : PublicParameter)
    (weight : α → HashInput → FewTimeView → ENNReal) (computation : ProbComp α)
    (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | computation] * cacheMessageWeight parameter (weight result) cache) =
      cacheMessageWeight parameter (fun input target => ∑' result, Pr[= result | computation] * weight result input target) cache := by
  simp only [cacheMessageWeight, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro input
  unfold cacheMessageEntryWeight
  cases cache input with
  | none => simp only [mul_zero, tsum_zero]
  | some output => simp only; split_ifs <;> simp only [mul_zero, tsum_zero]

theorem cacheMessageWeight_fresh_restriction (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) :
    cacheMessageWeight parameter (fun input target => if cache input = none then weight input target else 0) cache = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases hcache : cache input <;> simp [hcache]

theorem cacheMessageWeight_of_le (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (before after : QueryCache HashSpec)
    (hcache : before ≤ after) :
    cacheMessageWeight parameter weight after = cacheMessageWeight parameter weight before +
      cacheMessageWeight parameter (fun input target => if before input = none then weight input target else 0) after := by
  rw [cacheMessageWeight, cacheMessageWeight, cacheMessageWeight, ← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  cases hbefore : before input with
  | none => simp only [cacheMessageEntryWeight, hbefore, if_true, zero_add]
  | some output =>
      simp only [cacheMessageEntryWeight, hbefore, hcache hbefore, reduceCtorEq, if_false]
      split_ifs <;> simp only [add_zero]

end SphincsSecurity.Concrete
