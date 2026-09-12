import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheMessageWeight
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def certificateBankCount (bank : HashInput → Bool) : ENNReal :=
  ∑' input, if bank input then 1 else 0

theorem certificateBankCount_empty : certificateBankCount (fun _ => false) = 0 := by
  simp [certificateBankCount]

theorem one_le_certificateBankCount (bank : HashInput → Bool) (input : HashInput) (hbank : bank input = true) :
    1 ≤ certificateBankCount bank := by
  have h := ENNReal.le_tsum (f := fun input => if bank input then (1 : ENNReal) else 0) input
  simpa only [certificateBankCount, hbank, if_true] using h

noncomputable def bankedCacheWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) : ENNReal :=
  ∑' input, if bank input then 1 else if stopped then 0 else
    cacheMessageEntryWeight parameter weight cache input

theorem bankedCacheWeight_mono (parameter : PublicParameter)
    (first second : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec)
    (hle : ∀ input target, first input target ≤ second input target) :
    bankedCacheWeight parameter first bank stopped cache ≤ bankedCacheWeight parameter second bank stopped cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · unfold cacheMessageEntryWeight
    cases cache input
    · exact le_rfl
    · simp only
      split_ifs
      · exact hle input _
      · exact le_rfl

theorem bankedCacheWeight_discard_le (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank stopped cache ≤ bankedCacheWeight parameter weight bank false cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  cases bank input <;> cases stopped <;> simp

theorem certificateBankCount_le_bankedCacheWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) :
    certificateBankCount bank ≤ bankedCacheWeight parameter weight bank stopped cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  split_ifs <;> first | exact le_rfl | exact zero_le

theorem bankedCacheWeight_stopped (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank true cache = certificateBankCount bank := by
  simp only [bankedCacheWeight, certificateBankCount, if_true]

theorem bankedCacheWeight_live (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank false cache = certificateBankCount bank +
      cacheMessageWeight parameter (fun input target => if bank input then 0 else weight input target) cache := by
  rw [bankedCacheWeight, certificateBankCount, cacheMessageWeight, ← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  cases hbank : bank input <;> cases hcache : cache input <;>
    simp [cacheMessageEntryWeight, hbank, hcache]

theorem bankedCacheWeight_bank_le (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank completed : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec)
    (hcompleted : ∀ input, completed input = true →
      1 ≤ cacheMessageEntryWeight parameter weight cache input) :
    bankedCacheWeight parameter weight (fun input => bank input || completed input) stopped cache ≤
      bankedCacheWeight parameter weight bank false cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  cases hbank : bank input <;> cases hcomplete : completed input <;>
    simp only [hbank, hcomplete, Bool.false_or, Bool.true_or, Bool.false_eq_true, if_true, if_false, le_refl]
  · cases stopped <;> simp
  · exact hcompleted input hcomplete

theorem expected_bankedCacheWeight_step_le_of_split {α : Type} (parameter : PublicParameter)
    (computation : ProbComp α) (before : QueryCache HashSpec) (after : α → QueryCache HashSpec)
    (weight : α → HashInput → FewTimeView → ENNReal)
    (initial : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (completed : α → HashInput → Bool) (stopped : α → Bool) (charge : ENNReal)
    (hsplit : ∀ result ∈ support computation, ∀ value : HashInput → FewTimeView → ENNReal,
      cacheMessageWeight parameter value (after result) = cacheMessageWeight parameter value before +
        cacheMessageWeight parameter (fun input target => if before input = none then value input target else 0) (after result))
    (hcompleted : ∀ result ∈ support computation, ∀ input, completed result input = true →
      1 ≤ cacheMessageEntryWeight parameter (weight result) (after result) input)
    (hold : ∀ input target, (∑' result, Pr[= result | computation] * weight result input target) ≤ initial input target)
    (hnew : (∑' result, Pr[= result | computation] *
      cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
        (after result)) ≤ charge) :
    (∑' result, Pr[= result | computation] *
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result)) ≤ bankedCacheWeight parameter initial bank false before + charge := by
  let pending := fun result input target => if bank input then 0 else weight result input target
  have hstep (result : α) (hr : result ∈ support computation) :
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result) ≤
      certificateBankCount bank + cacheMessageWeight parameter (pending result) before +
        cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
          (after result) := by
    apply (bankedCacheWeight_bank_le parameter (weight result) bank (completed result) (stopped result)
      (after result) (hcompleted result hr)).trans
    rw [bankedCacheWeight_live, hsplit result hr (pending result), ← add_assoc]
    apply add_le_add le_rfl
    apply cacheMessageWeight_mono
    intro input target
    dsimp only [pending]
    split_ifs <;> first | exact le_rfl | exact zero_le
  have hold' : (∑' result, Pr[= result | computation] * cacheMessageWeight parameter (pending result) before) ≤
      cacheMessageWeight parameter (fun input target => if bank input then 0 else initial input target) before := by
    rw [expected_cacheMessageWeight]
    apply cacheMessageWeight_mono
    intro input target
    dsimp only [pending]
    cases hb : bank input
    · simpa only [hb, Bool.false_eq_true, if_false] using hold input target
    · simp only [if_true, mul_zero, tsum_zero, le_refl]
  calc
    _ ≤ ∑' result, Pr[= result | computation] *
        (certificateBankCount bank + cacheMessageWeight parameter (pending result) before +
          cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
            (after result)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (hstep result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' result, Pr[= result | computation]) * certificateBankCount bank +
        (∑' result, Pr[= result | computation] * cacheMessageWeight parameter (pending result) before) +
        (∑' result, Pr[= result | computation] *
          cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
            (after result)) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ certificateBankCount bank +
        cacheMessageWeight parameter (fun input target => if bank input then 0 else initial input target) before + charge :=
      add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) hold') hnew
    _ = _ := by rw [bankedCacheWeight_live]

theorem expected_bankedCacheWeight_step_le {α : Type} (parameter : PublicParameter)
    (computation : ProbComp α) (before : QueryCache HashSpec) (after : α → QueryCache HashSpec)
    (weight : α → HashInput → FewTimeView → ENNReal)
    (initial : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (completed : α → HashInput → Bool) (stopped : α → Bool) (charge : ENNReal)
    (hcache : ∀ result ∈ support computation, before ≤ after result)
    (hcompleted : ∀ result ∈ support computation, ∀ input, completed result input = true →
      1 ≤ cacheMessageEntryWeight parameter (weight result) (after result) input)
    (hold : ∀ input target, (∑' result, Pr[= result | computation] * weight result input target) ≤ initial input target)
    (hnew : (∑' result, Pr[= result | computation] *
      cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
        (after result)) ≤ charge) :
    (∑' result, Pr[= result | computation] *
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result)) ≤ bankedCacheWeight parameter initial bank false before + charge :=
  expected_bankedCacheWeight_step_le_of_split parameter computation before after weight initial bank completed stopped charge
    (fun result hr value => cacheMessageWeight_of_le parameter value before (after result) (hcache result hr))
    hcompleted hold hnew

end SphincsSecurity.Concrete
