import SphincsSecurity.Proof.Hypertree.StructuralMatchBound
import SphincsSecurity.Proof.Ots.EncodingMatchBound
import SphincsSecurity.Proof.Ots.OtsDistinctContactBound
import SphincsSecurity.Proof.Ots.OtsMarkerContactProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs canonicalGraphLabels Finset.univ

theorem referenceGraphContextGame_encoding {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : GraphContextResult Result => (result.1.parameter, result.2.2.1, canonicalGraphMessage result.2.1, result.2.2.2)) <$>
      referenceGraphContextGame observer inputs hencoding dummy adversary =
        referenceEncodingContextGame observer inputs hencoding dummy adversary := by
  simp only [referenceGraphContextGame, referenceGraphContextRest, referenceEncodingContextGame, referenceEncodingContextRest,
    map_bind, map_pure, bind_assoc, pure_bind]

theorem referenceGraphContextGame_contact_event (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary)
    (event : InstrumentedResult ContactResult → Prop) :
    Pr[fun result => event (result.1.parameter, result.2.2.1, result.2.2.2) |
      referenceGraphContextGame contactObserver inputs hencoding dummy adversary] =
        Pr[event | referenceContactGame inputs hencoding dummy adversary] := by
  rw [referenceContactGame, ← referenceGraphContextGame_erased contactObserver inputs hencoding dummy adversary, probEvent_map]
  rfl

def GraphPrimitiveEvent (dummy : OtsReferenceWords) (result : GraphContextResult ContactResult) : Prop :=
  let words := referenceFamilyWords result.2.2.1 dummy
  let trace := result.2.2.2.before * result.2.2.2.after
  OtsVerifierWitness.EncodingOutputMatch result.1.parameter words (canonicalGraphMessage result.2.1) result.2.2.1 trace ∨
    ReferenceStructuralMatch.Seen result.1 result.2.1 words trace ∨
      result.2.2.2.TwoEdge result.1.parameter words ∨ result.2.2.2.TwoContacts result.1.parameter words ∨
        result.2.2.2.MarkerContact result.1.parameter words

theorem graphPrimitiveEvent_of_outcome (key : SecretKey) (f : QueryImpl HashSpec Id) (selections : ReferenceFamily)
    (dummy : OtsReferenceWords) (result : ContactResult)
    (h : ReferencePrimitiveWitness.Outcome key f (referenceFamilyWords selections dummy)
      (canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)) selections result) :
    GraphPrimitiveEvent dummy (key, canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f, selections, result) := by
  rcases h with hencoding | hstructural | htwo | hdistinct | hmarker
  · exact Or.inl hencoding
  · exact Or.inr (Or.inl (ReferenceStructuralMatch.source_match key f _ _ hstructural))
  · exact Or.inr (Or.inr (Or.inl htwo))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hdistinct)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hmarker)))

noncomputable def primitivePrefixRate (q : Nat) : ENNReal :=
  let n : ENNReal := Fintype.card Digest
  let x := (q : ENNReal) / n
  prefixTwoEdgeRate q / (1 - x) + (4 * x) / ((1 - x)^2 * n) + (82 * x) / ((1 - x) * n)

noncomputable def primitiveEncodingRate (q : Nat) : ENNReal :=
  let n : ENNReal := Fintype.card Digest
  let x := (q : ENNReal) / n
  n⁻¹ + (3444 * x) / ((1 - x) * n)

theorem primitivePrefixRate_mono {q r : Nat} (h : q ≤ r) : primitivePrefixRate q ≤ primitivePrefixRate r := by
  dsimp only [primitivePrefixRate, prefixTwoEdgeRate]
  gcongr

theorem primitiveEncodingRate_mono {q r : Nat} (h : q ≤ r) : primitiveEncodingRate q ≤ primitiveEncodingRate r := by
  dsimp only [primitiveEncodingRate]
  gcongr

theorem primitive_rates_small (q : Nat) (hq : q ≤ 3 * 2 ^ 114) :
    primitivePrefixRate q ≤ (7 / 4 : ENNReal) / Fintype.card Digest ∧
      primitiveEncodingRate q ≤ (7 / 4 : ENNReal) / Fintype.card Digest := by
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have hn : (Fintype.card Digest : ENNReal) ≠ 0 := by positivity
  have hx : ((3 * 2 ^ 114 : Nat) : ENNReal) / Fintype.card Digest < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hn) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast (show 3 * 2 ^ 114 < Fintype.card Digest by rw [hcard]; norm_num)
  have hd : 1 - ((3 * 2 ^ 114 : Nat) : ENNReal) / Fintype.card Digest ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hx)
  have hs := ENNReal.toReal_sub_of_le hx.le (show (1 : ENNReal) ≠ ⊤ by finiteness)
  constructor
  · apply (primitivePrefixRate_mono hq).trans
    dsimp only [primitivePrefixRate, prefixTwoEdgeRate]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, hs,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, hcard]
  · apply (primitiveEncodingRate_mono hq).trans
    dsimp only [primitiveEncodingRate]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, hs,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num [hcard]

theorem referenceGraphContextGame_primitive_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      primitivePrefixRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) +
      primitiveEncodingRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.encodingCalls : ENNReal)) +
      (Fintype.card Digest : ENNReal)⁻¹ * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.otherCalls dummy : ENNReal)) := by
  let law := referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  have he := referenceEncodingContextGame_match_le_encodingCost dummy adversary
  rw [← referenceGraphContextGame_encoding contactObserver _ _ dummy adversary, probEvent_map] at he
  have hs := referenceGraphContextGame_match_le_otherCost dummy adversary
  have ht := referenceContactGame_twoEdge_le dummy adversary q hbound hsmall
  have hd := referenceContactGame_distinct_le dummy adversary q hbound hsmall
  have hm := referenceContactGame_markerContact_le dummy adversary q hbound hsmall
  rw [← referenceGraphContextGame_contact_event _ _ dummy adversary] at ht hd hm
  have h := (probEvent_or_le law _ _).trans (add_le_add he
    ((probEvent_or_le law _ _).trans (add_le_add hs
      ((probEvent_or_le law _ _).trans (add_le_add ht
        ((probEvent_or_le law _ _).trans (add_le_add hd hm)))))))
  change Pr[GraphPrimitiveEvent dummy | law] ≤ _ at h
  refine h.trans_eq ?_
  simp only [primitivePrefixRate, primitiveEncodingRate, div_eq_mul_inv]
  ring

theorem referenceGraphContextGame_primitive_joint_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest)
    (rate : ENNReal) (hp : primitivePrefixRate q ≤ rate) (he : primitiveEncodingRate q ≤ rate)
    (ho : (Fintype.card Digest : ENNReal)⁻¹ ≤ rate) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      rate * (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.messageCalls : ENNReal)) ≤ rate * q := by
  let law := referenceRecordedGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  have h := add_le_add (referenceGraphContextGame_primitive_le dummy adversary q hbound hsmall)
    (le_refl (rate * ∑' result, Pr[= result | law] * (result.messageCalls : ENNReal)))
  refine h.trans ?_
  calc
    _ ≤ rate * (∑' result, Pr[= result | law] * (result.prefixCalls dummy : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.encodingCalls : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.otherCalls dummy : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.messageCalls : ENNReal)) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul' hp le_rfl) (mul_le_mul' he le_rfl)) (mul_le_mul' ho le_rfl)) le_rfl
    _ = rate * ∑' result, Pr[= result | law] * ((result.prefixCalls dummy + result.remainingCalls dummy : Nat) : ENNReal) := by
      simp only [ReferenceRecordedResult.remainingCalls, Nat.cast_add, mul_add, ENNReal.tsum_add, add_assoc]
    _ ≤ rate * q := by
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∑' result, Pr[= result | law] * (q : ENNReal) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support law
          · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (referenceRecordedGame_joint_budget dummy adversary q hbound result hr))
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ ≤ q := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem referenceGraphContextGame_primitive_small_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q ≤ 3 * 2 ^ 114) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      ((7 / 4 : ENNReal) / Fintype.card Digest) *
        (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.messageCalls : ENNReal)) ≤
        (7 / 4 : ENNReal) * ((q : ENNReal) / Fintype.card Digest) := by
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have hq : q < Fintype.card Digest := hsmall.trans_lt (by rw [hcard]; norm_num)
  have hr := primitive_rates_small q hsmall
  have ho : (Fintype.card Digest : ENNReal)⁻¹ ≤ (7 / 4 : ENNReal) / Fintype.card Digest := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div, hcard]
  simpa only [div_eq_mul_inv, mul_right_comm, mul_assoc] using
    referenceGraphContextGame_primitive_joint_budget dummy adversary q hbound hq _ hr.1 hr.2 ho

end SphincsSecurity.Concrete
