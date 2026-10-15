import Sphincs.Code
import Sphincs.Uniform

/-! Candidate WOTS+C encoding classification and exact small-neighborhood bounds.
Adapted from leanVM b7a107256; the candidate uses 64 two-bit digits without padding. -/

namespace Sphincs.Security.EncodingCode

open TargetSum OracleComp OracleSpec ENNReal
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def UnitNeighborAt (reference candidate : Encoding) (lowered : ChainIndex) : Prop :=
  Valid reference ∧ Valid candidate ∧ (candidate lowered).val + 1 = (reference lowered).val ∧
    ∀ index, index ≠ lowered → (reference index).val ≤ (candidate index).val

theorem UnitNeighborAt.ne {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) : candidate ≠ reference := by
  intro he
  have hd := h.2.2.1
  rw [he] at hd
  omega

noncomputable def unitNeighbors (reference : Encoding) (lowered : ChainIndex) : Finset Encoding :=
  Finset.univ.filter (fun candidate => UnitNeighborAt reference candidate lowered)

theorem mem_unitNeighbors {reference candidate : Encoding} {lowered : ChainIndex} :
    candidate ∈ unitNeighbors reference lowered ↔ UnitNeighborAt reference candidate lowered := by
  simp only [unitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def allUnitNeighbors (reference : Encoding) : Finset Encoding :=
  Finset.univ.biUnion (unitNeighbors reference)

theorem mem_allUnitNeighbors {reference candidate : Encoding} :
    candidate ∈ allUnitNeighbors reference ↔ ∃ lowered, UnitNeighborAt reference candidate lowered := by
  simp only [allUnitNeighbors, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_unitNeighbors]

/-- The unit neighbors of a word at one lowered chain. -/
def unitNeighborBound : Nat := numChains - 1

/-- The unit neighbors of a word at any chain. -/
def neighborBound : Nat := numChains * (numChains - 1)

private theorem two_terms_le_sum (f : ChainIndex → Nat) {left right : ChainIndex} (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (Finset.subset_univ ({left, right} : Finset ChainIndex))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h

private theorem single_of_sum_one (f : ChainIndex → Nat) (hsum : (∑ index, f index) = 1) :
    ∃ index, f index = 1 ∧ ∀ other, other ≠ index → f other = 0 := by
  have hnonzero : ∃ index, f index ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ index, f index) = 0 := Finset.sum_eq_zero fun index _ => hnone index
    omega
  obtain ⟨index, hi⟩ := hnonzero
  have hle : f index ≤ ∑ other, f other := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hone : f index = 1 := by omega
  refine ⟨index, hone, fun other hne => ?_⟩
  have hpair := two_terms_le_sum f hne
  omega

/-- For the target-sum code a unit neighbor moves exactly one step from the lowered chain to one other chain. -/
private theorem UnitNeighborAt.raised {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) :
    ∃ raised, raised ≠ lowered ∧ (reference raised).val + 1 = (candidate raised).val ∧
      ∀ index, index ≠ lowered → index ≠ raised → candidate index = reference index := by
  obtain ⟨hreference, hcandidate, hlow, hup⟩ := h
  have hpoint : ∀ index : ChainIndex,
      ((reference index).val - (candidate index).val) + (candidate index).val =
        ((candidate index).val - (reference index).val) + (reference index).val := fun index => by omega
  have hsum := congrArg (fun f : ChainIndex → Nat => ∑ index, f index) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  have hback : ∑ index, ((reference index).val - (candidate index).val) = 1 := by
    rw [Finset.sum_eq_single lowered]
    · omega
    · intro index _ hne
      have := hup index hne
      omega
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  change _ + TargetSum.sum candidate = _ + TargetSum.sum reference at hsum
  have hsums : TargetSum.sum candidate = TargetSum.sum reference := hcandidate.trans hreference.symm
  have hforward : ∑ index, ((candidate index).val - (reference index).val) = 1 := by omega
  obtain ⟨raised, hraise, hothers⟩ := single_of_sum_one _ hforward
  refine ⟨raised, fun he => ?_, by omega, fun index hl hr => ?_⟩
  · subst raised
    omega
  · have hdown := hothers index hr
    have hle := hup index hl
    apply Fin.ext
    omega

theorem unitNeighbors_card_le (reference : Encoding) (lowered : ChainIndex) :
    (unitNeighbors reference lowered).card ≤ unitNeighborBound := by
  let chooseRaised : {candidate // UnitNeighborAt reference candidate lowered} → {raised : ChainIndex // raised ≠ lowered} :=
    fun candidate => ⟨candidate.property.raised.choose, candidate.property.raised.choose_spec.1⟩
  have hinj : Function.Injective chooseRaised := by
    intro left right he
    apply Subtype.ext
    have he' : left.property.raised.choose = right.property.raised.choose := congrArg Subtype.val he
    obtain ⟨_, hup, hrest⟩ := left.property.raised.choose_spec
    obtain ⟨_, hup', hrest'⟩ := right.property.raised.choose_spec
    rw [he'] at hup hrest
    funext index
    by_cases hl : index = lowered
    · subst index
      apply Fin.ext
      have := left.property.2.2.1
      have := right.property.2.2.1
      omega
    · by_cases hr : index = right.property.raised.choose
      · subst index
        apply Fin.ext
        omega
      · exact (hrest index hl hr).trans (hrest' index hl hr).symm
  have hcard := Fintype.card_le_of_injective chooseRaised hinj
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  have hr : (Finset.univ.filter fun raised : ChainIndex => raised ≠ lowered) = Finset.univ.erase lowered := by
    ext raised
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [hr, Finset.card_erase_of_mem (Finset.mem_univ lowered), Finset.card_univ, Fintype.card_fin] at hcard
  rw [unitNeighborBound]
  simpa only [unitNeighbors] using hcard

theorem allUnitNeighbors_card_le (reference : Encoding) : (allUnitNeighbors reference).card ≤ neighborBound := by
  calc
    _ ≤ ∑ lowered : ChainIndex, (unitNeighbors reference lowered).card := Finset.card_biUnion_le
    _ ≤ ∑ _lowered : ChainIndex, unitNeighborBound :=
      Finset.sum_le_sum fun lowered _ => unitNeighbors_card_le reference lowered
    _ = neighborBound := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, neighborBound,
        unitNeighborBound]

/-! ### Values, for the closing arithmetic only -/

theorem unitNeighborBound_eq : unitNeighborBound = 63 := by
  rw [unitNeighborBound]
  rfl

theorem neighborBound_eq : neighborBound = 4032 := by
  rw [neighborBound]
  rfl

/-- The chain steps an adversary must invert to turn `reference` into `candidate`. -/
def backwardWeight (reference candidate : Encoding) : Nat :=
  ∑ index : ChainIndex, ((reference index).val - (candidate index).val)

theorem unitNeighbor_of_backwardWeight_one {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate) (hweight : backwardWeight reference candidate = 1) :
    ∃ lowered, UnitNeighborAt reference candidate lowered := by
  obtain ⟨lowered, hlower, hothers⟩ := single_of_sum_one (fun index => (reference index).val - (candidate index).val) hweight
  refine ⟨lowered, hreference, hcandidate, ?_, fun index hne => ?_⟩
  · omega
  · have hdown := hothers index hne
    omega

theorem eq_of_backwardWeight_zero {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate) (hweight : backwardWeight reference candidate = 0) :
    reference = candidate := by
  apply Completeness.encoding_antichain hreference hcandidate
  intro index
  have hle : (reference index).val - (candidate index).val ≤ backwardWeight reference candidate := by
    unfold backwardWeight
    exact Finset.single_le_sum (f := fun index : ChainIndex => (reference index).val - (candidate index).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  omega

theorem backwardWeight_two_witness {reference candidate : Encoding} (hweight : 2 ≤ backwardWeight reference candidate) :
    (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧ (candidate right).val < (reference right).val := by
  by_cases hlarge : ∃ index, (candidate index).val + 2 ≤ (reference index).val
  · exact Or.inl hlarge
  have hnonzero : ∃ index, (candidate index).val < (reference index).val := by
    by_contra hnone
    push Not at hnone
    have hz : backwardWeight reference candidate = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exact Nat.sub_eq_zero_of_le (hnone index)
    omega
  obtain ⟨left, hl⟩ := hnonzero
  by_cases hother : ∃ right, left ≠ right ∧ (candidate right).val < (reference right).val
  · obtain ⟨right, hne, hr⟩ := hother
    exact Or.inr ⟨left, right, hne, hl, hr⟩
  · have hzero : ∀ index, index ≠ left → (reference index).val - (candidate index).val = 0 := by
      intro index hne
      have hn : ¬(candidate index).val < (reference index).val := fun hi => hother ⟨index, hne.symm, hi⟩
      omega
    have hsum : backwardWeight reference candidate = (reference left).val - (candidate left).val := by
      apply Finset.sum_eq_single left
      · intro index _ hne
        exact hzero index hne
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    have hn := not_exists.mp hlarge left
    omega

/-- Two valid words are equal, unit neighbors, or apart by two backward steps on one chain or one step on each of two chains. -/
theorem valid_encoding_classification {reference candidate : Encoding} (hreference : Valid reference) (hcandidate : Valid candidate) :
    reference = candidate ∨ (∃ lowered, UnitNeighborAt reference candidate lowered) ∨
      (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧ (candidate right).val < (reference right).val := by
  by_cases hzero : backwardWeight reference candidate = 0
  · exact Or.inl (eq_of_backwardWeight_zero hreference hcandidate hzero)
  by_cases hone : backwardWeight reference candidate = 1
  · exact Or.inr (Or.inl (unitNeighbor_of_backwardWeight_one hreference hcandidate hone))
  exact Or.inr (Or.inr (backwardWeight_two_witness (by omega)))

/-- All 128 digest bits occur in the candidate's 64 two-bit digits. -/
theorem digestEncoding_injective : Function.Injective digestEncoding := by
  intro left right hencoding
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have hbound : bit < 128 := hbit
  let index : ChainIndex := ⟨bit / 2, by change bit / 2 < 64; omega⟩
  have hdigit : left.extractLsb' (digitOffset index) 2 = right.extractLsb' (digitOffset index) 2 := by
    apply BitVec.eq_of_toNat_eq
    exact congrArg Fin.val (congrFun hencoding index)
  have hbits := congrArg (fun digit : BitVec 2 => digit.getLsbD (bit % 2)) hdigit
  have hmod : bit % 2 < 2 := by omega
  have hoffset : digitOffset index + bit % 2 = bit := by
    change 2 * (bit / 2) + bit % 2 = bit
    omega
  simpa only [BitVec.getLsbD_extractLsb', hmod, decide_true, Bool.true_and,
    hoffset] using hbits

theorem decode_valid {digest : Digest} {word : Encoding}
    (hdecode : decodeDigest digest = some word) : Valid word := by
  unfold decodeDigest at hdecode
  split at hdecode
  · rename_i hvalid
    exact Option.some.inj hdecode ▸ hvalid
  · simp at hdecode

/-- A valid codeword has a unique digest preimage; the candidate has no padding bits. -/
theorem decode_some_injective {left right : Digest} {word : Encoding}
    (hleft : decodeDigest left = some word) (hright : decodeDigest right = some word) :
    left = right := by
  unfold decodeDigest at hleft hright
  split at hleft <;> split at hright
  · exact digestEncoding_injective ((Option.some.inj hleft).trans (Option.some.inj hright).symm)
  all_goals simp at hleft hright

/-- Digests decoding into a prescribed finite set of words. -/
noncomputable def decodingDigests (words : Finset Encoding) : Finset Digest :=
  Finset.univ.filter fun digest => ∃ word ∈ words, decodeDigest digest = some word

theorem mem_decodingDigests {words : Finset Encoding} {digest : Digest} :
    digest ∈ decodingDigests words ↔ ∃ word ∈ words, decodeDigest digest = some word := by
  simp only [decodingDigests, Finset.mem_filter, Finset.mem_univ, true_and]

theorem decodingDigests_card_le (words : Finset Encoding) :
    (decodingDigests words).card ≤ words.card := by
  apply Finset.card_le_card_of_injOn (fun digest => (decodeDigest digest).getD (fun _ => ⟨0, by decide⟩))
  · intro digest hd
    obtain ⟨word, hw, hdecode⟩ := mem_decodingDigests.mp hd
    simpa only [hdecode, Option.getD_some, Finset.mem_coe] using hw
  · intro left hl right hr he
    obtain ⟨leftWord, _, hleft⟩ := mem_decodingDigests.mp hl
    obtain ⟨rightWord, _, hright⟩ := mem_decodingDigests.mp hr
    simp only [hleft, hright, Option.getD_some] at he
    exact decode_some_injective hleft (by rw [he]; exact hright)

end Sphincs.Security.EncodingCode
