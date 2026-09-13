import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.RawSigningMomentBound
import SphincsSecurity.Proof.Fts.MessageDeficitConcentration

/-! ## InitialTargetShape -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem TargetShapeValid.empty (remaining : Finset FtsTree) : TargetShapeValid ∅ remaining := by
  constructor <;> intro group hgroup <;> exact (Finset.notMem_empty group hgroup).elim

end SphincsSecurity.Concrete

/-! ## NearUniformRawStep -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def nearUniformDigestReuseWeight : ENNReal :=
  (1025 / 1024 : ENNReal) * ((2 ^ 118 : Nat) : ENNReal)⁻¹

theorem exactDigestReuseWeight_le_near_uniform_of_clean_cache (key : SecretKey) (cache : QueryCache HashSpec)
    (cap : Nat) (hcap : cap ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ cap)
    (hclean : ¬ MessageDeficitExceptional key cache) (message : Message) :
    exactDigestReuseWeight key message cache ≤ nearUniformDigestReuseWeight :=
  exactDigestReuseWeight_le_near_uniform_of_deficit key message cache cap hcap hcache
    (le_of_not_gt (fun h => hclean ⟨message, h⟩))

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open ENNReal

theorem reuseRawEnvelope_le_binomialAverage (key : SecretKey) (reuse rate : ENNReal)
    (hrate : rate ≤ 1) (queries signatures bound : Nat) (state : CoverLogState)
    (remaining : Finset FtsTree) (hdegree : remaining.card ≤ bound)
    (hprob : ∀ index : Index,
      (Fintype.card Index : ENNReal)⁻¹ + reuse *
        (cachedIndexMultiplicity key.parameter state.1 index +
          (queries : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + bound + signatures) ≤ rate) :
    reuseRawEnvelope key reuse queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage rate signatures (fun count =>
        (((signingSlotsAtIndex (observedOptionalSigningViews
          (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal) + count) ^
          remaining.card) := by
  apply (reuseRawEnvelope_query_shift_le key reuse queries signatures bound state ∅ remaining
    (TargetShapeValid.empty _) (by simpa only [Finset.card_empty, Nat.zero_add] using hdegree)).trans
  apply Finset.sum_le_sum
  intro index _
  exact targetIndexSigning_iterate_power_le_binomialAverage hrate signatures (hprob index) _ remaining.card

noncomputable def targetProposalOverhead : ENNReal := 1537 / 1024

noncomputable def targetProposalIndexRate : ENNReal :=
  targetProposalOverhead * (Fintype.card Index : ENNReal)⁻¹

theorem targetProposalIndexRate_le_one : targetProposalIndexRate ≤ 1 := by
  unfold targetProposalIndexRate targetProposalOverhead
  norm_num only [Index, totalHeight, Fintype.card_fin]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, Index, totalHeight]

theorem targetProposalRate_of_cache_bound (cache : ENNReal) (spent queries signatures bound : Nat)
    (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit) (hbound : bound ≤ 14)
    (hcache : cache ≤ (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal)) :
    (Fintype.card Index : ENNReal)⁻¹ + nearUniformDigestReuseWeight *
      (cache + (queries : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + bound + signatures) ≤
        targetProposalIndexRate := by
  have hsize : cache + (queries : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + bound + signatures ≤
      ((2 ^ 127 : Nat) : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ +
        ((2 ^ 80 : Nat) : ENNReal) + 14 + signatureLimit := by
    calc
      _ ≤ (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal) +
          (queries : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + bound + signatures := by
        gcongr
      _ = ((spent + queries : Nat) : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ +
          ((2 ^ 80 : Nat) : ENNReal) + bound + signatures := by
        push_cast
        ring
      _ ≤ _ := by
        exact add_le_add
          (add_le_add (add_le_add (mul_le_mul' (Nat.cast_le.mpr hqueries) le_rfl) le_rfl)
            (by exact_mod_cast hbound)) (Nat.cast_le.mpr hsignatures)
  apply (add_le_add le_rfl (mul_le_mul' le_rfl hsize)).trans
  unfold nearUniformDigestReuseWeight targetProposalIndexRate targetProposalOverhead
  norm_num only [Index, totalHeight, Fintype.card_fin, signatureLimit]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv]
  norm_num

theorem reuseRawEnvelope_le_proposalIndexAverage (key : SecretKey)
    (spent queries signatures bound : Nat) (state : CoverLogState) (remaining : Finset FtsTree)
    (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit)
    (hdegree : remaining.card ≤ bound) (hbound : bound ≤ 14)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal)) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage targetProposalIndexRate signatures (fun count =>
        (((signingSlotsAtIndex (observedOptionalSigningViews
          (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal) + count) ^
          remaining.card) :=
  reuseRawEnvelope_le_binomialAverage key nearUniformDigestReuseWeight targetProposalIndexRate
    targetProposalIndexRate_le_one queries signatures bound state remaining hdegree
    (fun index => targetProposalRate_of_cache_bound _ spent queries signatures bound hqueries hsignatures hbound (hcache index))

theorem proposalIndexAverage_le_uniformAverage (signatures proposals degree : Nat)
    {signings consumed : ENNReal} (hcounts : signings ≤ consumed)
    (hroom : targetProposalOverhead * signatures + degree ≤ ((proposals + 1 : Nat) : ENNReal)) :
    binomialAverage targetProposalIndexRate signatures (fun count => (signings + count) ^ degree) ≤
      binomialAverage (Fintype.card Index : ENNReal)⁻¹ proposals (fun count => (consumed + count) ^ degree) := by
  apply binomialAverage_shifted_power_le_of_room targetProposalIndexRate_le_one
    (by norm_num [Index, totalHeight]) hcounts signatures proposals degree (mass := targetProposalOverhead * signatures)
  · unfold targetProposalIndexRate
    exact le_of_eq (by ring)
  · exact hroom

theorem reuseRawEnvelope_le_uniformProposalAverage (key : SecretKey)
    (spent queries signatures bound proposals : Nat) (state : CoverLogState) (remaining : Finset FtsTree)
    (consumed : Index → Nat) (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit)
    (hdegree : remaining.card ≤ bound) (hbound : bound ≤ 14)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal))
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card ≤ consumed index)
    (hroom : targetProposalOverhead * signatures + remaining.card ≤ ((proposals + 1 : Nat) : ENNReal)) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage (Fintype.card Index : ENNReal)⁻¹ proposals
        (fun count => ((consumed index : ENNReal) + count) ^ remaining.card) := by
  apply (reuseRawEnvelope_le_proposalIndexAverage key spent queries signatures bound state remaining
    hqueries hsignatures hdegree hbound hcache).trans
  apply Finset.sum_le_sum
  intro index _
  exact proposalIndexAverage_le_uniformAverage signatures proposals remaining.card
    (Nat.cast_le.mpr (hcounts index)) hroom

end SphincsSecurity.Concrete
