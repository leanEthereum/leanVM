import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.RawProposalMomentBound
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

noncomputable def sampleUniformProposalWord (α : Type) [SampleableType α] : Nat → ProbComp (List α)
  | 0 => pure []
  | steps + 1 => do
      let next ← $ᵗ α
      let rest ← sampleUniformProposalWord α steps
      pure (next :: rest)

theorem expected_uniformSample_choice {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (index : α) (hit miss : ENNReal) :
    (∑' next : α, Pr[= next | ($ᵗ α : ProbComp α)] * (if next = index then hit else miss)) =
      (1 - (Fintype.card α : ENNReal)⁻¹) * miss + (Fintype.card α : ENNReal)⁻¹ * hit := by
  classical
  have hmiss : Pr[fun next => next ≠ index | ($ᵗ α : ProbComp α)] =
      1 - (Fintype.card α : ENNReal)⁻¹ := by
    apply ENNReal.eq_sub_of_add_eq' (by finiteness)
    have h := probEvent_compl ($ᵗ α : ProbComp α) (fun next => next = index)
    simpa only [probEvent_eq_eq_probOutput, probOutput_uniformSample, probFailure_uniformSample, tsub_zero,
      add_comm] using h
  calc
    _ = (∑' next : α, (if next = index then Pr[= next | ($ᵗ α : ProbComp α)] else 0)) * hit +
        (∑' next : α, (if next ≠ index then Pr[= next | ($ᵗ α : ProbComp α)] else 0)) * miss := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      apply tsum_congr
      intro next
      by_cases h : next = index <;> simp [h]
    _ = _ := by
      rw [← probEvent_eq_tsum_ite, ← probEvent_eq_tsum_ite, probEvent_eq_eq_probOutput,
        probOutput_uniformSample, hmiss, add_comm]

theorem expected_uniformProposalWord_count {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (index : α) (steps : Nat) (f : Nat → ENNReal) :
    (∑' word : List α, Pr[= word | sampleUniformProposalWord α steps] * f (word.count index)) =
      binomialAverage (Fintype.card α : ENNReal)⁻¹ steps f := by
  induction steps generalizing f with
  | zero => simp only [sampleUniformProposalWord, tsum_probOutput_pure_mul, List.count_nil, binomialAverage_zero]
  | succ steps ih =>
      rw [sampleUniformProposalWord, tsum_probOutput_bind_mul]
      simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      have hinner (next : α) :
          (∑' word : List α, Pr[= word | sampleUniformProposalWord α steps] * f ((next :: word).count index)) =
            if next = index then binomialAverage (Fintype.card α : ENNReal)⁻¹ steps (fun count => f (count + 1))
              else binomialAverage (Fintype.card α : ENNReal)⁻¹ steps f := by
        by_cases h : next = index
        · subst next
          simpa only [List.count_cons_self, ↓reduceIte] using ih (fun count => f (count + 1))
        · simpa only [List.count_cons_of_ne h, if_neg h] using ih f
      simp_rw [hinner]
      exact expected_uniformSample_choice index _ _

theorem expected_uniformProposalWord_power_sum {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (steps degree : Nat) (consumed : α → Nat) :
    (∑' word : List α, Pr[= word | sampleUniformProposalWord α steps] *
      ∑ index : α, ((consumed index : ENNReal) + word.count index) ^ degree) =
      ∑ index : α, binomialAverage (Fintype.card α : ENNReal)⁻¹ steps
        (fun count => ((consumed index : ENNReal) + count) ^ degree) := by
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro index _
  exact expected_uniformProposalWord_count index steps (fun count => ((consumed index : ENNReal) + count) ^ degree)

theorem reuseRawEnvelope_le_expected_uniformProposalWord (key : SecretKey)
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
      ∑' word : List Index, Pr[= word | sampleUniformProposalWord Index proposals] *
        ∑ index : Index, ((consumed index : ENNReal) + word.count index) ^ remaining.card := by
  rw [expected_uniformProposalWord_power_sum]
  exact reuseRawEnvelope_le_uniformProposalAverage key spent queries signatures bound proposals state remaining
    consumed hqueries hsignatures hdegree hbound hcache hcounts hroom

theorem targetProposalRoom_of_prefix (completed signatures total used degree slack : Nat)
    (hsignatures : completed + signatures ≤ signatureLimit) (hdegree : degree ≤ 14)
    (htotal : targetProposalOverhead * signatureLimit + slack + 13 ≤ (total : ENNReal))
    (hused : (used : ENNReal) ≤ targetProposalOverhead * completed + slack) :
    targetProposalOverhead * signatures + degree ≤ ((total - used + 1 : Nat) : ENNReal) := by
  have hcompleted : completed ≤ signatureLimit := (Nat.le_add_right completed signatures).trans hsignatures
  have husedTotal : used ≤ total := by
    apply (Nat.cast_le (α := ENNReal)).mp
    exact hused.trans ((add_le_add (mul_le_mul' le_rfl (Nat.cast_le.mpr hcompleted)) le_rfl).trans
      ((le_self_add : targetProposalOverhead * signatureLimit + slack ≤
        targetProposalOverhead * signatureLimit + slack + 13).trans htotal))
  have hcapacity : (used : ENNReal) + (targetProposalOverhead * signatures + degree) ≤ (total : ENNReal) + 1 := by
    calc
      _ ≤ targetProposalOverhead * completed + slack + (targetProposalOverhead * signatures + degree) :=
        add_le_add hused le_rfl
      _ = targetProposalOverhead * ((completed + signatures : Nat) : ENNReal) + slack + degree := by
        push_cast
        ring
      _ ≤ targetProposalOverhead * signatureLimit + slack + 14 :=
        add_le_add (add_le_add (mul_le_mul' le_rfl (Nat.cast_le.mpr hsignatures)) le_rfl)
          (by exact_mod_cast hdegree)
      _ = (targetProposalOverhead * signatureLimit + slack + 13) + 1 := by ring
      _ ≤ _ := add_le_add htotal le_rfl
  have hsum : ((total - used + 1 : Nat) : ENNReal) + (used : ENNReal) = (total : ENNReal) + 1 := by
    exact_mod_cast (show total - used + 1 + used = total + 1 by omega)
  apply ENNReal.le_of_add_le_add_right (a := (used : ENNReal)) (by finiteness)
  calc
    _ = (used : ENNReal) + (targetProposalOverhead * signatures + degree) := add_comm _ _
    _ ≤ (total : ENNReal) + 1 := hcapacity
    _ = _ := hsum.symm

theorem targetProposalPoolMinimum_eq :
    targetProposalOverhead * signatureLimit + 131072 + 13 = (25313293 : ENNReal) := by
  unfold targetProposalOverhead
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div]
  norm_num [signatureLimit]

theorem reuseRawEnvelope_le_expected_terminalProposalWord (key : SecretKey)
    (spent queries completed total : Nat) (state : CoverLogState) (remaining : Finset FtsTree)
    (consumedWord : List Index) (hqueries : spent + queries ≤ 2 ^ 127) (hcompleted : completed ≤ signatureLimit)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal))
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card ≤ consumedWord.count index)
    (htotal : 25313293 ≤ total)
    (hprefix : (consumedWord.length : ENNReal) ≤ targetProposalOverhead * completed + 131072) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries (signatureLimit - completed) state ∅ remaining ≤
      ∑' word : List Index, Pr[= word | sampleUniformProposalWord Index (total - consumedWord.length)] *
        ∑ index : Index, ((consumedWord ++ word).count index : ENNReal) ^ remaining.card := by
  have hdegree : remaining.card ≤ 14 := by
    exact (Finset.card_le_univ remaining).trans_eq (by decide : Fintype.card FtsTree = 14)
  have hroom : targetProposalOverhead * (signatureLimit - completed : Nat) + remaining.card ≤
      ((total - consumedWord.length + 1 : Nat) : ENNReal) :=
    targetProposalRoom_of_prefix completed (signatureLimit - completed) total consumedWord.length remaining.card 131072
      (by omega) hdegree
      (by norm_num only [Nat.cast_ofNat]; rw [targetProposalPoolMinimum_eq]; exact_mod_cast htotal) hprefix
  have h := reuseRawEnvelope_le_expected_uniformProposalWord key spent queries (signatureLimit - completed) 14
    (total - consumedWord.length) state remaining (fun index => consumedWord.count index) hqueries (Nat.sub_le _ _)
    hdegree le_rfl hcache hcounts hroom
  simpa only [List.count_append, Nat.cast_add] using h

end SphincsSecurity.Concrete
