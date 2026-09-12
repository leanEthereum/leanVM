import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.BinomialMoments
import SphincsSecurity.Proof.Fts.ReuseRawEnvelope
import SphincsSecurity.Proof.Fts.TargetIndexEnvelope
import SphincsSecurity.Proof.Fts.TargetShapeExpectation
namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def indexPowerVector (cache signings : ENNReal) : TargetIndexVector :=
  fun power degree => cache ^ power * signings ^ degree

def TargetIndexDegreeLE (bound : Nat) (first second : TargetIndexVector) : Prop :=
  ∀ power degree, power + degree ≤ bound → first power degree ≤ second power degree

theorem targetIndexCacheLower_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexCacheLower first) (targetIndexCacheLower second) := by
  intro power degree hdegree
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h lower degree (by have := Finset.mem_range.mp hlower; omega)

theorem targetIndexTreeLower_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexTreeLower first) (targetIndexTreeLower second) := by
  intro power degree hdegree
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h power lower (by have := Finset.mem_range.mp hlower; omega)

theorem targetIndexReuseStep_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexReuseStep first) (targetIndexReuseStep second) := by
  intro power degree hdegree
  unfold targetIndexReuseStep targetIndexTreeLower
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h (power + 1) lower (by have := Finset.mem_range.mp hlower; omega)

theorem targetIndexSigning_degree_mono (uniform reuse : ENNReal)
    {bound : Nat} {first second : TargetIndexVector} (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexSigning uniform reuse first) (targetIndexSigning uniform reuse second) := by
  intro power degree hdegree
  exact add_le_add
    (add_le_add (h power degree hdegree) (mul_le_mul' le_rfl
      (add_le_add (add_le_add (targetIndexCacheLower_degree_mono h power degree hdegree)
        (targetIndexTreeLower_degree_mono h power degree hdegree))
        (targetIndexCacheLower_degree_mono (targetIndexTreeLower_degree_mono h) power degree hdegree))))
    (mul_le_mul' le_rfl (targetIndexReuseStep_degree_mono h power degree hdegree))

theorem targetIndexSigning_iterate_degree_mono (uniform reuse : ENNReal) (signings : Nat)
    {bound : Nat} {first second : TargetIndexVector} (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound ((targetIndexSigning uniform reuse)^[signings] first)
      ((targetIndexSigning uniform reuse)^[signings] second) := by
  induction signings with
  | zero => exact h
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact targetIndexSigning_degree_mono uniform reuse ih

theorem ennreal_add_one_pow (value : ENNReal) (degree : Nat) :
    (value + 1) ^ degree = value ^ degree +
      ∑ lower ∈ Finset.range degree, (degree.choose lower : ENNReal) * value ^ lower := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
  rw [add_comm]
  apply congrArg (value ^ degree + ·)
  apply Finset.sum_congr rfl
  intro lower _
  exact mul_comm _ _

theorem indexPowerVector_cache_succ (cache signings : ENNReal) (power degree : Nat) :
    indexPowerVector (cache + 1) signings power degree =
      indexPowerVector cache signings power degree + targetIndexCacheLower (indexPowerVector cache signings) power degree := by
  simp only [indexPowerVector, ennreal_add_one_pow, add_mul, Finset.sum_mul, targetIndexCacheLower]
  congr 1
  apply Finset.sum_congr rfl
  intro lower _
  ring

theorem targetIndexQuery_power {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (power degree : Nat) :
    targetIndexQuery rate (indexPowerVector cache signings) power degree =
      (1 - rate) * indexPowerVector cache signings power degree +
        rate * indexPowerVector (cache + 1) signings power degree := by
  rw [indexPowerVector_cache_succ, bernoulli_mix_increment hrate]
  rfl

theorem targetIndexQuery_binomialAverage (arrival rate : ENNReal) (steps : Nat)
    (moments : Nat → TargetIndexVector) (power degree : Nat) :
    targetIndexQuery arrival (fun p d => binomialAverage rate steps (fun count => moments count p d)) power degree =
      binomialAverage rate steps (fun count => targetIndexQuery arrival (moments count) power degree) := by
  simp only [targetIndexQuery, targetIndexCacheLower, binomialAverage_add,
    binomialAverage_mul_left, binomialAverage_sum]

theorem targetIndexQuery_iterate_power {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (queries power degree : Nat) :
    (targetIndexQuery rate)^[queries] (indexPowerVector cache signings) power degree =
      binomialAverage rate queries (fun count => indexPowerVector (cache + count) signings power degree) := by
  induction queries generalizing power degree with
  | zero => simp [binomialAverage_zero]
  | succ queries ih =>
      have hfun : (targetIndexQuery rate)^[queries] (indexPowerVector cache signings) =
          fun p d => binomialAverage rate queries (fun count => indexPowerVector (cache + count) signings p d) := by
        funext p d
        exact ih p d
      rw [Function.iterate_succ_apply', hfun, targetIndexQuery_binomialAverage]
      simp_rw [targetIndexQuery_power hrate]
      rw [binomialAverage_add, binomialAverage_mul_left, binomialAverage_mul_left, binomialAverage_succ]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]

theorem targetIndexQuery_iterate_power_le {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (queries bound : Nat) :
    TargetIndexDegreeLE bound ((targetIndexQuery rate)^[queries] (indexPowerVector cache signings))
      (indexPowerVector (cache + queries * rate + bound) signings) := by
  intro power degree hdegree
  rw [targetIndexQuery_iterate_power hrate]
  simp only [indexPowerVector, binomialAverage_mul_right]
  apply mul_le_mul' _ le_rfl
  exact (binomialAverage_shifted_power_le hrate cache queries power).trans
    (pow_le_pow_left' (add_le_add le_rfl (Nat.cast_le.mpr (by omega : power ≤ bound))) power)

theorem targetIndexEnvelope_power_query_shift_le {rate : ENNReal} (hrate : rate ≤ 1)
    (uniform reuse cache signings : ENNReal) (queries signatures bound power degree : Nat)
    (hdegree : power + degree ≤ bound) :
    targetIndexEnvelope uniform reuse rate queries signatures (indexPowerVector cache signings) power degree ≤
      (targetIndexSigning uniform reuse)^[signatures]
        (indexPowerVector (cache + queries * rate + bound) signings) power degree :=
  targetIndexSigning_iterate_degree_mono uniform reuse signatures
    (targetIndexQuery_iterate_power_le hrate cache signings queries bound) power degree hdegree

theorem targetShapeEnvelope_sum_indexPower {α : Type} [Fintype α]
    (uniform reuse arrival : ENNReal) (queries signatures : Nat) (cache signings : α → ENNReal)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signatures
      (fun G R => ∑ i, indexPowerVector (cache i) (signings i) G.card R.card) groups remaining =
      ∑ i, targetIndexEnvelope uniform reuse arrival queries signatures
        (indexPowerVector (cache i) (signings i)) groups.card remaining.card := by
  have hsum : (fun G R => ∑ i, indexPowerVector (cache i) (signings i) G.card R.card) =
      fun G R => ∑' i, liftTargetIndexVector (indexPowerVector (cache i) (signings i)) G R := by
    funext G R
    rw [tsum_fintype]
    rfl
  rw [hsum, targetShapeEnvelope_tsum, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact targetShapeEnvelope_lift uniform reuse arrival queries signatures _ groups remaining hvalid

theorem reuseRawEnvelope_query_shift_le (key : SecretKey) (reuse : ENNReal)
    (queries signatures bound : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) (hdegree : groups.card + remaining.card ≤ bound) :
    reuseRawEnvelope key reuse queries signatures state groups remaining ≤
      ∑ index : Index, (targetIndexSigning (Fintype.card Index : ENNReal)⁻¹ reuse)^[signatures]
        (indexPowerVector
          (cachedIndexMultiplicity key.parameter state.1 index +
            (queries : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + bound)
          ((signingSlotsAtIndex (observedOptionalSigningViews
            (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal))
        groups.card remaining.card := by
  have harrival : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) =
      ((2 ^ 36 : Nat) : ENNReal)⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness))]
    norm_num [ftsTreeHeight, Index, totalHeight]
  have hrate : (((2 ^ 36 : Nat) : ENNReal)⁻¹) ≤ 1 := by norm_num
  unfold reuseRawEnvelope observedRawIndexShapeVector liftTargetIndexVector targetIndexMoments
  change targetShapeEnvelope _ _ _ queries signatures
    (fun G R => ∑ index : Index, indexPowerVector _ _ G.card R.card) groups remaining ≤ _
  rw [targetShapeEnvelope_sum_indexPower _ _ _ _ _ _ _ groups remaining hvalid, harrival]
  apply Finset.sum_le_sum
  intro index _
  exact targetIndexEnvelope_power_query_shift_le hrate _ _ _ _ queries signatures bound _ _ hdegree

end SphincsSecurity.Concrete
