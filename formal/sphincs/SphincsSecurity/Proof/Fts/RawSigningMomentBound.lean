import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.RawQueryMomentBound
namespace SphincsSecurity.Concrete

open ENNReal

theorem targetIndexSigning_add (uniform reuse : ENNReal) (first second : TargetIndexVector) :
    targetIndexSigning uniform reuse (fun p d => first p d + second p d) =
      fun p d => targetIndexSigning uniform reuse first p d + targetIndexSigning uniform reuse second p d := by
  funext power degree
  simp only [targetIndexSigning, targetIndexCacheLower, targetIndexTreeLower, targetIndexReuseStep,
    mul_add, Finset.sum_add_distrib]
  ring

theorem targetIndexSigning_mul (uniform reuse scalar : ENNReal) (moments : TargetIndexVector) :
    targetIndexSigning uniform reuse (fun p d => scalar * moments p d) =
      fun p d => scalar * targetIndexSigning uniform reuse moments p d := by
  have hcache (values : TargetIndexVector) (p d : Nat) :
      targetIndexCacheLower (fun p d => scalar * values p d) p d =
        scalar * targetIndexCacheLower values p d := by
    simp only [targetIndexCacheLower, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  have htree (values : TargetIndexVector) : targetIndexTreeLower (fun p d => scalar * values p d) =
      fun p d => scalar * targetIndexTreeLower values p d := by
    funext p d
    simp only [targetIndexTreeLower, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  funext power degree
  simp only [targetIndexSigning, hcache, htree, targetIndexReuseStep]
  ring

theorem targetIndexSigning_iterate_add (uniform reuse : ENNReal) (steps : Nat) (first second : TargetIndexVector) :
    (targetIndexSigning uniform reuse)^[steps] (fun p d => first p d + second p d) =
      fun p d => (targetIndexSigning uniform reuse)^[steps] first p d +
        (targetIndexSigning uniform reuse)^[steps] second p d := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [Function.iterate_succ_apply', ih, targetIndexSigning_add]

theorem targetIndexSigning_iterate_mul (uniform reuse scalar : ENNReal) (steps : Nat) (moments : TargetIndexVector) :
    (targetIndexSigning uniform reuse)^[steps] (fun p d => scalar * moments p d) =
      fun p d => scalar * (targetIndexSigning uniform reuse)^[steps] moments p d := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [Function.iterate_succ_apply', ih, targetIndexSigning_mul]

theorem indexPowerVector_signing_succ (cache signings : ENNReal) :
    indexPowerVector cache (signings + 1) =
      fun p d => indexPowerVector cache signings p d + targetIndexTreeLower (indexPowerVector cache signings) p d := by
  funext power degree
  simp only [indexPowerVector, ennreal_add_one_pow, mul_add, Finset.mul_sum, targetIndexTreeLower]
  congr 1
  apply Finset.sum_congr rfl
  intro lower _
  ring

theorem indexPowerVector_diagonal_succ (cache signings : ENNReal) (power degree : Nat) :
    indexPowerVector (cache + 1) (signings + 1) power degree =
      indexPowerVector cache signings power degree + targetIndexCacheLower (indexPowerVector cache signings) power degree +
        targetIndexTreeLower (indexPowerVector cache signings) power degree +
        targetIndexCacheLower (targetIndexTreeLower (indexPowerVector cache signings)) power degree := by
  rw [indexPowerVector_cache_succ, indexPowerVector_signing_succ]
  simp only [targetIndexCacheLower, mul_add, Finset.sum_add_distrib]
  ring

theorem targetIndexReuseStep_power (cache signings : ENNReal) (power degree : Nat) :
    targetIndexReuseStep (indexPowerVector cache signings) power degree =
      cache * targetIndexTreeLower (indexPowerVector cache signings) power degree := by
  simp only [targetIndexReuseStep, targetIndexTreeLower, indexPowerVector, pow_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  ring

theorem targetIndexSigning_power {uniform reuse cache : ENNReal}
    (hprob : uniform + reuse * cache ≤ 1) (signings : ENNReal) (power degree : Nat) :
    targetIndexSigning uniform reuse (indexPowerVector cache signings) power degree =
      (1 - (uniform + reuse * cache)) * indexPowerVector cache signings power degree +
        uniform * indexPowerVector (cache + 1) (signings + 1) power degree +
        reuse * cache * indexPowerVector cache (signings + 1) power degree := by
  rw [indexPowerVector_diagonal_succ, indexPowerVector_signing_succ]
  simp only [targetIndexSigning, targetIndexReuseStep_power]
  have hsum : 1 - (uniform + reuse * cache) + (uniform + reuse * cache) = 1 :=
    tsub_add_cancel_of_le hprob
  calc
    _ = (1 - (uniform + reuse * cache) + (uniform + reuse * cache)) *
        indexPowerVector cache signings power degree + uniform *
          (targetIndexCacheLower (indexPowerVector cache signings) power degree +
            targetIndexTreeLower (indexPowerVector cache signings) power degree +
            targetIndexCacheLower (targetIndexTreeLower (indexPowerVector cache signings)) power degree) +
          reuse * cache * targetIndexTreeLower (indexPowerVector cache signings) power degree := by
      rw [hsum]
      ring
    _ = _ := by ring

noncomputable def indexSigningAverage (uniform reuse : ENNReal) :
    Nat → (ENNReal → ENNReal → ENNReal) → ENNReal → ENNReal → ENNReal
  | 0, f, cache, signings => f cache signings
  | steps + 1, f, cache, signings =>
      (1 - (uniform + reuse * cache)) * indexSigningAverage uniform reuse steps f cache signings +
        uniform * indexSigningAverage uniform reuse steps f (cache + 1) (signings + 1) +
        reuse * cache * indexSigningAverage uniform reuse steps f cache (signings + 1)

theorem targetIndexSigning_iterate_power {uniform reuse cache : ENNReal}
    (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ 1)
    (signings : ENNReal) (power degree : Nat) :
    (targetIndexSigning uniform reuse)^[steps] (indexPowerVector cache signings) power degree =
      indexSigningAverage uniform reuse steps (fun c s => indexPowerVector c s power degree) cache signings := by
  induction steps generalizing cache signings power degree with
  | zero => rfl
  | succ steps ih =>
      have hbase : uniform + reuse * cache ≤ 1 :=
        (add_le_add le_rfl (mul_le_mul' le_rfl le_self_add)).trans hprob
      have hstay : uniform + reuse * (cache + steps) ≤ 1 := by
        apply le_trans _ hprob
        gcongr
        exact Nat.le_succ steps
      have hnext : uniform + reuse * (cache + 1 + steps) ≤ 1 := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hprob
      have hfun : targetIndexSigning uniform reuse (indexPowerVector cache signings) =
          fun p d => (1 - (uniform + reuse * cache)) * indexPowerVector cache signings p d +
            uniform * indexPowerVector (cache + 1) (signings + 1) p d +
            reuse * cache * indexPowerVector cache (signings + 1) p d := by
        funext p d
        exact targetIndexSigning_power hbase signings p d
      rw [Function.iterate_succ_apply, hfun]
      simp only [targetIndexSigning_iterate_add, targetIndexSigning_iterate_mul]
      rw [ih hstay, ih hnext, ih hstay]
      rfl

theorem bernoulli_mix_rate_mono {rate nextRate first second : ENNReal}
    (hrate : rate ≤ nextRate) (hnext : nextRate ≤ 1) (hvalue : first ≤ second) :
    (1 - rate) * first + rate * second ≤ (1 - nextRate) * first + nextRate * second := by
  have hsum : first + (second - first) = second := add_tsub_cancel_of_le hvalue
  calc
    _ = first + rate * (second - first) := by
      conv_lhs => rhs; rw [← hsum]
      exact bernoulli_mix_increment (hrate.trans hnext) _ _
    _ ≤ first + nextRate * (second - first) := add_le_add le_rfl (mul_le_mul' hrate le_rfl)
    _ = _ := by
      rw [← bernoulli_mix_increment hnext, hsum]

theorem indexSigningAverage_le_binomialAverage {uniform reuse rate cache : ENNReal}
    (hrate : rate ≤ 1) (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ rate)
    (f : ENNReal → ENNReal) (hmono : Monotone f) (signings : ENNReal) :
    indexSigningAverage uniform reuse steps (fun _ s => f s) cache signings ≤
      binomialAverage rate steps (fun count => f (signings + count)) := by
  induction steps generalizing cache signings with
  | zero => simp only [indexSigningAverage, binomialAverage_zero, Nat.cast_zero, add_zero, le_refl]
  | succ steps ih =>
      have hbase : uniform + reuse * cache ≤ rate :=
        (add_le_add le_rfl (mul_le_mul' le_rfl le_self_add)).trans hprob
      have hstay : uniform + reuse * (cache + steps) ≤ rate := by
        apply le_trans _ hprob
        gcongr
        exact Nat.le_succ steps
      have hnext : uniform + reuse * (cache + 1 + steps) ≤ rate := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hprob
      have hvalue : binomialAverage rate steps (fun count => f (signings + count)) ≤
          binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
        binomialAverage_mono rate steps (fun _ => hmono (add_le_add le_self_add le_rfl))
      calc
        _ ≤ (1 - (uniform + reuse * cache)) *
              binomialAverage rate steps (fun count => f (signings + count)) +
            uniform * binomialAverage rate steps (fun count => f (signings + 1 + count)) +
            reuse * cache * binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
          add_le_add (add_le_add (mul_le_mul' le_rfl (ih hstay signings))
            (mul_le_mul' le_rfl (ih hnext (signings + 1))))
            (mul_le_mul' le_rfl (ih hstay (signings + 1)))
        _ = (1 - (uniform + reuse * cache)) *
              binomialAverage rate steps (fun count => f (signings + count)) +
            (uniform + reuse * cache) *
              binomialAverage rate steps (fun count => f (signings + 1 + count)) := by ring
        _ ≤ (1 - rate) * binomialAverage rate steps (fun count => f (signings + count)) +
            rate * binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
          bernoulli_mix_rate_mono hbase hrate hvalue
        _ = _ := by
          simp only [binomialAverage_succ, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]

theorem targetIndexSigning_iterate_power_le_binomialAverage {uniform reuse rate cache : ENNReal}
    (hrate : rate ≤ 1) (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ rate)
    (signings : ENNReal) (degree : Nat) :
    (targetIndexSigning uniform reuse)^[steps] (indexPowerVector cache signings) 0 degree ≤
      binomialAverage rate steps (fun count => (signings + count) ^ degree) := by
  rw [targetIndexSigning_iterate_power steps (hprob.trans hrate)]
  simp only [indexPowerVector, pow_zero, one_mul]
  exact indexSigningAverage_le_binomialAverage hrate steps hprob (fun s => s ^ degree)
    (fun _ _ h => pow_le_pow_left' h degree) signings

end SphincsSecurity.Concrete
