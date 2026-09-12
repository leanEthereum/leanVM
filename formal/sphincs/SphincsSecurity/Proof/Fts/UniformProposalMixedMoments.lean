import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.UniformProposalMoments
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

noncomputable def uniformWordAverage {α : Type} [SampleableType α]
    (steps : Nat) (payoff : List α → ENNReal) : ENNReal :=
  ∑' word, Pr[= word | sampleUniformProposalWord α steps] * payoff word

theorem uniformWordAverage_add {α : Type} [SampleableType α]
    (steps : Nat) (first second : List α → ENNReal) :
    uniformWordAverage steps (fun word => first word + second word) =
      uniformWordAverage steps first + uniformWordAverage steps second := by
  simp only [uniformWordAverage, mul_add, ENNReal.tsum_add]

theorem uniformWordAverage_mul_left {α : Type} [SampleableType α]
    (steps : Nat) (factor : ENNReal) (payoff : List α → ENNReal) :
    uniformWordAverage steps (fun word => factor * payoff word) =
      factor * uniformWordAverage steps payoff := by
  simp only [uniformWordAverage, mul_left_comm _ factor, ENNReal.tsum_mul_left]

theorem uniformWordAverage_sum {α β : Type} [SampleableType α]
    (steps : Nat) (set : Finset β) (payoff : β → List α → ENNReal) :
    uniformWordAverage steps (fun word => ∑ index ∈ set, payoff index word) =
      ∑ index ∈ set, uniformWordAverage steps (payoff index) := by
  simp only [uniformWordAverage, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

theorem uniformWordAverage_count_descFactorial {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (index : α) (steps degree : Nat) :
    uniformWordAverage steps (fun word : List α => (word.count index).descFactorial degree) =
      (steps.descFactorial degree : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ^ degree := by
  letI : Nonempty α := ⟨index⟩
  rw [uniformWordAverage, expected_uniformProposalWord_count index steps
    (fun count => (count.descFactorial degree : ENNReal))]
  exact binomialAverage_descFactorial (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos)) steps degree

theorem descFactorial_succ_add (count degree : Nat) :
    (count + 1).descFactorial (degree + 1) =
      count.descFactorial (degree + 1) + (degree + 1) * count.descFactorial degree := by
  rw [Nat.succ_descFactorial_succ]
  calc
    _ = count * count.descFactorial degree + count.descFactorial degree := by ring
    _ = _ := by rw [mul_descFactorial_eq]; ring

private theorem expected_uniformSample_two_increments {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (first second : α) (base left right : ENNReal) :
    (∑' next : α, Pr[= next | ($ᵗ α : ProbComp α)] *
      (base + (if next = first then left else 0) + (if next = second then right else 0))) =
      base + (Fintype.card α : ENNReal)⁻¹ * left + (Fintype.card α : ENNReal)⁻¹ * right := by
  simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_zero]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_sub, probFailure_uniformSample, tsub_zero, one_mul]
  simp only [tsum_ite_eq, probOutput_uniformSample]

theorem uniformWordAverage_mixed_descFactorial {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (first second : α) (hdistinct : first ≠ second)
    (steps left right : Nat) :
    uniformWordAverage steps (fun word : List α =>
      ((word.count first).descFactorial left : ENNReal) * (word.count second).descFactorial right) =
      (steps.descFactorial (left + right) : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ^ (left + right) := by
  induction steps generalizing left right with
  | zero =>
      cases left <;> cases right <;>
        simp [uniformWordAverage, sampleUniformProposalWord]
  | succ steps ih =>
      cases left with
      | zero =>
          simpa only [Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.zero_add] using
            uniformWordAverage_count_descFactorial second (steps + 1) right
      | succ left =>
          cases right with
          | zero =>
              simpa only [Nat.descFactorial_zero, Nat.cast_one, mul_one, Nat.add_zero] using
                uniformWordAverage_count_descFactorial first (steps + 1) (left + 1)
          | succ right =>
              have hpoint (word : List α) (next : α) :
                  (((next :: word).count first).descFactorial (left + 1) : ENNReal) *
                    ((next :: word).count second).descFactorial (right + 1) =
                  ((word.count first).descFactorial (left + 1) : ENNReal) *
                    (word.count second).descFactorial (right + 1) +
                  (if next = first then (left + 1 : ENNReal) *
                    ((word.count first).descFactorial left * (word.count second).descFactorial (right + 1)) else 0) +
                  (if next = second then (right + 1 : ENNReal) *
                    ((word.count first).descFactorial (left + 1) * (word.count second).descFactorial right) else 0) := by
                by_cases hfirst : next = first
                · subst next
                  simp only [List.count_cons_self, List.count_cons_of_ne hdistinct,
                    descFactorial_succ_add, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
                    ↓reduceIte, if_neg hdistinct, add_zero]
                  ring
                · by_cases hsecond : next = second
                  · subst next
                    simp only [List.count_cons_self, List.count_cons_of_ne hfirst,
                      descFactorial_succ_add, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
                      ↓reduceIte, if_neg hfirst, add_zero]
                    ring
                  · simp only [List.count_cons_of_ne hfirst, List.count_cons_of_ne hsecond,
                      if_neg hfirst, if_neg hsecond, add_zero]
              rw [uniformWordAverage, sampleUniformProposalWord, tsum_probOutput_bind_mul]
              simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
              simp_rw [← ENNReal.tsum_mul_left]
              rw [ENNReal.tsum_comm]
              simp_rw [← mul_assoc]
              have hreorder :
                  (∑' word : List α, ∑' next : α, Pr[= next | ($ᵗ α : ProbComp α)] *
                    Pr[= word | sampleUniformProposalWord α steps] *
                    (((next :: word).count first).descFactorial (left + 1) : ENNReal) *
                    ((next :: word).count second).descFactorial (right + 1)) =
                  uniformWordAverage steps (fun word : List α =>
                    ((word.count first).descFactorial (left + 1) : ENNReal) *
                      (word.count second).descFactorial (right + 1) +
                    (Fintype.card α : ENNReal)⁻¹ * (left + 1) *
                      ((word.count first).descFactorial left * (word.count second).descFactorial (right + 1)) +
                    (Fintype.card α : ENNReal)⁻¹ * (right + 1) *
                      ((word.count first).descFactorial (left + 1) * (word.count second).descFactorial right)) := by
                unfold uniformWordAverage
                apply tsum_congr
                intro word
                calc
                  _ = Pr[= word | sampleUniformProposalWord α steps] * ∑' next : α,
                      Pr[= next | ($ᵗ α : ProbComp α)] *
                        ((((next :: word).count first).descFactorial (left + 1) : ENNReal) *
                          ((next :: word).count second).descFactorial (right + 1)) := by
                    rw [← ENNReal.tsum_mul_left]
                    apply tsum_congr
                    intro next
                    ring
                  _ = _ := by
                    simp_rw [hpoint, expected_uniformSample_two_increments]
                    ring
              rw [hreorder, uniformWordAverage_add, uniformWordAverage_add,
                uniformWordAverage_mul_left, uniformWordAverage_mul_left, ih, ih, ih]
              have hdegree : left + 1 + (right + 1) = (left + right + 1) + 1 := by omega
              rw [hdegree, descFactorial_succ_add]
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, pow_succ]
              have hexp : left + (right + 1) = left + right + 1 := by omega
              simp only [hexp, Nat.add_right_comm left 1 right, pow_succ]
              ring

theorem descFactorial_add_le_mul (steps left right : Nat) :
    steps.descFactorial (left + right) ≤ steps.descFactorial left * steps.descFactorial right := by
  have h := Nat.descFactorial_mul_descFactorial (n := steps) (k := left) (m := left + right)
    (Nat.le_add_right left right)
  rw [Nat.add_sub_cancel_left] at h
  rw [← h, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.descFactorial_le right (Nat.sub_le steps left))

theorem uniformWordAverage_mixed_descFactorial_le_product {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (first second : α) (hdistinct : first ≠ second)
    (steps left right : Nat) :
    uniformWordAverage steps (fun word : List α =>
      ((word.count first).descFactorial left : ENNReal) * (word.count second).descFactorial right) ≤
      uniformWordAverage steps (fun word : List α => (word.count first).descFactorial left) *
        uniformWordAverage steps (fun word : List α => (word.count second).descFactorial right) := by
  rw [uniformWordAverage_mixed_descFactorial first second hdistinct,
    uniformWordAverage_count_descFactorial, uniformWordAverage_count_descFactorial]
  calc
    _ ≤ ((steps.descFactorial left : ENNReal) * steps.descFactorial right) *
        (Fintype.card α : ENNReal)⁻¹ ^ (left + right) := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast descFactorial_add_le_mul steps left right
    _ = _ := by rw [pow_add]; ring

theorem uniformWordAverage_mono {α : Type} [SampleableType α]
    (steps : Nat) {first second : List α → ENNReal} (hle : ∀ word, first word ≤ second word) :
    uniformWordAverage steps first ≤ uniformWordAverage steps second :=
  ENNReal.tsum_le_tsum fun word => mul_le_mul' le_rfl (hle word)

theorem uniformWordAverage_mixed_power_le_product {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (first second : α) (hdistinct : first ≠ second)
    (steps left right : Nat) :
    uniformWordAverage steps (fun word : List α => (word.count first : ENNReal) ^ left *
      (word.count second : ENNReal) ^ right) ≤
      uniformWordAverage steps (fun word : List α => (word.count first : ENNReal) ^ left) *
        uniformWordAverage steps (fun word : List α => (word.count second : ENNReal) ^ right) := by
  have hpower (count degree : Nat) : (count : ENNReal) ^ degree =
      ∑ order ∈ Finset.range (degree + 1),
        (Nat.stirlingSecond degree order : ENNReal) * count.descFactorial order := by
    exact_mod_cast power_eq_stirling_descFactorial count degree
  simp_rw [hpower, Finset.sum_mul, Finset.mul_sum, uniformWordAverage_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hfactor :
      (fun word : List α =>
        ((Nat.stirlingSecond left a : ENNReal) * (word.count first).descFactorial a) *
          ((Nat.stirlingSecond right b : ENNReal) * (word.count second).descFactorial b)) =
      (fun word : List α =>
        ((Nat.stirlingSecond left a : ENNReal) * Nat.stirlingSecond right b) *
          ((word.count first).descFactorial a * (word.count second).descFactorial b)) := by
    funext word
    ring
  rw [hfactor, uniformWordAverage_mul_left, uniformWordAverage_mul_left, uniformWordAverage_mul_left]
  exact (mul_le_mul' le_rfl
    (uniformWordAverage_mixed_descFactorial_le_product first second hdistinct steps a b)).trans_eq (by ring)

noncomputable def stirlingPowerMoment (rate : ENNReal) (degree : Nat) : ENNReal :=
  ∑ order ∈ Finset.range (degree + 1), (Nat.stirlingSecond degree order : ENNReal) * rate ^ order

theorem uniformWordAverage_power_le_stirling {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (index : α) (steps degree : Nat) (rate : ENNReal)
    (hrate : (steps : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ≤ rate) :
    uniformWordAverage steps (fun word : List α => (word.count index : ENNReal) ^ degree) ≤
      stirlingPowerMoment rate degree := by
  letI : Nonempty α := ⟨index⟩
  rw [uniformWordAverage, expected_uniformProposalWord_count index steps (fun count => (count : ENNReal) ^ degree),
    binomialAverage_power (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos))]
  apply Finset.sum_le_sum
  intro order _
  calc
    _ ≤ (Nat.stirlingSecond degree order : ENNReal) * (steps : ENNReal) ^ order *
        (Fintype.card α : ENNReal)⁻¹ ^ order := by
      apply mul_le_mul' (mul_le_mul' le_rfl _) le_rfl
      exact_mod_cast Nat.descFactorial_le_pow steps order
    _ = (Nat.stirlingSecond degree order : ENNReal) *
        ((steps : ENNReal) * (Fintype.card α : ENNReal)⁻¹) ^ order := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left' hrate order)

end SphincsSecurity.Concrete
