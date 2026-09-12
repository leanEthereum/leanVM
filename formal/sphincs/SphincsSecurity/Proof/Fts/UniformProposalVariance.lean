import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.UniformProposalMixedMoments
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

theorem uniformWordAverage_sum_square_le {α β : Type} [SampleableType α] [Fintype β] [DecidableEq β]
    (steps : Nat) (payoff : β → List α → ENNReal)
    (hcross : ∀ first second, first ≠ second →
      uniformWordAverage steps (fun word => payoff first word * payoff second word) ≤
        uniformWordAverage steps (payoff first) * uniformWordAverage steps (payoff second)) :
    uniformWordAverage steps (fun word => (∑ index, payoff index word) ^ 2) ≤
      (∑ index, uniformWordAverage steps (payoff index)) ^ 2 +
        ∑ index, uniformWordAverage steps (fun word => payoff index word ^ 2) := by
  calc
    _ = ∑ first, ∑ second, uniformWordAverage steps
        (fun word => payoff first word * payoff second word) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, uniformWordAverage_sum]
      exact Finset.sum_comm
    _ ≤ ∑ first, ∑ second,
        (uniformWordAverage steps (payoff first) * uniformWordAverage steps (payoff second) +
          if second = first then uniformWordAverage steps (fun word => payoff first word ^ 2) else 0) := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      by_cases heq : first = second
      · subst second
        simp only [↓reduceIte, pow_two]
        exact le_add_self
      · simpa only [if_neg (Ne.symm heq), add_zero] using hcross first second heq
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        pow_two, Finset.sum_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_comm

noncomputable def proposalPowerSum {α : Type} [Fintype α] [DecidableEq α]
    (degree : Nat) (word : List α) : ENNReal :=
  ∑ index : α, (word.count index : ENNReal) ^ degree

theorem uniformWordAverage_powerSum_le {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (steps degree : Nat) (rate : ENNReal)
    (hrate : (steps : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ≤ rate) :
    uniformWordAverage steps (proposalPowerSum (α := α) degree) ≤
      (Fintype.card α : ENNReal) * stirlingPowerMoment rate degree := by
  unfold proposalPowerSum
  rw [uniformWordAverage_sum]
  calc
    _ ≤ ∑ _index : α, stirlingPowerMoment rate degree :=
      Finset.sum_le_sum fun index _ => uniformWordAverage_power_le_stirling index steps degree rate hrate
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem uniformWordAverage_powerSum_square_le {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (steps degree : Nat) (rate : ENNReal)
    (hrate : (steps : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ≤ rate) :
    uniformWordAverage steps (fun word => proposalPowerSum (α := α) degree word ^ 2) ≤
      uniformWordAverage steps (proposalPowerSum (α := α) degree) ^ 2 +
        (Fintype.card α : ENNReal) * stirlingPowerMoment rate (degree * 2) := by
  have h := uniformWordAverage_sum_square_le steps
    (fun index (word : List α) => (word.count index : ENNReal) ^ degree)
    (fun first second hne => uniformWordAverage_mixed_power_le_product first second hne steps degree degree)
  rw [← uniformWordAverage_sum] at h
  apply h.trans
  apply add_le_add le_rfl
  simp_rw [← pow_mul]
  calc
    _ ≤ ∑ _index : α, stirlingPowerMoment rate (degree * 2) :=
      Finset.sum_le_sum fun index _ => uniformWordAverage_power_le_stirling index steps (degree * 2) rate hrate
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end SphincsSecurity.Concrete
