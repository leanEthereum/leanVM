import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Chains.PartialChainEndpoint
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem one_sub_sum_le_prod {Index : Type} [DecidableEq Index] (indices : Finset Index)
    (loss : Index → ℝ) (hlower : ∀ index ∈ indices, 0 ≤ loss index) (hupper : ∀ index ∈ indices, loss index ≤ 1) :
    1 - ∑ index ∈ indices, loss index ≤ ∏ index ∈ indices, (1 - loss index) := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnot ih =>
      have hzero := hlower index (Finset.mem_insert_self _ _)
      have hone := hupper index (Finset.mem_insert_self _ _)
      have hsum : 0 ≤ ∑ other ∈ indices, loss other :=
        Finset.sum_nonneg (fun other hother => hlower other (Finset.mem_insert_of_mem hother))
      have htail := ih (fun other hother => hlower other (Finset.mem_insert_of_mem hother))
        (fun other hother => hupper other (Finset.mem_insert_of_mem hother))
      rw [Finset.sum_insert hnot, Finset.prod_insert hnot]
      calc
        _ ≤ (1 - loss index) * (1 - ∑ other ∈ indices, loss other) := by
          nlinarith [mul_nonneg hzero hsum]
        _ ≤ _ := mul_le_mul_of_nonneg_left htail (by linarith)

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]

noncomputable def queriedCount (observed : State → Option State) : Nat :=
  Fintype.card State - (unqueried observed).card

noncomputable def queryCount {n : Nat} (observed : Fin n → State → Option State) : Nat :=
  ∑ step, queriedCount (observed step)

omit [DecidableEq State] [Nonempty State] in
theorem queriedCount_le (observed : State → Option State) : queriedCount observed ≤ Fintype.card State :=
  Nat.sub_le _ _

omit [DecidableEq State] in
theorem freeFraction_ne_top (observed : State → Option State) : freeFraction observed ≠ ⊤ := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold freeFraction
  finiteness

omit [DecidableEq State] in
theorem freeFraction_toReal (observed : State → Option State) :
    (freeFraction observed).toReal = 1 - (queriedCount observed : ℝ) / Fintype.card State := by
  have hcard : (Fintype.card State : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcount : (unqueried observed).card ≤ Fintype.card State := Finset.card_le_univ _
  rw [freeFraction, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    queriedCount, Nat.cast_sub hcount, sub_div, div_self hcard]
  ring

omit [DecidableEq State] in
theorem product_ge_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    1 - (queryCount observed : ENNReal) / Fintype.card State ≤ ∏ step, freeFraction (observed step) := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcardR : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  by_cases hbudget : (queryCount observed : ENNReal) / Fintype.card State ≤ 1
  · apply (ENNReal.toReal_le_toReal (by finiteness)
      (ENNReal.prod_ne_top (fun step _ => freeFraction_ne_top (observed step)))).mp
    rw [ENNReal.toReal_sub_of_le hbudget (by finiteness), ENNReal.toReal_one, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    simp only [ENNReal.toReal_prod, freeFraction_toReal, queryCount, Nat.cast_sum, Finset.sum_div]
    exact one_sub_sum_le_prod Finset.univ (fun step => (queriedCount (observed step) : ℝ) / Fintype.card State)
      (fun _ _ => by positivity)
      (fun step _ => (div_le_one hcardR).mpr (by exact_mod_cast queriedCount_le (observed step)))
  · rw [tsub_eq_zero_of_le (le_of_not_ge hbudget)]
    exact bot_le

theorem meanPreimages_ge_queryCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    1 - (queryCount observed : ENNReal) / Fintype.card State ≤ meanPreimages observed endpoint :=
  (product_ge_queryCount observed).trans (meanPreimages_ge_product observed endpoint)

theorem meanPreimages_ge_budget {n : Nat} (observed : Fin n → State → Option State) (endpoint : State)
    (budget : Nat) (hbudget : queryCount observed ≤ budget) :
    1 - (budget : ENNReal) / Fintype.card State ≤ meanPreimages observed endpoint := by
  apply le_trans _ (meanPreimages_ge_queryCount observed endpoint)
  have hcount : (queryCount observed : ENNReal) ≤ (budget : ENNReal) := by exact_mod_cast hbudget
  exact tsub_le_tsub_left (ENNReal.div_le_div_right hcount _) _

end SphincsSecurity.Concrete.PartialChainEndpoint
