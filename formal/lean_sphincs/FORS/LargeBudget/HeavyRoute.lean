module

public import FORS.LargeBudget.HeavyPotential
public import FORS.LargeBudget.Route

@[expose] public section

/-! The large-budget route with the weighted baseline and one heavy message. The one-coin FORS
potential is the one of `LargeBudget/HeavyPotential`: the coin only pays the rate of a message with at most half of
the budget in cached digests, so the fair-rate hypothesis is needed at `(q - keygenCost) / 2` cached
digests, and the start value of the potential is the excess forecast with one spare slot
(`startExcessH`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

/-! ### The start of the run -/

section StartH

/-- The one-coin excess forecast of a new pair at the start of the run, with the spare slot of the
potential with one heavy message. -/
noncomputable def startExcessH (wbar b0 : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excess b0) (signatureLimit + 1) I 0) k []

theorem hValueH_start (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (wbar b0 : ℝ≥0∞) (s : State)
    (k : ℕ) : hValueH parameter data Qtot wbar b0 s [] [] 0 signatureLimit k = startExcessH wbar b0 k := rfl

/-- At the start no digest block is cached: the whole budget is left. -/
theorem start_total (parameter : PublicParameter) (data : PublicData)
    (initial : HiddenOutside.Cache HashInput HashOutput) (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (known : Knowledge Coordinate) (budget : ℕ) :
    TotalInv parameter data budget (DebtState.start initial known) budget := by
  have h0 : totalCount parameter data (DebtState.start initial known) = 0 := by
    unfold totalCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ h
    exact h (hclean p firstCall)
  unfold TotalInv
  rw [h0, zero_add]

/-- **The potential at the start of the run**: the excess forecasts of the future pairs, the failing
indices, and the cap term of the landed pairs. -/
theorem potH_start_le (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (wbar b0 : ℝ≥0∞)
    (Fail : Finset (Fin (2 ^ subtreeHeight))) (tg : Targeting HashInput HashOutput Coordinate)
    (initial : HiddenOutside.Cache HashInput HashOutput) (Lmax : ℕ) (s : State) (k : ℕ) :
    potH parameter data Qtot wbar b0 Fail tg initial Lmax s [] [] [] 0 k ≤
      (k * (startExcessH wbar b0 k + failMass Fail) + signatureLimit * failMass Fail) + lam Lmax 0 k := by
  unfold potH
  refine add_le_add ?_ (le_of_eq rfl)
  split_ifs
  · exact bot_le
  · unfold coreH
    simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil, Nat.sub_zero]
    rw [hValueH_start]

end StartH

/-! ### The rest of the game, weighted, one heavy message -/

end FORS.Security.ForsPotential
