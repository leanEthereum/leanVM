import Sphincs.BridgeForsAssembly
import Sphincs.BridgeNoRepeat
import Sphincs.BridgeForsGameOnce

/-! The one-coin excess forecast of a new pair at the start of the run (`startExcessO`), which is
the start value of the future-pair term of the one-coin FORS potential. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

section TotalO

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The one-coin excess forecast of a new pair at the start of the run. -/
noncomputable def startExcessO (wbar b0 : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excess b0) signatureLimit I 0) k []

theorem hValueO_start (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (s : State) (k : ℕ) :
    hValueO parameter data wbar b0 s [] [] 0 signatureLimit k = startExcessO wbar b0 k := rfl

omit [Params] in
/-- At the start no digest block is cached: the empty list of touched messages is valid. -/
theorem start_minv (parameter : PublicParameter) (data : PublicData)
    (initial : HiddenOutside.Cache HashInput HashOutput) (hclean : ∀ p, initial (pblk parameter data p) = none)
    (known : Knowledge Coordinate) : MInv parameter data (DebtState.start initial known) [] :=
  ⟨List.nodup_nil, fun m ρ h => absurd (hclean (m, ρ)) h⟩

/-- **The potential at the start of the run**: the excess forecasts of the future pairs, the failing
indices, and the cap term of the landed pairs. -/
theorem potO_start_le (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞)
    (Fail : Finset (Fin (2 ^ subtreeHeight))) (tg : Targeting HashInput HashOutput Coordinate)
    (initial : HiddenOutside.Cache HashInput HashOutput) (Lmax : ℕ) (s : State) (k : ℕ) :
    potO parameter data wbar b0 Fail tg initial Lmax s [] [] [] 0 k ≤
      (k * (startExcessO wbar b0 k + failMass Fail) + signatureLimit * failMass Fail) + lam Lmax 0 k := by
  unfold potO
  refine add_le_add ?_ (le_of_eq rfl)
  split_ifs
  · exact bot_le
  · unfold coreO
    simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil, Nat.sub_zero]
    rw [hValueO_start]

end TotalO

end Sphincs.Security.ForsPotential
