import Whir.CountedCandidateCheckOriginalWeights
import Whir.ExtractorArithmeticCostVerifier
import Whir.CommitmentAnchor

/-! The final original anchor check counts the literal anchor value functional, with one actual equality table and the actual dot loop. It is not a recomputed commitment, a resampled point, or a compressed replacement for the original anchor. -/
namespace Whir.CountedCandidateCheck
open Concrete Protocol CausalGame SupportedCandidateExtraction
open Whir.ExtractorArithmeticCost

def countedOriginalMle (candidate point : Array E) : E × Nat :=
  let table := countedEqTable point
  let result := countedDot candidate table.1
  (result.1, table.2 + result.2)

theorem countedOriginalMle_value (candidate point : Array E) :
    (countedOriginalMle candidate point).1 = Concrete.mle candidate point := by
  simp [countedOriginalMle, countedDot_value, countedEqTable_value, Concrete.mle]

theorem countedOriginalMle_field (candidate point : Array E) :
    (countedOriginalMle candidate point).2 ≤ 3 * 2 ^ point.size + 2 * candidate.size := by
  have table := countedEqTable_cost point
  have dot : (countedDot candidate (countedEqTable point).1).2 =
      2 * min candidate.size (countedEqTable point).1.size := rfl
  have minimum := Nat.min_le_left candidate.size (countedEqTable point).1.size
  unfold countedOriginalMle tableCharge at *
  dsimp only
  have dense : 2 ^ point.size - 1 ≤ 2 ^ point.size := Nat.sub_le _ _
  nlinarith

/-- The equality table materializes its bounded physical number of entries; no success or acceptance premise supplies this dimension. -/
theorem countedOriginalMle_table_size (point : Array E) :
    (countedEqTable point).1.size = 2 ^ point.size := by
  rw [countedEqTable_value]
  exact TerminalRefinement.size_eqTable point

def countedOriginalAnchor (c : Config) (lanes : Nat) (w : Witness c lanes) (point : Array E) : E × Nat :=
  countedOriginalMle (paddedWitness c lanes w) point

theorem countedOriginalAnchor_value (c : Config) (lanes : Nat) (w : Witness c lanes) (point : Array E) :
    (countedOriginalAnchor c lanes w point).1 = CommitmentAnchor.value c lanes w point :=
  countedOriginalMle_value _ _

#print axioms countedOriginalAnchor_value

end Whir.CountedCandidateCheck
