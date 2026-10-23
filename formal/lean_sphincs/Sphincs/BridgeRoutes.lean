import Sphincs.BridgeExpose

/-! The two routes of the final bound start from the seed-free win of an internalized adversary
(the deterministic signer reduces to it): the stopped prepared experiment, with or without the
above-word chain values exposed. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

open HiddenReveal HiddenCost Eager Short Concrete
open Completeness SeedModel Graph Assembly Reduce HiddenGraph Internalize GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- **The seed-free win in the stopped prepared world.** -/
theorem seedFree_le_prep (adversary : Adversary) (q : Nat) :
    Pr{let x ← seedFreeExperiment (internalize adversary) q}[Win x] ≤
      Pr{let x ← (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let prepared ← preparation parameterOutput fixed highs remaining
        HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          (knownOf (truncateHash parameterOutput) fixed) prepared.2)}[(HiddenReveal.StopOr RichWin) x] := by
  refine (seedFree_le_stopped (internalize adversary) q Win).trans (le_of_eq ?_)
  refine probEvent_bind_congr₂ _ _ _ _ _ fun parameterOutput => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun fixed => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun highs => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun remaining => ?_
  have hshort : OnlyShort (HiddenCost.erase (HiddenCost.trace
      (sampleProgram (internalize adversary) q parameterOutput fixed highs remaining))) :=
    OnlyC.erase (OnlyC.trace (OnlyC.cap (OnlyC.costGame (truncateHash parameterOutput)
      (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed))) adversary) q))
  unfold outsideFn
  rw [(evalDist_stoppedExperiment_prep (sampleModel parameterOutput highs) _ (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining).forestKey _ hshort _).prEvent_eq]
  refine probEvent_bind_congr₂ _ _ _ _ _ fun prepared => ?_
  rw [probEvent_stopOr_map]
  unfold HiddenOutside.stoppedExperiment
  refine probEvent_bind_congr₂ _ _ _ _ _ fun table => ?_
  have hprog : sampleProgram (internalize adversary) q parameterOutput fixed highs remaining =
      (fun result => Option.map outcomeWins result.1) <$> richProgram (internalize adversary) q
        (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) :=
    cap_costGame_eq _ _ _ _
  rw [hprog, trace_map, erase_map, outside_stopped_map, probEvent_stopOr_map]
  have hevent : (HiddenReveal.StopOr ((Win ∘ Prod.fst) ∘ fun result :
      ((Option Outcome × List HiddenGraph.Coordinate) × List (Entry HashInput)) × QueryCache HashSpec =>
        ((Option.map outcomeWins result.1.1.1, result.1.2), result.2))) =
      HiddenReveal.StopOr RichWin := by
    funext result
    rcases result with _ | ⟨⟨⟨outcome, reveals⟩, entries⟩, cache⟩
    · rfl
    · rcases outcome with _ | value <;> simp [HiddenReveal.StopOr, Win, RichWin]
  rw [hevent]

set_option maxRecDepth 100000 in
/-- **The seed-free win in the stopped prepared world, with the above-word values exposed.** -/
theorem seedFree_le_exposeP (adversary : Adversary) (q : Nat) :
    Pr{let x ← seedFreeExperiment (internalize adversary) q}[Win x] ≤
      Pr{let x ← (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let prepared ← preparation parameterOutput fixed highs remaining
        let known ← exposeR (aboveList (truncateHash parameterOutput) prepared.1)
          (knownOf (truncateHash parameterOutput) fixed)
        HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          known prepared.2)}[(HiddenReveal.StopOr RichWin) x] := by
  refine (seedFree_le_expose (internalize adversary) q Win
    (fun parameterOutput fixed highs remaining outsideTable =>
      aboveList (truncateHash parameterOutput)
        (resultsOf (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).forestKey
          (outsideFn (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed) outsideTable)))).trans (le_of_eq ?_)
  refine probEvent_bind_congr₂ _ _ _ _ _ fun parameterOutput => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun fixed => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun highs => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun remaining => ?_
  have hshort : OnlyShort (HiddenCost.erase (HiddenCost.trace
      (sampleProgram (internalize adversary) q parameterOutput fixed highs remaining))) :=
    OnlyC.erase (OnlyC.trace (OnlyC.cap (OnlyC.costGame (truncateHash parameterOutput)
      (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed))) adversary) q))
  unfold outsideFn
  rw [(evalDist_expose_prep (sampleModel parameterOutput highs) _ (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining).forestKey _ hshort _
      (aboveList (truncateHash parameterOutput))).prEvent_eq]
  refine probEvent_bind_congr₂ _ _ _ _ _ fun prepared => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun known => ?_
  rw [probEvent_stopOr_map]
  unfold HiddenOutside.stoppedExperiment
  refine probEvent_bind_congr₂ _ _ _ _ _ fun table => ?_
  have hprog : sampleProgram (internalize adversary) q parameterOutput fixed highs remaining =
      (fun result => Option.map outcomeWins result.1) <$> richProgram (internalize adversary) q
        (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) :=
    cap_costGame_eq _ _ _ _
  rw [hprog, trace_map, erase_map, outside_stopped_map, probEvent_stopOr_map]
  have hevent : (HiddenReveal.StopOr ((Win ∘ Prod.fst) ∘ fun result :
      ((Option Outcome × List HiddenGraph.Coordinate) × List (Entry HashInput)) × QueryCache HashSpec =>
        ((Option.map outcomeWins result.1.1.1, result.1.2), result.2))) =
      HiddenReveal.StopOr RichWin := by
    funext result
    rcases result with _ | ⟨⟨⟨outcome, reveals⟩, entries⟩, cache⟩
    · rfl
    · rcases outcome with _ | value <;> simp [HiddenReveal.StopOr, Win, RichWin]
  rw [hevent]

end Sphincs.Security.HiddenBridge
