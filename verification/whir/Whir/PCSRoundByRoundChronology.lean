import Whir.CausalPositions

/-! Chronology includes the verifier's final tail draw even though it receives
no subsequent prover response. -/
namespace Whir.PCSRoundByRoundChronology
open Concrete Protocol CausalGame CausalProbability CausalPositions
open Classical

private theorem tail_not_mem_levels (c : Config) (j : Fin (c.logN - c.folds.toList.sum)) :
    Coordinate.tail j ∉ [.initial] ++ (List.range c.folds.size).flatMap (levelCoordinates c) := by
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap]
  rintro (impossible | ⟨i, hi, member⟩)
  · cases impossible
  · have within := List.mem_range.mp hi
    simp [levelCoordinates, within] at member

private theorem levelPrefix_length (c : Config) (t : Tape c) :
    ([Coordinate.initial] ++ (List.range c.folds.size).flatMap (levelCoordinates c)).length =
      tailStart c (challenges c t) := by
  have mapped : ((List.range c.folds.size).flatMap (levelCoordinates c)).map
      (fun q => batch q (get q t)) =
      (List.range c.folds.size).flatMap (levelBatches (challenges c t)) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro i hi
    exact levelCoordinates_map c t i (List.mem_range.mp hi)
  have lengths := congrArg List.length mapped
  simpa only [List.length_map, List.length_append, List.length_singleton,
    tailStart, levelStart] using congrArg (fun n => 1 + n) lengths

/-- Zero-based position of every actual terminal draw, including the final one. -/
theorem position_tail (c : Config) (t : Tape c) (j : Fin (c.logN - c.folds.toList.sum)) :
    position (.tail j) = tailStart c (challenges c t) + j.val := by
  unfold position visibleCoordinates
  rw [List.idxOf_append_of_notMem (tail_not_mem_levels c j)]
  rw [levelPrefix_length c t]
  congr 1
  by_cases visible : j.val < c.logN - c.folds.toList.sum - 1
  · let k : Fin (c.logN - c.folds.toList.sum - 1) := ⟨j.val, visible⟩
    have member : Coordinate.tail j ∈ (List.ofFn fun k : Fin (c.logN - c.folds.toList.sum - 1) =>
        Coordinate.tail ⟨k.val, by omega⟩) := by
      apply List.mem_ofFn.mpr
      exact ⟨k, by congr⟩
    have bound := List.idxOf_lt_length_of_mem member
    have eq := List.getElem_idxOf bound
    simp only [List.getElem_ofFn] at eq
    exact congrArg (fun q => match q with | Coordinate.tail a => a.val | _ => 0) eq
  · have absent : Coordinate.tail j ∉ (List.ofFn fun k : Fin (c.logN - c.folds.toList.sum - 1) =>
        Coordinate.tail ⟨k.val, by omega⟩) := by
      intro member
      obtain ⟨k, eq⟩ := List.mem_ofFn.mp member
      have same := Coordinate.tail.inj eq
      have values : k.val = j.val := congrArg Fin.val same
      exact visible (values ▸ k.isLt)
    rw [List.idxOf_eq_length_iff.mpr absent, List.length_ofFn]
    omega

end Whir.PCSRoundByRoundChronology
