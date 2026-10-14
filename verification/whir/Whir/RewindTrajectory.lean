import Whir.InteractiveSoundness

/-! Actual accepted continuations recover a generic extension-field list candidate at any chosen level, not merely an initial base-word candidate. The proof reuses the actual causal fold/query transitions and terminal collision cover. It does not assert that different reset executions choose the same candidate; the separate OOD/batching argument is needed for that. -/
namespace Whir.RewindTrajectory
open Concrete Protocol CausalGame CausalExecution ExecutionShapes ParameterBounds VerifierInvariant

/-- Loss may begin at any level: no initial candidate or initial batching assumption is needed. -/
theorem accepted_level_lost_cover (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (start : Fin (config p).folds.size)
    (incoming : Lost (foldCandidates (Input p lanes root claims) strategy tape start 0)
      (levelAt (Input p lanes root claims) strategy tape start).state) :
    ∃ q, CausalBadEvents.Bad (Input p lanes root claims) strategy q tape := by
  classical
  apply Classical.byContradiction
  intro noBad
  have safe (q) : ¬ CausalBadEvents.Bad (Input p lanes root claims) strategy q tape :=
    fun h => noBad ⟨q, h⟩
  have entering (j : Nat) (hj : j < (config p).folds.size) (after : start.val ≤ j) :
      Lost (foldCandidates (Input p lanes root claims) strategy tape j 0)
        (levelAt (Input p lanes root claims) strategy tape j).state := by
    induction j with
    | zero =>
      have initial : start.val = 0 := by omega
      simpa only [initial] using incoming
    | succ j ih =>
      by_cases initial : start.val = j + 1
      · simpa only [initial] using incoming
      · have previous : j < (config p).folds.size := by omega
        have before : start.val ≤ j := by omega
        let index : Fin (config p).folds.size := ⟨j, previous⟩
        have folded := InteractiveSoundness.folds_preserve_lost p lanes root claims strategy tape
          index (ih previous before) (fun k => safe (.fold index k))
        have queried := InteractiveSoundness.query_preserves_lost p lanes root claims strategy tape
          accepted index folded (fun k => safe (.ood index k)) (safe (.query index))
        rw [following_eq_next _ _ _ j hj] at queried
        exact queried
  have positive := (production_config_valid p).2.1
  let last : Fin (config p).folds.size := ⟨(config p).folds.size - 1, by omega⟩
  have lastEnd : last.val + 1 = (config p).folds.size := by dsimp [last]; omega
  have noNext : ¬ last.val + 1 < (config p).folds.size := by omega
  have after : start.val ≤ last.val := by dsimp [last]; omega
  have folded := InteractiveSoundness.folds_preserve_lost p lanes root claims strategy tape last
    (entering last last.isLt after) (fun j => safe (.fold last j))
  have queried := InteractiveSoundness.query_preserves_lost p lanes root claims strategy tape
    accepted last folded (fun j => safe (.ood last j)) (safe (.query last))
  have beforeState := (accepted_execution (Input p lanes root claims) strategy tape accepted).2.2
  have incoming : dot (proof (Input p lanes root claims) strategy tape).residual
      (CausalTerminal.before (Input p lanes root claims) strategy tape).weight ≠
        (CausalTerminal.before (Input p lanes root claims) strategy tape).claim := by
    have member : (proof (Input p lanes root claims) strategy tape).residual ∈
        followingCandidates (Input p lanes root claims) strategy tape last := by
      simp only [followingCandidates, noNext, ↓reduceIte, Finset.mem_singleton]
    have lost := queried _ member
    simpa only [lastEnd, beforeState] using lost
  have checked := accepted_level (Input p lanes root claims) strategy tape accepted last last.isLt
  have terminalShape := boundary_shape (config p) (challenges (config p) tape)
    (proof (Input p lanes root claims) strategy tape) last _ _ checked
  dsimp only at terminalShape
  rw [← foldAt_end (Input p lanes root claims) strategy tape last last.isLt] at terminalShape
  have dims := (foldAt_shape p lanes root claims strategy tape last (config p).folds[last.val]! le_rfl).1
  simp only [Nat.sub_self, Nat.add_zero] at dims
  rw [dims] at terminalShape
  have shapeLast : (proof (Input p lanes root claims) strategy tape).residual.size =
      2 ^ remaining (config p) last := by
    have pair : (proof (Input p lanes root claims) strategy tape).levels[last.val]!.nextOracle = none ∧
        (proof (Input p lanes root claims) strategy tape).residual.size = 2 ^ remaining (config p) last := by
      simpa only [noNext, ↓reduceIte] using terminalShape
    exact pair.2
  have remainingLast : remaining (config p) last = (config p).logN - (config p).folds.toList.sum := by
    unfold remaining
    rw [lastEnd, ← Array.length_toList, List.take_length]
  rw [remainingLast] at shapeLast
  have weight := (levelAt_shape p lanes root claims strategy tape (config p).folds.size le_rfl).2
  rw [beforeState] at weight
  simp only [before] at weight
  have takeAll : (config p).folds.toList.take (config p).folds.size = (config p).folds.toList := by
    rw [← Array.length_toList, List.take_length]
  rw [takeAll] at weight
  have weightShape : (CausalTerminal.before (Input p lanes root claims) strategy tape).weight.size =
      (proof (Input p lanes root claims) strategy tape).residual.size := weight.trans shapeLast.symm
  obtain ⟨j, escaped⟩ := CausalTerminal.event_has_collision (Input p lanes root claims) strategy tape
    ⟨accepted, shapeLast, weightShape, incoming⟩
  exact safe (.tail j) escaped

/-- A genuine generic-E candidate exists at every level of an accepted continuation outside the already charged actual prefix events. -/
theorem accepted_level_candidate (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (start : Fin (config p).folds.size)
    (safe : ∀ q, ¬ CausalBadEvents.Bad (Input p lanes root claims) strategy q tape) :
    ∃ witness ∈ foldCandidates (Input p lanes root claims) strategy tape start 0,
      dot witness (levelAt (Input p lanes root claims) strategy tape start).state.weight =
        (levelAt (Input p lanes root claims) strategy tape start).state.claim := by
  classical
  by_contra missing
  have lost : Lost (foldCandidates (Input p lanes root claims) strategy tape start 0)
      (levelAt (Input p lanes root claims) strategy tape start).state := by
    simpa only [Lost, not_exists, not_and] using missing
  obtain ⟨q, bad⟩ := accepted_level_lost_cover p lanes root claims strategy tape accepted start lost
  exact safe q bad

/-- In particular, Root1 has its own fixed generic-E list, rather than an assumed Root0 decoder radius. -/
theorem accepted_following_candidate (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (level : Fin (config p).folds.size) (hasNext : level.val + 1 < (config p).folds.size)
    (safe : ∀ q, ¬ CausalBadEvents.Bad (Input p lanes root claims) strategy q tape) :
    ∃ witness ∈ followingCandidates (Input p lanes root claims) strategy tape level,
      dot witness (levelAt (Input p lanes root claims) strategy tape (level.val + 1)).state.weight =
        (levelAt (Input p lanes root claims) strategy tape (level.val + 1)).state.claim := by
  rw [following_eq_next _ _ _ level hasNext]
  exact accepted_level_candidate p lanes root claims strategy tape accepted ⟨level.val + 1, hasNext⟩ safe

#print axioms accepted_level_lost_cover
#print axioms accepted_level_candidate
#print axioms accepted_following_candidate
end Whir.RewindTrajectory
