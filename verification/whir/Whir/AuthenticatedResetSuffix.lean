import Whir.AuthenticatedResetCollector

/-! Fresh suffix entropy replaces every coordinate at or after a legal query
cut. Prefix messages and the fixed prover coins are replayed unchanged. Extra
unused prefix entropy in the fresh tape is ignored, not rejection-sampled. -/
namespace Whir.AuthenticatedResetSupport
open Concrete Protocol CausalGame CausalProbability KnowledgeExtraction

/-- Only verifier tape coordinates, never prover responses, are reset. -/
def resetCoordinates {c : Config} (cut : Nat) (fresh : Tape c) :
    List (Coordinate c) → Tape c → Tape c
  | [], base => base
  | q :: qs, base => resetCoordinates cut fresh qs
      (if cut ≤ position q then set q base (get q fresh) else base)

def resetSuffix {c : Config} (cut : Nat) (base fresh : Tape c) : Tape c :=
  resetCoordinates cut fresh (visibleCoordinates c ++
    List.ofFn (fun j : Fin (c.logN - c.folds.toList.sum) => Coordinate.tail j)) base

theorem resetCoordinates_prefix {c : Config} (cut : Nat) (fresh base : Tape c)
    (qs : List (Coordinate c)) :
    (visibleBatches c (resetCoordinates cut fresh qs base).1
      (challenges c (resetCoordinates cut fresh qs base))).take cut =
        (visibleBatches c base.1 (challenges c base)).take cut := by
  induction qs generalizing base with
  | nil => rfl
  | cons q qs ih =>
    unfold resetCoordinates
    rw [ih]
    split
    · rename_i later
      have fixed := visible_prefix q base (get q fresh)
      have take := congrArg (List.take cut) fixed
      simpa only [List.take_take, Nat.min_eq_left later] using take
    · rfl

theorem resetCoordinates_levelAt (input : Public) (strategy : Strategy) (cut : Nat)
    (fresh base : Tape input.config) (qs : List (Coordinate input.config))
    (level : Fin input.config.folds.size)
    (before : levelStart (challenges input.config base) level ≤ cut) :
    CausalExecution.levelAt input strategy (resetCoordinates cut fresh qs base) level =
      CausalExecution.levelAt input strategy base level := by
  induction qs generalizing base with
  | nil => rfl
  | cons q qs ih =>
    unfold resetCoordinates
    split
    · rename_i later
      rw [ih _ (by rw [CausalPositions.levelStart_set]; exact before)]
      exact CausalStateCausality.levelAt_set input strategy q base (get q fresh)
        level level.isLt.le (before.trans later)
    · exact ih base before

/-- The sampler's query squeezes and its independent lambda are retained as
one actual query message. The fresh suffix includes all later coordinates. -/
def fullResetTape (input : Public) (base : Tape input.config)
    (level : Fin input.config.folds.size) (depth : Nat)
    (chunks : queryChunks input.config level =
      ((input.config.queries[level.val]! + 192 / depth - 1) / (192 / depth)))
    (query : RewindCoverage.QueryTape depth input.config.queries[level.val]!)
    (suffix : E × Tape input.config) : Tape input.config :=
  set (.query level) (resetSuffix (position (.query level)) base suffix.2)
    ((fun j => query (Fin.cast chunks j)), suffix.1)

theorem fullResetTape_prefix (input : Public) (base : Tape input.config)
    (level : Fin input.config.folds.size) (depth : Nat) (chunks) (query) (suffix) :
    RewindRowExtraction.queryPrefix input (fullResetTape input base level depth chunks query suffix) level =
      RewindRowExtraction.queryPrefix input base level := by
  unfold fullResetTape
  rw [RewindRowExtraction.queryPrefix_reset]
  exact resetCoordinates_prefix _ _ _ _

theorem fullResetTape_oracle (input : Public) (strategy : Strategy) (base : Tape input.config)
    (level : Fin input.config.folds.size) (depth : Nat) (chunks) (query) (suffix) :
    (CausalExecution.levelAt input strategy (fullResetTape input base level depth chunks query suffix) level).oracle =
      (CausalExecution.levelAt input strategy base level).oracle := by
  unfold fullResetTape
  rw [RewindRowExtraction.reset_oracle_fixed]
  have before : levelStart (challenges input.config base) level ≤ position (.query level) := by
    rw [CausalPositions.position_query level base]
    omega
  exact congrArg CheckedState.oracle (resetCoordinates_levelAt input strategy _ _ base _ level before)

theorem fullResetTape_squeezes (input : Public) (base : Tape input.config)
    (level : Fin input.config.folds.size) (depth : Nat) (chunks) (query) (suffix) :
    (challenges input.config (fullResetTape input base level depth chunks query suffix)).levels[level.val]!.querySqueezes =
      Array.ofFn query := by
  simp only [challenges, _root_.getElem!_pos, Array.size_ofFn, level.isLt, Array.getElem_ofFn]
  change Array.ofFn (get (.query level) (fullResetTape input base level depth chunks query suffix)).1 = _
  unfold fullResetTape
  rw [get_set]
  apply Array.ext
  · simp only [Array.size_ofFn]
    exact chunks
  · intro i hi hi'
    simp only [Array.getElem_ofFn, Fin.cast]

#print axioms fullResetTape_squeezes

#print axioms fullResetTape_prefix
#print axioms fullResetTape_oracle
end Whir.AuthenticatedResetSupport
