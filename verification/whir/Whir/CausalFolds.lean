import Whir.CausalStateCausality
import Whir.ProductionTransitions

/-! Actual prefix restoration events for production fold coordinates. -/
namespace Whir.CausalFolds
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStateCausality
open VerifierInvariant ParameterBounds GroupedChallenges

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A local invariant restoration, guarded by the incoming physical shape.
No future acceptance test occurs in this event. -/
def Event (input : Public) (strategy : Strategy) (i : Fin input.config.folds.size)
    (j : Fin input.config.folds[i.val]!) (t : Tape input.config) : Prop :=
  (foldAt input strategy t i j).state.weight.size =
      2 ^ (input.config.folds[i.val]! - j.val) * dimension input.config i ∧
  Lost (foldCandidates input strategy t i j) (foldAt input strategy t i j).state ∧
  ¬ Lost (foldCandidates input strategy t i (j.val+1))
      (foldAt input strategy t i (j.val+1)).state

/-- Physical pair indexing agrees with the actual current lane width. -/
theorem pair_width (k j : Nat) (h : j < k) :
    2 ^ (k-j) = 2 ^ (k-(j+1)) * 2 := by
  rw [show k-j = (k-(j+1))+1 by omega, pow_succ]

theorem block_eq (c : Config) (i : Fin c.folds.size) :
    block c i = CandidateFolding.foldBlock (i.val == 0) (dimension c i) := by
  unfold block CandidateFolding.foldBlock dimension remaining
  by_cases hi : i.val = 0
  · simp only [hi, beq_self_eq_true, ↓reduceIte]
    have hz : 0 < c.folds.size := by omega
    rw [List.take_one]
    simp [List.head?_eq_getElem?, _root_.getElem!_pos, hz]
  · simp [hi]

theorem foldError_nonneg (p : Profile) (i : Fin (config p).folds.size) :
    0 ≤ foldError (config p) (estimates (config p)) i := by
  change (0 : ℚ) ≤ (2 * 2^32 + 2^108) / 2^192
  positivity

/-- Prefix measurability: replacing any coordinate after this indivisible
fold-and-reply leaves the event unchanged, without conditioning on acceptance. -/
theorem event_set (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!)
    (q : Coordinate input.config) (t : Tape input.config) (x : Sample q)
    (before : levelStart (challenges input.config t) i.val + (j.val+1) ≤ position q) :
    Event input strategy i j (set q t x) ↔ Event input strategy i j t := by
  unfold Event
  rw [foldAt_set input strategy q t x i j.val (by omega) (by omega),
    foldAt_set input strategy q t x i (j.val+1) (by omega) before,
    foldCandidates_set input strategy q t x i j.val (by omega) (by omega),
    foldCandidates_set input strategy q t x i (j.val+1) (by omega) before]

theorem pairedOracle_set (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!)
    (q : Coordinate input.config) (t : Tape input.config) (x : Sample q)
    (before : levelStart (challenges input.config t) i.val + j.val ≤ position q) {N : Nat} :
    OracleReplay.pairedOracle (i.val == 0) input.config.folds[i.val]!
      (levelAt input strategy (set q t x) i.val).oracle
      (challenges input.config (set q t x)).levels[i.val]!.folds j.val j.isLt (N := N) =
    OracleReplay.pairedOracle (i.val == 0) input.config.folds[i.val]!
      (levelAt input strategy t i.val).oracle
      (challenges input.config t).levels[i.val]!.folds j.val j.isLt := by
  unfold OracleReplay.pairedOracle
  rw [oracleAt_set input strategy q t x i j.val (by omega) before]

open Classical in
/-- Every exact coordinate fiber is bounded. The decoded pending message remains
an arbitrary function of the fresh scalar; only its incoming state is fixed. -/
theorem fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (i : Fin (config p).folds.size) (j : Fin (config p).folds[i.val]!)
    (t : Tape (config p)) :
    let input : Public := ⟨config p, lanes, root, claims⟩
    Soundness.uniformProb (Finset.univ.filter fun r : E =>
      Event input strategy i j (set (.fold i j) t r)) ≤
      foldError (config p) (estimates (config p)) i := by
  classical
  let input : Public := ⟨config p, lanes, root, claims⟩
  let old := (foldAt input strategy t i j).state
  let oracle := OracleReplay.pairedOracle (i.val == 0) (config p).folds[i.val]!
    (levelAt input strategy t i).oracle (challenges (config p) t).levels[i.val]!.folds j.val j.isLt
    (N := 2 ^ (remaining (config p) i + (config p).rates[i.val]!))
  let pending := fun r => (proof input strategy (set (.fold i j) t r)).levels[i.val]!.afterFold[j.val]!
  have position : levelStart (challenges input.config t) i.val + j.val =
      CausalProbability.position (.fold i j) := (CausalPositions.position_fold i j t).symm
  have hs (r : E) : foldAt input strategy (set (.fold i j) t r) i j =
      foldAt input strategy t i j :=
    foldAt_set input strategy (.fold i j) t r i j.val j.isLt.le position.le
  have hc (r : E) : foldCandidates input strategy (set (.fold i j) t r) i j =
      foldCandidates input strategy t i j :=
    foldCandidates_set input strategy (.fold i j) t r i j.val j.isLt.le position.le
  have paired :
      CandidateFolding.arrayCandidates (i.val == 0)
        (CandidateFolding.concreteEncoder (remaining (config p) i) (config p).rates[i.val]!)
        oracle (threshold (config p) i) = foldCandidates input strategy t i j :=
    OracleReplay.paired_candidates _ _ _ _ _ _ _ _ _
  have ha (r : E) : (foldAt input strategy (set (.fold i j) t r) i (j.val+1)).state =
      old.fold (CandidateFolding.foldBlock (i.val == 0) (dimension (config p) i)) r (pending r) := by
    rw [foldAt_succ, hs]
    simp only [foldStep, challenge_fold input.config _ i j, get_set, block_eq]
    rfl
  have hl (r : E) : foldCandidates input strategy (set (.fold i j) t r) i (j.val+1) =
      CandidateFolding.arrayCandidates (i.val == 0)
        (CandidateFolding.concreteEncoder (remaining (config p) i) (config p).rates[i.val]!)
        (CandidateFolding.foldOracle oracle r) (threshold (config p) i) := by
    unfold foldCandidates
    rw [OracleReplay.oracleAt_succ _ _ _ _ j.val j.isLt,
      pairedOracle_set input strategy i j (.fold i j) t r position.le,
      challenge_fold input.config _ i j, get_set]
  change Soundness.uniformProb (Finset.univ.filter fun r : E =>
    Event input strategy i j (set (.fold i j) t r)) ≤ _
  by_cases guard : old.weight.size =
      2 ^ ((config p).folds[i.val]! - j.val) * dimension (config p) i ∧
      Lost (foldCandidates input strategy t i j) old
  · have shape : old.weight.size =
        (2 ^ ((config p).folds[i.val]! - (j.val+1)) * 2) * dimension (config p) i := by
      rw [← pair_width _ _ j.isLt]
      exact guard.1
    have bound := ProductionTransitions.production_fold_escape (i.val == 0) p i
      oracle old pending shape (by rw [paired]; exact guard.2)
    have events : (Finset.univ.filter fun r : E =>
        Event input strategy i j (set (.fold i j) t r)) =
        (Finset.univ.filter fun r : E =>
          ¬ Lost (CandidateFolding.arrayCandidates (i.val == 0)
            (CandidateFolding.concreteEncoder (remaining (config p) i) (config p).rates[i.val]!)
            (CandidateFolding.foldOracle oracle r) (threshold (config p) i))
            (old.fold (CandidateFolding.foldBlock (i.val == 0) (dimension (config p) i)) r (pending r))) := by
      apply Finset.filter_congr
      intro r _
      unfold Event
      rw [hs, hc, hl, ha]
      change (old.weight.size = _ ∧ Lost (foldCandidates input strategy t i j) old ∧ _) ↔ _
      simp only [input, guard.1, guard.2, true_and]
    rw [events]
    exact bound
  · have empty : (Finset.univ.filter fun r : E =>
        Event input strategy i j (set (.fold i j) t r)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro r _ he
      unfold Event at he
      rw [hs, hc] at he
      exact guard ⟨he.1, he.2.1⟩
    rw [empty]
    simpa [Soundness.uniformProb] using foldError_nonneg p i

open Classical in
/-- Exact product averaging over the actual tape; events need not be independent. -/
theorem event_bound (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (i : Fin (config p).folds.size) (j : Fin (config p).folds[i.val]!) :
    Soundness.uniformProb (Finset.univ.filter
      (Event (⟨config p, lanes, root, claims⟩ : Public) strategy i j)) ≤
      foldError (config p) (estimates (config p)) i := by
  classical
  apply fiber_event_bound (.fold i j)
  intro rest
  exact fiber_bound p lanes root claims strategy i j rest.val

end Whir.CausalFolds
