import Whir.InitialKnowledgeSchedule

/-! The actual causal six-fold trajectory instantiates the typed generic
SafeClaimFoldSchedule. All reindexings preserve physical coefficient order. -/
namespace Whir.InitialKnowledgeSchedule
open Concrete Protocol CausalGame CausalExecution ExecutionShapes CausalProbability
open CandidateFolding SupportedCandidateExtraction ParameterBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

private theorem cast_schedule_start {k N start start' finish : Nat}
    (h : start' = start) (top : Bool) (enc : (Fin k → E) →ₗ[E] (Fin N → E))
    (C : Submodule E (Fin N → E)) (threshold : Nat)
    (oracle : Fin start → Fin N → E) (last : Fin finish → Fin N → E)
    (state endState : VerifierState E) (transform : Array E → Array E)
    (schedule : SafeClaimFoldSchedule top enc C threshold oracle last state endState transform) :
    SafeClaimFoldSchedule top enc C threshold (fun lane : Fin start' => oracle (Fin.cast h lane))
      last state endState transform := by
  subst start'
  exact schedule

noncomputable def matrix (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i : Fin input.config.folds.size) (j : Nat) :=
  OracleReplay.oracleAt (i.val == 0) input.config.folds[i.val]!
    (levelAt input strategy t i).oracle (challenges input.config t).levels[i.val]!.folds j
    (N := length input.config i)

/-- No abstract schedule is assumed: actual causal states, messages and oracle
matrices build it from the two incoming-prefix scalar exclusions. -/
theorem actual_safe_claim_schedule (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (i : Fin (config p).folds.size) (start count : Nat)
    (bound : start+count ≤ (config p).folds[i.val]!)
    (mca : ∀ j : Fin (config p).folds[i.val]!, ¬ RawMCA (Input p lanes root claims) strategy i j t)
    (guard : ∀ j : Fin (config p).folds[i.val]!, ¬ ClaimEscape (Input p lanes root claims) strategy i j t) :
    SafeClaimFoldSchedule (i.val == 0)
      (concreteEncoder (remaining (config p) i) (config p).rates[i.val]!)
      (LinearMap.range (concreteEncoder (remaining (config p) i) (config p).rates[i.val]!))
      (threshold (config p) i)
      (matrix (Input p lanes root claims) strategy t i start)
      (matrix (Input p lanes root claims) strategy t i (start+count))
      (foldAt (Input p lanes root claims) strategy t i start).state
      (foldAt (Input p lanes root claims) strategy t i (start+count)).state
      (foldFrom (Input p lanes root claims) t i start count) := by
  induction count generalizing start with
  | zero => exact SafeClaimFoldSchedule.done _ _
  | succ count ih =>
    let input := Input p lanes root claims
    let j : Fin (config p).folds[i.val]! := ⟨start, by omega⟩
    have rest := ih (start+1) (by omega)
    have endIndex : start+1+count = start+(count+1) := by omega
    rw [endIndex] at rest
    unfold matrix at rest
    rw [OracleReplay.oracleAt_succ _ _ _ _ start j.isLt, foldAt_succ] at rest
    simp only [foldStep, CausalFolds.block_eq] at rest
    have weight : (foldAt input strategy t i start).state.weight.size =
        (2 ^ (input.config.folds[i.val]! - (start+1)) * 2) * dimension input.config i := by
      rw [(foldAt_shape p lanes root claims strategy t i start (by omega)).2]
      rw [← CausalFolds.pair_width _ _ j.isLt, dimension, ← Nat.pow_add, Nat.add_comm]
    have claimSafe : (challenges input.config t).levels[i.val]!.folds[start]! ∉
        candidateRoundEscape (arrayCandidates (i.val == 0)
          (concreteEncoder (remaining input.config i) input.config.rates[i.val]!)
          (paired input strategy t i j) (threshold input.config i))
          (foldAt input strategy t i start).state (CandidateFolding.foldBlock (i.val == 0) (dimension input.config i)) := by
      unfold paired
      rw [OracleReplay.paired_candidates]
      simpa only [ClaimEscape, foldCandidates, CausalFolds.block_eq, j] using guard j
    have schedule := SafeClaimFoldSchedule.step (paired input strategy t i j)
      (foldAt input strategy t i start).state (challenges input.config t).levels[i.val]!.folds[start]!
      (proof input strategy t).levels[i.val]!.afterFold[start]! weight (mca j) claimSafe rest
    have width := CausalFolds.pair_width input.config.folds[i.val]! start j.isLt
    have cast := cast_schedule_start width (i.val == 0) _ _ _ _ _ _ _ _ schedule
    have oracle : (fun lane : Fin (2 ^ (input.config.folds[i.val]! - start)) =>
        paired input strategy t i j (Fin.cast width lane)) = matrix input strategy t i start := by
      funext lane q
      rfl
    rw [oracle] at cast
    have transform : (fun a => foldFrom input t i (start+1) count
        (foldValues a (CandidateFolding.foldBlock (i.val == 0) (dimension input.config i))
          (challenges input.config t).levels[i.val]!.folds[start]!)) = foldFrom input t i start (count+1) := by
      funext a
      rw [foldFrom_succ, CausalFolds.block_eq]
    rw [transform] at cast
    exact cast

#print axioms actual_safe_claim_schedule
end Whir.InitialKnowledgeSchedule
