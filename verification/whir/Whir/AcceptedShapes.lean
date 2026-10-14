import Whir.ExecutionShapes
import Whir.LevelBoundary

/-! Actual accepted shape checks connect commitment-fixed candidates to the
operational oracle at every level and to the one-lane close invariant. -/
namespace Whir.AcceptedShapes
open Concrete Protocol CausalGame CausalExecution ExecutionShapes ParameterBounds
open CandidateFolding VerifierInvariant

/-- Even an empty public-claim array is subject to the actual initialized lane guard. -/
theorem accepted_lane_bound (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (accepted : experiment input strategy tape = true) :
    input.lanes ≤ 2 ^ input.config.folds[0]! := by
  have h := (initialize_success _ _ _ _ _ _ _ _
    (accepted_execution input strategy tape accepted).1).1
  simp only [shapeValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1.2

/-- These are the precise immutable leaf lengths checked by the actual verifier. -/
theorem accepted_oracle (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (i : Fin (config p).folds.size) :
    oracleValid (levelAt (Input p lanes root claims) strategy tape i).oracle (length (config p) i)
      (if i.val == 0 then lanes else 2 ^ (config p).folds[i.val]!) = true := by
  by_cases zero : i.val = 0
  · have valid := (initialize_success _ _ _ _ _ _ _ _
      (accepted_execution (Input p lanes root claims) strategy tape accepted).1).2.1
    simpa [zero, initial, length, (InitialCandidates.production_initial_facts p).1]
      using valid
  · let j := i.val - 1
    have ji : j + 1 = i.val := by dsimp [j]; omega
    have hj : j < (config p).folds.size := by omega
    have hnext : j + 1 < (config p).folds.size := by omega
    have checked := accepted_level (Input p lanes root claims) strategy tape accepted j hj
    have boundary := boundary_shape (config p) (challenges (config p) tape)
      (proof (Input p lanes root claims) strategy tape) j _ _ checked
    dsimp only at boundary
    rw [← foldAt_end (Input p lanes root claims) strategy tape j hj] at boundary
    have ended := (foldAt_shape p lanes root claims strategy tape ⟨j, hj⟩
      (config p).folds[j]! le_rfl).1
    simp only [Nat.sub_self, Nat.add_zero] at ended
    rw [ended] at boundary
    simp [ji] at boundary
    rw [← getElem!_pos (config p).folds i.val i.isLt] at boundary
    have dims := production_before p i
    have previous : remaining (config p) j = remaining (config p) i + (config p).folds[i.val]! := by
      rw [← before_succ, ji]
      exact dims
    have subdim : remaining (config p) j - (config p).folds[i.val]! = remaining (config p) i := by omega
    rw [subdim] at boundary
    have oracle : (levelAt (Input p lanes root claims) strategy tape i).oracle =
        (proof (Input p lanes root claims) strategy tape).levels[j]!.nextOracle.getD #[] := by
      rw [← ji, levelAt_succ]
      rfl
    rw [oracle]
    simpa only [show (i.val == 0) = false from by simp [zero], Bool.false_eq_true, ↓reduceIte, length]
      using boundary.2

/-- Reversed base leaves may be pruned; extension leaves have the full configured width. -/
theorem accepted_leaf_bound (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (i : Fin (config p).folds.size) (q : Fin (length (config p) i)) :
    ((levelAt (Input p lanes root claims) strategy tape i).oracle[q.val]!).size ≤
      2 ^ (config p).folds[i.val]! := by
  have shape := OracleReplay.oracleValid_row _ _ _
    (accepted_oracle p lanes root claims strategy tape accepted i) q.val q.isLt
  by_cases zero : i.val = 0
  · have bound := accepted_lane_bound (Input p lanes root claims) strategy tape accepted
    have live : ((levelAt (Input p lanes root claims) strategy tape i).oracle[q.val]!).size = lanes := by
      simpa [zero] using shape
    simpa only [zero] using live.le.trans bound
  · simpa only [show (i.val == 0) = false from by simp [zero], Bool.false_eq_true, ↓reduceIte]
      using shape.le

/-- A completed arbitrary-oracle fold is exactly the singleton-row oracle used by the query kernel. -/
theorem terminal_candidates (base : Bool) (k n rate threshold : Nat) (root : Oracle)
    (folds : Array E) (count : folds.size = k)
    (live : ∀ q : Fin (2 ^ (n + rate)), root[q.val]!.size ≤ 2 ^ k) :
    arrayCandidates base (concreteEncoder n rate) (OracleReplay.oracleAt base k root folds k) threshold =
      arrayCandidates base (concreteEncoder n rate)
        (fun _ : Fin 1 => fun q => OracleReplay.postfoldWord base root folds q.val) threshold := by
  subst k
  have cast : 1 = 2 ^ (folds.size - folds.size) := by simp
  have reindex := OracleReplay.arrayCandidates_cast cast base (concreteEncoder n rate)
    (OracleReplay.oracleAt base folds.size root folds folds.size) threshold
  have columns : (fun lane : Fin 1 => OracleReplay.oracleAt base folds.size root folds folds.size
      (Fin.cast cast lane)) = (fun _ : Fin 1 => fun q : Fin (2 ^ (n + rate)) =>
        OracleReplay.postfoldWord base root folds q.val) := by
    funext lane q
    exact OracleReplay.oracleAt_terminal base root folds q (live q) (Fin.cast cast lane)
  rw [columns] at reindex
  exact reindex.symm

/-- Accepted physical layouts discharge the exact close-invariant premise used by the query theorem. -/
theorem closeLost_of_terminal_lost (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (i : Fin (config p).folds.size)
    (lost : Lost (foldCandidates (Input p lanes root claims) strategy tape i (config p).folds[i.val]!)
      (foldAt (Input p lanes root claims) strategy tape i (config p).folds[i.val]!).state) :
    LevelBoundary.CloseLost (remaining (config p) i) (config p).rates[i.val]!
      (threshold (config p) i)
      (fun q => OracleReplay.postfoldWord (i.val == 0)
        (levelAt (Input p lanes root claims) strategy tape i).oracle
        (challenges (config p) tape).levels[i.val]!.folds q.val)
      (foldAt (Input p lanes root claims) strategy tape i (config p).folds[i.val]!).state := by
  unfold foldCandidates at lost
  rw [terminal_candidates _ _ _ _ _ _ _ (TapeValidity.level_shapes _ tape i i.isLt).1
    (accepted_leaf_bound p lanes root claims strategy tape accepted i)] at lost
  exact LevelBoundary.closeLost_of_lost (i.val == 0) _ _ _ _ _ lost

/-- The initial operational list is literally the commitment-fixed extension list, including pruned base lanes. -/
theorem initial_candidates (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p))
    (valid : oracleValid (liftRoot root) (length (config p) 0) lanes = true) :
    foldCandidates (Input p lanes root claims) strategy tape 0 0 =
      InitialCandidates.extensionCandidates (config p) lanes root := by
  have remaining0 := (InitialCandidates.production_initial_facts p).1
  have rootSize : root.size = length (config p) 0 := by
    have h := valid
    simp only [oracleValid, Bool.and_eq_true, beq_iff_eq] at h
    simpa [liftRoot] using h.1
  change arrayCandidates true (concreteEncoder (remaining (config p) 0) (config p).rates[0]!)
    (OracleReplay.oracleAt true (config p).folds[0]! (liftRoot root)
      (challenges (config p) tape).levels[0]!.folds 0) (threshold (config p) 0) = _
  rw [remaining0]
  unfold InitialCandidates.extensionCandidates
  congr 1
  funext lane q
  have hq : q.val < root.size := by
    rw [rootSize]
    simpa only [length, remaining0] using q.isLt
  have hrow := OracleReplay.oracleValid_row (liftRoot root) (length (config p) 0) lanes valid
    q.val (by simpa only [← rootSize] using hq)
  have shape : root[q.val]!.size = lanes := by
    simpa [liftRoot, getElem!_pos, hq] using hrow
  exact OracleReplay.initial_fullRow (config p) lanes root
    (challenges (config p) tape).levels[0]!.folds q hq shape lane

end Whir.AcceptedShapes
