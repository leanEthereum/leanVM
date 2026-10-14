import Whir.CausalExecution
import Whir.InitialSoundness
import Whir.ProductionTransitions

/-! Dimensions of total actual execution, including malformed prover messages.
Message values never determine weight lengths or the configured fold ladder. -/
namespace Whir.ExecutionShapes
open Concrete Protocol CausalGame CausalExecution ParameterBounds

abbrev Input (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim) : Public :=
  ⟨config p, lanes, root, claims⟩

def before (c : Config) (i : Nat) : Nat := c.logN - (c.folds.toList.take i).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem production_before : ∀ p : Profile, ∀ i : Fin (config p).folds.size,
    before (config p) i = remaining (config p) i + (config p).folds[i.val]! := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem production_ood_positive : ∀ p : Profile, ∀ i : Fin (config p).folds.size,
    i.val + 1 < (config p).folds.size → 0 < oodCount (config p) i := by
  decide +kernel

@[simp] theorem before_succ (c : Config) (i : Nat) : before c (i + 1) = remaining c i := rfl

@[simp] theorem ood_weight (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E) :
    (oodBatch cs p s).1.weight.size = s.weight.size := by
  have h := OperationalRefinement.runSteps_invariant (oodStep cs p)
    (fun _ pair => pair.1.weight.size = s.weight.size) p.oods.size 0 (s, E.one) rfl
    (by intro i pair _ _ h; simpa [oodStep, VerifierState.batch] using h)
  exact h

@[simp] theorem query_weight (n i : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : VerifierState E × E) :
    (queryBatch n i cs p qs s).weight.size = s.1.weight.size := by
  simp [queryBatch, VerifierState.batch]

theorem next_shape (c : Config) (ch : Challenges) (p : Opening) (i : Nat)
    (s : CheckedState) (n k : Nat) (folds : ch.levels[i]!.folds.size = k)
    (start : s.n = n + k) (weight : s.state.weight.size = 2 ^ (n + k)) :
    (next c ch p i s).n = n ∧ (next c ch p i s).state.weight.size = 2 ^ n := by
  have folded := OracleReplay.foldBlock_prefix_shape (block c i) ch.levels[i]! p.levels[i]!
    s n k k le_rfl start weight
  simp only [Nat.sub_self, Nat.add_zero] at folded
  unfold next Protocol.foldBlock
  dsimp only
  rw [folds]
  exact ⟨folded.1, by simpa only [query_weight, ood_weight] using folded.2⟩

/-- Every configured prefix has its exact expected state and weight dimensions. -/
theorem levelAt_shape (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p)) (i : Nat) (hi : i ≤ (config p).folds.size) :
    (levelAt (Input p lanes root claims) strategy tape i).n = before (config p) i ∧
      (levelAt (Input p lanes root claims) strategy tape i).state.weight.size =
        2 ^ before (config p) i := by
  induction i with
  | zero => simp [initial, before]
  | succ i ih =>
    have index : i < (config p).folds.size := by omega
    have prior := ih (by omega)
    have dims := production_before p ⟨i, index⟩
    have start := prior.1.trans dims
    have weight := prior.2.trans (congrArg (fun n => 2 ^ n) dims)
    rw [levelAt_succ, before_succ]
    exact next_shape _ _ _ i _ (remaining (config p) i) (config p).folds[i]!
      (TapeValidity.level_shapes (config p) tape i index).1 start weight

/-- Each individual actual fold prefix matches the physical candidate array width. -/
theorem foldAt_shape (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p)) (i : Fin (config p).folds.size)
    (j : Nat) (hj : j ≤ (config p).folds[i.val]!) :
    (foldAt (Input p lanes root claims) strategy tape i j).n =
      remaining (config p) i + ((config p).folds[i.val]! - j) ∧
    (foldAt (Input p lanes root claims) strategy tape i j).state.weight.size =
      2 ^ (remaining (config p) i + ((config p).folds[i.val]! - j)) := by
  have prior := levelAt_shape p lanes root claims strategy tape i i.isLt.le
  have dims := production_before p i
  exact OracleReplay.foldBlock_prefix_shape _ _ _ _ _ _ j hj
    (prior.1.trans dims) (prior.2.trans (congrArg (fun n => 2 ^ n) dims))

theorem foldAt_end (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Nat) (hi : i < input.config.folds.size) :
    foldAt input strategy tape i input.config.folds[i]! =
      Protocol.foldBlock (block input.config i) (challenges input.config tape).levels[i]!
        (proof input strategy tape).levels[i]! (levelAt input strategy tape i) := by
  simp only [foldAt, Protocol.foldBlock, (TapeValidity.level_shapes input.config tape i hi).1]

/-- No honest-witness assumption enters candidate and pending-weight shape alignment. -/
theorem candidate_weight_size (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p)) (i : Fin (config p).folds.size)
    (j : Nat) (hj : j ≤ (config p).folds[i.val]!) (a : Array E)
    (ha : a ∈ foldCandidates (Input p lanes root claims) strategy tape i j) :
    (foldAt (Input p lanes root claims) strategy tape i j).state.weight.size = a.size := by
  rw [(foldAt_shape p lanes root claims strategy tape i j hj).2]
  exact (OracleReplay.candidate_size _ _ _ _ _ _ _ _ a ha).symm

/-- No fold changes the oracle against which that level authenticates its rows. -/
theorem foldAt_oracle (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i j : Nat) :
    (foldAt input strategy tape i j).oracle = (levelAt input strategy tape i).oracle := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [foldAt_succ, foldStep] using ih

end Whir.ExecutionShapes
