import Whir.CausalTerminal
import Whir.OracleReplay
import Whir.BatchingRefinement

/-! Total projections of the actual operational kernels make each finite
challenge-prefix event explicit. Successful checked execution is proved to
coincide with these projections; totalization never changes acceptance. -/
namespace Whir.CausalExecution
open Concrete Protocol CausalGame OperationalRefinement

abbrev proof := CausalTerminal.proof

def initial (input : Public) (strategy : Strategy) (tape : Tape input.config) : CheckedState :=
  let batched := batchClaims (2 ^ input.config.logN) input.claims tape.1
  ⟨input.config.logN, ⟨batched.weight, batched.value, (proof input strategy tape).initial⟩,
    liftRoot input.root⟩

def block (c : Config) (i : Nat) : Nat :=
  if i == 0 then 2 ^ (c.logN - c.folds[0]!) else 1

/-- Only the actual verifier's fold and batching kernels are evaluated. -/
def next (c : Config) (ch : Challenges) (p : Opening) (i : Nat) (s : CheckedState) : CheckedState :=
  let cs := ch.levels[i]!
  let level := p.levels[i]!
  let folded := Protocol.foldBlock (block c i) cs level s
  let qs := (deriveQueries (folded.n + c.rates[i]!) c.queries[i]! cs.querySqueezes).getD #[]
  ⟨folded.n, queryBatch folded.n i cs level qs (oodBatch cs level folded.state),
    level.nextOracle.getD #[]⟩

def levelAt (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Nat) : CheckedState :=
  runSteps (next input.config (challenges input.config tape) (proof input strategy tape))
    i 0 (initial input strategy tape)

def foldAt (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i j : Nat) : CheckedState :=
  let ch := challenges input.config tape
  let p := proof input strategy tape
  runSteps (foldStep (block input.config i) ch.levels[i]! p.levels[i]!)
    j 0 (levelAt input strategy tape i)

noncomputable def foldCandidates (input : Public) (strategy : Strategy)
    (tape : Tape input.config) (i j : Nat) : Finset (Array E) :=
  CandidateFolding.arrayCandidates (i == 0)
    (CandidateFolding.concreteEncoder (remaining input.config i) input.config.rates[i]!)
    (OracleReplay.oracleAt (i == 0) input.config.folds[i]!
      (levelAt input strategy tape i).oracle (challenges input.config tape).levels[i]!.folds j)
    (ParameterBounds.threshold input.config i)

/-- The next candidate set uses the boundary commitment, before OOD/query
challenges. The last level instead has the transmitted singleton residual. -/
noncomputable def followingCandidates (input : Public) (strategy : Strategy)
    (tape : Tape input.config) (i : Nat) : Finset (Array E) :=
  if i + 1 < input.config.folds.size then
    CandidateFolding.arrayCandidates false
      (CandidateFolding.concreteEncoder (remaining input.config (i + 1))
        input.config.rates[i + 1]!)
      (OracleReplay.oracleAt false input.config.folds[i + 1]!
        ((proof input strategy tape).levels[i]!.nextOracle.getD #[])
        (challenges input.config tape).levels[i + 1]!.folds 0)
      (ParameterBounds.threshold input.config (i + 1))
  else {(proof input strategy tape).residual}

@[simp] theorem levelAt_zero (input : Public) (strategy : Strategy) (tape : Tape input.config) :
    levelAt input strategy tape 0 = initial input strategy tape := rfl

@[simp] theorem foldAt_zero (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Nat) : foldAt input strategy tape i 0 = levelAt input strategy tape i := rfl

theorem levelAt_succ (input : Public) (strategy : Strategy) (tape : Tape input.config) (i : Nat) :
    levelAt input strategy tape (i + 1) =
      next input.config (challenges input.config tape) (proof input strategy tape) i
        (levelAt input strategy tape i) :=
  BatchingRefinement.runSteps_succ_last _ i _

theorem foldAt_succ (input : Public) (strategy : Strategy) (tape : Tape input.config) (i j : Nat) :
    foldAt input strategy tape i (j + 1) =
      foldStep (block input.config i) (challenges input.config tape).levels[i]!
        (proof input strategy tape).levels[i]! j (foldAt input strategy tape i j) :=
  BatchingRefinement.runSteps_succ_last _ j _

/-- Every accepted actual level has exactly the total kernel result. -/
theorem next_of_success (c : Config) (ch : Challenges) (p : Opening)
    (i : Nat) (s finish : CheckedState) (h : verifyLevel c ch p i s = .ok finish) :
    next c ch p i s = finish := by
  obtain ⟨_, _, qs, sampled, _, _, result⟩ := verifyLevel_success c ch p i s finish h
  unfold next block
  dsimp only
  rw [sampled]
  exact result.symm

private theorem except_pure {S : Type*} (s : S) :
    (pure s : Except String S) = .ok s := rfl
private theorem except_bind_ok {S T : Type u} (s : S) (f : S → Except String T) :
    (Except.ok s >>= f) = f s := rfl
private theorem except_bind_error {S T : Type u} (e : String) (f : S → Except String T) :
    (Except.error e >>= f) = .error e := rfl
private theorem except_throw {S : Type*} (e : String) :
    (throw e : Except String S) = .error e := rfl
attribute [local simp] except_pure except_bind_ok except_bind_error except_throw

/-- Actual initialization both validates the public shape and fixes the state. -/
theorem initialize_success (c : Config) (ch : Challenges) (lanes : Nat) (root : Oracle)
    (weight : Array E) (target : E) (p : Opening) (s : CheckedState)
    (h : initializeVerifier c ch lanes root weight target p = .ok s) :
    shapeValid c lanes weight = true ∧
      oracleValid root (2 ^ (c.logN - c.folds[0]! + c.rates[0]!)) lanes = true ∧
      s = ⟨c.logN, ⟨weight, target, p.initial⟩, root⟩ := by
  unfold initializeVerifier at h
  simp only [except_throw, except_pure, except_bind_error] at h
  split_ifs at h
  simp_all

/-- Checked recursion agrees with total recursion along every successful path. -/
theorem runSteps_of_success {S : Type*} (checked : Nat → S → Except String S)
    (total : Nat → S → S) (agrees : ∀ i s t, checked i s = .ok t → total i s = t)
    (count start : Nat) (s finish : S)
    (h : runChecked checked count start s = .ok finish) :
    runSteps total count start s = finish := by
  induction count generalizing start s with
  | zero => simpa [runChecked, runSteps] using h
  | succ count ih =>
    cases step : checked start s with
    | error e => simp [runChecked, step] at h
    | ok after =>
      have rest : runChecked checked count (start + 1) after = .ok finish := by
        simpa [runChecked, step] using h
      simpa only [runSteps, agrees start s after step] using ih (start + 1) after rest

/-- Every accepted execution visits exactly the exposed total level states. -/
theorem accepted_execution (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (accepted : experiment input strategy tape = true) :
    initializeVerifier input.config (challenges input.config tape) input.lanes
      (liftRoot input.root) (batchClaims (2 ^ input.config.logN) input.claims tape.1).weight
      (batchClaims (2 ^ input.config.logN) input.claims tape.1).value
      (proof input strategy tape) = .ok (initial input strategy tape) ∧
    replayLevels input.config (challenges input.config tape) (proof input strategy tape)
      (initial input strategy tape) = .ok (levelAt input strategy tape input.config.folds.size) ∧
    (levelAt input strategy tape input.config.folds.size).state =
      CausalTerminal.before input strategy tape := by
  obtain ⟨_, p, first, finish, parsed, initialized, trace, _⟩ :=
    (CausalRefinement.experiment_iff input strategy tape).mp accepted
  have hp : p = proof input strategy tape :=
    CausalRefinement.opening_eq_decoded _ _ _ _ parsed
  subst p
  have hfirst : first = initial input strategy tape :=
    (initialize_success _ _ _ _ _ _ _ _ initialized).2.2
  subst first
  have replay : replayLevels input.config (challenges input.config tape) (proof input strategy tape)
      (initial input strategy tape) = .ok finish :=
    (runChecked_ok_iff_trace _ _ _ _ _).mpr trace
  have hfinish : levelAt input strategy tape input.config.folds.size = finish :=
    runSteps_of_success _ _ (next_of_success input.config (challenges input.config tape)
      (proof input strategy tape)) _ _ _ _ replay
  refine ⟨initialized, ?_, ?_⟩
  · simpa only [hfinish] using replay
  · simp only [CausalTerminal.before, CausalTerminal.beforeChecked, initialized,
      except_bind_ok, replay, Except.toOption, Option.getD, hfinish]

/-- Successful checked execution exposes every prefix transition, not only its final state. -/
theorem runChecked_prefix {S : Type*} (checked : Nat → S → Except String S)
    (total : Nat → S → S) (agrees : ∀ i s t, checked i s = .ok t → total i s = t)
    (count start : Nat) (s finish : S)
    (success : runChecked checked count start s = .ok finish)
    (i : Nat) (hi : i < count) :
    checked (start + i) (runSteps total i start s) =
      .ok (runSteps total (i + 1) start s) := by
  induction count generalizing start s i with
  | zero => omega
  | succ count ih =>
    cases step : checked start s with
    | error e => simp [runChecked, step] at success
    | ok after =>
      have rest : runChecked checked count (start + 1) after = .ok finish := by
        simpa [runChecked, step] using success
      have totalStep := agrees start s after step
      cases i with
      | zero => simpa [runSteps, totalStep] using step
      | succ i =>
        simpa only [runSteps, totalStep, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ih (start + 1) after rest i (by omega)

theorem accepted_level (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (accepted : experiment input strategy tape = true) (i : Nat)
    (hi : i < input.config.folds.size) :
    verifyLevel input.config (challenges input.config tape) (proof input strategy tape) i
      (levelAt input strategy tape i) = .ok (levelAt input strategy tape (i + 1)) := by
  have replay := (accepted_execution input strategy tape accepted).2.1
  simpa only [Nat.zero_add, levelAt] using runChecked_prefix _ _
    (next_of_success input.config (challenges input.config tape) (proof input strategy tape))
    input.config.folds.size 0 (initial input strategy tape)
    (levelAt input strategy tape input.config.folds.size) replay i hi

/-- The boundary commitment's list is exactly the next level's incoming list. -/
theorem following_eq_next (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Nat) (hasNext : i + 1 < input.config.folds.size) :
    followingCandidates input strategy tape i = foldCandidates input strategy tape (i + 1) 0 := by
  have base : ((i + 1) == 0) = false := by simp
  simp only [followingCandidates, hasNext, ↓reduceIte, foldCandidates, base, levelAt_succ, next]

/-- The actual level verifier validates its boundary commitment or residual before deriving queries. -/
theorem boundary_shape (c : Config) (ch : Challenges) (p : Opening) (i : Nat)
    (s finish : CheckedState) (success : verifyLevel c ch p i s = .ok finish) :
    let folded := Protocol.foldBlock (block c i) ch.levels[i]! p.levels[i]! s
    if i + 1 < c.folds.size then
      p.levels[i]!.nextOracle.isSome = true ∧
        oracleValid (p.levels[i]!.nextOracle.getD #[])
          (2 ^ (folded.n - c.folds[i + 1]! + c.rates[i + 1]!))
          (2 ^ c.folds[i + 1]!) = true
    else p.levels[i]!.nextOracle = none ∧ p.residual.size = 2 ^ folded.n := by
  dsimp only
  unfold verifyLevel at success
  simp only [except_throw, except_bind_error, except_pure] at success
  generalize hf : Protocol.foldBlock (block c i) ch.levels[i]! p.levels[i]! s = folded at ⊢
  have hf' : Protocol.foldBlock (if i == 0 then 2 ^ (c.logN - c.folds[0]!) else 1)
      ch.levels[i]! p.levels[i]! s = folded := hf
  rw [hf'] at success
  cases hn : p.levels[i]!.nextOracle <;>
    cases hq : deriveQueries (folded.n + c.rates[i]!) c.queries[i]! ch.levels[i]!.querySqueezes
  all_goals
    simp only [hn, hq, Option.elim, except_pure, except_bind_ok, except_bind_error] at success
    split_ifs at success <;> simp_all

end Whir.CausalExecution
