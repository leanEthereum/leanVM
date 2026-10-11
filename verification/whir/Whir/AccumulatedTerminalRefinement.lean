import Whir.AccumulatedTerminalAlgebra
import Whir.InducedTerminalRefinement
import Whir.InitialTerminalRefinement
import Whir.SuccinctRingGroups

namespace Whir.AccumulatedTerminalRefinement
open Concrete Protocol ArrayLayout TerminalRefinement
open AccumulatedTerminalAlgebra

/-- Saved contexts retain native source data, never a dense weight table. -/
inductive Basis where
  | ood (z : Array E)
  | query (n : Nat) (queries : Array Nat) (lambda : E)
  deriving Repr

def Basis.dense : Basis → Array E
  | .ood z => eqTable z
  | .query n qs lambda => induced n qs (powers lambda qs.size)

def Basis.native : Basis → List E → E
  | .ood z, point => equalityProduct z.toList point
  | .query n qs lambda, point =>
      InducedTerminalRefinement.nativeBasisAt n qs (powers lambda qs.size) point.toArray

def Basis.Shape : Basis → Nat → Prop
  | .ood z, n => z.size = n
  | .query m _ _, n => m = n ∧ m ≤ 64

def Basis.dimension : Basis → Nat
  | .ood z => z.size
  | .query n _ _ => n

theorem Basis.dimension_eq (b : Basis) (n : Nat) (h : b.Shape n) : b.dimension = n := by
  cases b with
  | ood z => exact h
  | query m qs lambda => exact h.1

theorem Basis.size_dense (b : Basis) (n : Nat) (h : b.Shape n) : b.dense.size = 2 ^ n := by
  cases b with
  | ood z => simp only [Basis.dense, size_eqTable]; rw [h]
  | query m qs lambda =>
      simp [Basis.dense, induced, inducedColumns, show m = n from h.1]

theorem Basis.native_eq_mle (b : Basis) (point : List E) (h : b.Shape point.length) :
    b.native point = Concrete.mle b.dense point.toArray := by
  cases b with
  | ood z =>
    exact (mle_eqTable z.toList point (by simpa [Basis.Shape] using h)).symm
  | query n qs lambda =>
    exact InducedTerminalRefinement.nativeBasisAt_eq_mle n qs (powers lambda qs.size) point.toArray
      h.2 (BatchingRefinement.size_powers ..) (by simpa using h.1.symm)

inductive Step where
  | fold (r : E)
  | glue (basis : Basis) (beta : E)
  deriving Repr

def Step.dense : Step → AccumulatedTerminalAlgebra.Step E
  | .fold r => .fold r
  | .glue b beta => .glue b.dense beta

def challenges : List Step → List E
  | [] => []
  | .fold r :: xs => r :: challenges xs
  | .glue _ _ :: xs => challenges xs

def runDense (xs : List Step) (b : Array E) : Array E :=
  AccumulatedTerminalAlgebra.runDense (xs.map Step.dense) b

def Valid : List Step → Nat → Prop
  | [], _ => True
  | .fold _ :: xs, n => Valid xs n
  | .glue b _ :: xs, n => b.Shape ((challenges xs).length + n) ∧ Valid xs n

def contributions (tail : List E) : List Step → E
  | [] => 0
  | .fold _ :: xs => contributions tail xs
  | .glue b beta :: xs => beta * b.native (challenges xs ++ tail) + contributions tail xs

structure Saved where
  risStart : Nat
  basis : Basis
  beta : E
  deriving Repr

def save : List Step → Nat → List Saved
  | [], _ => []
  | .fold _ :: xs, start => save xs (start + 1)
  | .glue b beta :: xs, start => ⟨start, b, beta⟩ :: save xs start

/-- The succinct verifier's logical retained state: challenges plus
native contexts, without any dense weight array. -/
structure SourceState where
  ris : List E
  saved : List Saved
  deriving Repr

def SourceState.step (s : SourceState) : Step → SourceState
  | .fold r => { s with ris := s.ris ++ [r] }
  | .glue b beta => { s with saved := s.saved ++ [⟨s.ris.length, b, beta⟩] }

def record (xs : List Step) (s : SourceState) : SourceState := xs.foldl SourceState.step s

/-- Proves the incremental source append operations produce the exact saved
context construction used by the terminal theorem, from any initial prefix. -/
theorem record_chronology (xs : List Step) (s : SourceState) :
    record xs s = ⟨s.ris ++ challenges xs, s.saved ++ save xs s.ris.length⟩ := by
  induction xs generalizing s with
  | nil => cases s; simp [record, challenges, save]
  | cons x xs ih =>
    change record xs (s.step x) = _
    rw [ih]
    cases x <;> simp [SourceState.step, challenges, save, List.append_assoc]

/-- The point is the unrotated global suffix at the saved `ris_start`.
A terminal residual point is appended exactly once, before dropping the prefix. -/
def nativeSaved (saved : List Saved) (ris tail : List E) : E :=
  (saved.map fun s => s.beta * s.basis.native ((ris ++ tail).drop s.risStart)).sum

theorem save_chronology (xs : List Step) (pre tail : List E) :
    nativeSaved (save xs pre.length) (pre ++ challenges xs) tail = contributions tail xs := by
  induction xs generalizing pre with
  | nil => simp [save, nativeSaved, contributions]
  | cons x xs ih =>
    cases x with
    | fold r =>
      simpa [save, challenges, contributions, List.append_assoc] using ih (pre ++ [r])
    | glue b beta =>
      simp only [save, nativeSaved, List.map_cons, List.sum_cons, challenges, contributions]
      rw [show ((pre ++ challenges xs) ++ tail).drop pre.length = challenges xs ++ tail by
        rw [List.append_assoc, List.drop_left]]
      exact congrArg (beta * b.native (challenges xs ++ tail) + ·) (ih pre)

/-- The saved-context invariant is established by the actual append/fold
chronology, rather than required from the physical verifier's caller. -/
theorem save_valid (xs : List Step) (n start : Nat) (hv : Valid xs n) :
    ∀ s ∈ save xs start,
      start ≤ s.risStart ∧ s.risStart ≤ start + (challenges xs).length ∧
      s.basis.Shape (start + (challenges xs).length + n - s.risStart) := by
  induction xs generalizing start with
  | nil => simp [save]
  | cons x xs ih =>
    cases x with
    | fold r =>
      intro s hs
      obtain ⟨hlo, hhi, hshape⟩ := ih (start + 1) hv s hs
      refine ⟨by omega, by simpa [challenges, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhi, ?_⟩
      simpa [challenges, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hshape
    | glue b beta =>
      intro s hs
      simp only [save, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨Nat.le_refl _, Nat.le_add_right _ _, by simpa [challenges, Nat.add_assoc] using hv.1⟩
      · exact ih start hv.2 s hs

/-- Exact source slice length: ris[start .. start + log_msg_cols - tail.len]
followed by the common terminal point, with no local rotation. -/
theorem saved_suffix (xs : List Step) (pre tail : List E) (hv : Valid xs tail.length)
    (s : Saved) (hs : s ∈ save xs pre.length) :
    ((pre ++ challenges xs) ++ tail).drop s.risStart =
      ((pre ++ challenges xs).drop s.risStart).take (s.basis.dimension - tail.length) ++ tail := by
  obtain ⟨_, hstart, hshape⟩ := save_valid xs tail.length pre.length hv s hs
  have hdim := s.basis.dimension_eq _ hshape
  have hbound : s.risStart ≤ (pre ++ challenges xs).length := by simpa using hstart
  have hlen : s.basis.dimension - tail.length = ((pre ++ challenges xs).drop s.risStart).length := by
    simp only [List.length_drop, List.length_append]
    omega
  rw [hlen, List.take_length]
  exact List.drop_append_of_le_length hbound

theorem nativeSaved_source_slices (xs : List Step) (pre tail : List E)
    (hv : Valid xs tail.length) :
    nativeSaved (save xs pre.length) (pre ++ challenges xs) tail =
      ((save xs pre.length).map fun s => s.beta * s.basis.native
        (((pre ++ challenges xs).drop s.risStart).take (s.basis.dimension - tail.length) ++ tail)).sum := by
  unfold nativeSaved
  congr 1
  apply List.map_congr_left
  intro s hs
  rw [saved_suffix xs pre tail hv s hs]

@[simp] theorem challenges_dense (xs : List Step) :
    AccumulatedTerminalAlgebra.challenges (xs.map Step.dense) = challenges xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [Step.dense, AccumulatedTerminalAlgebra.challenges, challenges, ih]

theorem valid_dense (xs : List Step) (n : Nat) (hv : Valid xs n) :
    AccumulatedTerminalAlgebra.Valid (xs.map Step.dense) n := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    cases x with
    | fold r => exact ih hv
    | glue b beta => exact ⟨by simpa using b.size_dense _ hv.1, ih hv.2⟩

theorem contributions_dense (xs : List Step) (tail : List E) (hv : Valid xs tail.length) :
    AccumulatedTerminalAlgebra.contributions tail (xs.map Step.dense) = contributions tail xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | fold r => exact ih hv
    | glue b beta =>
      simp only [List.map_cons, Step.dense, AccumulatedTerminalAlgebra.contributions,
        challenges_dense, contributions]
      rw [← b.native_eq_mle _ (by simpa using hv.1), ih hv.2]

/-- Full accumulated dense weight equality, including every OOD and every
query contribution; its only hypotheses are actual shape guards. -/
theorem accumulated (xs : List Step) (b : Array E) (tail : List E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length)) (hv : Valid xs tail.length) :
    Concrete.mle (runDense xs b) tail.toArray =
      Concrete.mle b (challenges xs ++ tail).toArray + nativeSaved (save xs 0) (challenges xs) tail := by
  have h := AccumulatedTerminalAlgebra.accumulated (xs.map Step.dense) b tail
    (by simpa using hb) (valid_dense xs _ hv)
  rw [contributions_dense xs tail hv] at h
  rw [← save_chronology xs [] tail] at h
  simpa [runDense] using h

theorem terminal (xs : List Step) (b : Array E)
    (hb : b.size = 2 ^ (challenges xs).length) (hv : Valid xs 0) :
    (runDense xs b)[0]! = Concrete.mle b (challenges xs).toArray +
      nativeSaved (save xs 0) (challenges xs) [] := by
  have h := accumulated xs b [] (by simpa using hb) hv
  rw [mle_empty _ (by simpa [runDense] using
    AccumulatedTerminalAlgebra.runDense_size (xs.map Step.dense) b 0 (by simpa using hb))] at h
  simpa using h

/-- Actual post-fold source chronology: OOD coefficients start at lambda,
then the induced query basis is glued with lambda^(ood_count+1). -/
def oodSteps (oods : Array (Array E)) (lambda : E) : Nat → Nat → List Step
  | 0, _ => []
  | count + 1, start =>
      .glue (.ood oods[start]!) (lambda ^ (start + 1)) :: oodSteps oods lambda count (start + 1)

def levelBatch (n : Nat) (oods : Array (Array E)) (queries : Array Nat) (lambda : E) : List Step :=
  oodSteps oods lambda oods.size 0 ++
    [.glue (.query n queries lambda) (lambda ^ (oods.size + 1))]

def level (folds : Array E) (n : Nat) (oods : Array (Array E))
    (queries : Array Nat) (lambda : E) : List Step :=
  folds.toList.map Step.fold ++ levelBatch n oods queries lambda

@[simp] theorem runDense_nil (b : Array E) : runDense [] b = b := rfl
@[simp] theorem runDense_fold (r : E) (xs : List Step) (b : Array E) :
    runDense (.fold r :: xs) b = runDense xs (foldLow b r) := rfl
@[simp] theorem runDense_glue (w : Basis) (beta : E) (xs : List Step) (b : Array E) :
    runDense (.glue w beta :: xs) b = runDense xs (weightGlue b w.dense beta) := rfl

theorem runDense_append (xs ys : List Step) (b : Array E) :
    runDense (xs ++ ys) b = runDense ys (runDense xs b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [List.cons_append, runDense_fold, runDense_glue, ih]

theorem oodSteps_weight (cs : LevelChallenges) (p : LevelProof)
    (count start : Nat) (s : VerifierState E) :
    runDense (oodSteps cs.oodPoints cs.lambda count start) s.weight =
      (runSteps (oodStep cs p) count start (s, cs.lambda ^ start)).1.weight := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih =>
    simp only [oodSteps, runDense_glue, Basis.dense, runSteps, oodStep]
    rw [pow_succ]
    exact ih (start + 1)
      (s.batch (eqTable cs.oodPoints[start]!) p.oods[start]!.value
        (cs.lambda ^ start * cs.lambda) p.oods[start]!.intro)

theorem oodSteps_scalar (cs : LevelChallenges) (p : LevelProof)
    (count start : Nat) (s : VerifierState E) :
    (runSteps (oodStep cs p) count start (s, cs.lambda ^ start)).2 =
      cs.lambda ^ (start + count) := by
  induction count generalizing start s with
  | zero => simp [runSteps]
  | succ count ih =>
    simp only [runSteps, oodStep]
    rw [← pow_succ, ih]
    congr 1
    omega

/-- Exactly the weight projection of Protocol's real OOD loop followed by its
query batch, including the scalar carried by that loop. -/
theorem levelBatch_weight (n i : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : VerifierState E) (h : p.oods.size = cs.oodPoints.size) :
    runDense (levelBatch n cs.oodPoints qs cs.lambda) s.weight =
      (queryBatch n i cs p qs (oodBatch cs p s)).weight := by
  rw [levelBatch, runDense_append, runDense_glue, runDense_nil]
  have hw := oodSteps_weight cs p cs.oodPoints.size 0 s
  have hs := oodSteps_scalar cs p cs.oodPoints.size 0 s
  simp only [pow_zero, Nat.zero_add] at hw hs
  change (runSteps (oodStep cs p) cs.oodPoints.size 0 (s, E.one)).2 =
    cs.lambda ^ cs.oodPoints.size at hs
  simp only [queryBatch, oodBatch, h, VerifierState.batch, Basis.dense]
  rw [hw, hs, pow_succ]
  rfl

theorem runDense_folds (rs : List E) (b : Array E) :
    runDense (rs.map Step.fold) b = rs.foldl foldLow b := by
  induction rs generalizing b with
  | nil => rfl
  | cons r rs ih => exact ih (foldLow b r)

theorem foldSteps_weight (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (count start : Nat) (s : CheckedState) :
    (runSteps (foldStep block cs p) count start s).state.weight =
      (List.range' start count).foldl (fun b j => foldValues b block cs.folds[j]!) s.state.weight := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih =>
    simp only [runSteps, List.range'_succ, List.foldl_cons]
    exact ih (start + 1) (foldStep block cs p start s)

/-- The real indexed Protocol loop, not an assumed evaluator identity. -/
theorem foldBlock_weight (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (s : CheckedState) :
    (foldBlock block cs p s).state.weight =
      cs.folds.foldl (fun b r => foldValues b block r) s.state.weight := by
  have mapped : (List.range cs.folds.size).map (fun i => cs.folds[i]!) = cs.folds.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      simp only [getElem!_pos cs.folds i (by simpa using hi')]
  rw [foldBlock, foldSteps_weight, ← List.range_eq_range', ← List.foldl_map,
    mapped, Array.foldl_toList]

theorem foldBlock_weight_lane (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (s : CheckedState) :
    (foldBlock block cs p s).state.weight =
      cs.folds.foldl (fun b r => foldLane b block r) s.state.weight := by
  rw [foldBlock_weight]
  congr 1
  funext b r
  simp only [foldValues]
  split <;> rename_i h
  · have he : block = 1 := by simpa using h
    subst block
    exact (foldLane_one ..).symm
  · rfl

theorem level_weight (n i : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : CheckedState) (h : p.oods.size = cs.oodPoints.size) :
    runDense (level cs.folds n cs.oodPoints qs cs.lambda) s.state.weight =
      (queryBatch n i cs p qs (oodBatch cs p (foldBlock 1 cs p s).state)).weight := by
  rw [level, runDense_append, runDense_folds, Array.foldl_toList]
  have hf := foldBlock_weight 1 cs p s
  simp only [foldValues, BEq.rfl, ↓reduceIte] at hf
  rw [← hf]
  exact levelBatch_weight n i cs p qs _ h

@[simp] theorem challenges_append (xs ys : List Step) :
    challenges (xs ++ ys) = challenges xs ++ challenges ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [challenges, ih]

@[simp] theorem challenges_folds (rs : List E) :
    challenges (rs.map Step.fold) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [challenges, ih]

@[simp] theorem challenges_oodSteps (oods : Array (Array E)) (lambda : E) (count start : Nat) :
    challenges (oodSteps oods lambda count start) = [] := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => exact ih (start + 1)

@[simp] theorem challenges_levelBatch (n : Nat) (oods : Array (Array E))
    (qs : Array Nat) (lambda : E) : challenges (levelBatch n oods qs lambda) = [] := by
  simp [levelBatch, challenges]

@[simp] theorem challenges_level (folds : Array E) (n : Nat) (oods : Array (Array E))
    (qs : Array Nat) (lambda : E) : challenges (level folds n oods qs lambda) = folds.toList := by
  simp [level]

theorem valid_append (xs ys : List Step) (n : Nat) :
    Valid (xs ++ ys) n ↔ Valid xs ((challenges ys).length + n) ∧ Valid ys n := by
  induction xs with
  | nil => simp [Valid]
  | cons x xs ih =>
    cases x <;> simp [Valid, ih, List.length_append, Nat.add_assoc, and_assoc]

theorem valid_oodSteps (oods : Array (Array E)) (lambda : E) (count start n : Nat)
    (bound : start + count ≤ oods.size)
    (shape : ∀ j, start ≤ j → j < start + count → oods[j]!.size = n) :
    Valid (oodSteps oods lambda count start) n := by
  induction count generalizing start with
  | zero => trivial
  | succ count ih =>
    constructor
    · simpa [Basis.Shape] using shape start (by omega) (by omega)
    · exact ih (start + 1) (by omega) (by intro j hj hj'; exact shape j (by omega) (by omega))

theorem valid_levelBatch (n : Nat) (oods : Array (Array E)) (qs : Array Nat) (lambda : E)
    (hn : n ≤ 64) (ho : ∀ j < oods.size, oods[j]!.size = n) :
    Valid (levelBatch n oods qs lambda) n := by
  rw [levelBatch, valid_append]
  constructor
  · simpa [challenges] using valid_oodSteps oods lambda oods.size 0 n
      (by omega) (by intro j _ hj; exact ho j (by omega))
  · exact ⟨⟨by simp [challenges], hn⟩, trivial⟩

theorem valid_folds (rs : List E) (n : Nat) : Valid (rs.map Step.fold) n := by
  induction rs with
  | nil => trivial
  | cons r rs ih => exact ih

/-- Source-local dimension guards suffice; callers do not supply a saved-context
invariant or a terminal-evaluator equality. -/
theorem valid_level (folds : Array E) (n : Nat) (oods : Array (Array E))
    (qs : Array Nat) (lambda : E) (hn : n ≤ 64)
    (ho : ∀ j < oods.size, oods[j]!.size = n) :
    Valid (level folds n oods qs lambda) n := by
  rw [level, valid_append]
  exact ⟨valid_folds _ _, valid_levelBatch n oods qs lambda hn ho⟩

theorem save_folds (rs : List E) (xs : List Step) (start : Nat) :
    save (rs.map Step.fold ++ xs) start = save xs (start + rs.length) := by
  induction rs generalizing start with
  | nil => simp
  | cons r rs ih =>
    simpa [save, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (start + 1)

/-- ris_start is captured after, not before, the current level's folds. -/
theorem save_level (folds : Array E) (n : Nat) (oods : Array (Array E))
    (qs : Array Nat) (lambda : E) (start : Nat) :
    save (level folds n oods qs lambda) start =
      save (levelBatch n oods qs lambda) (start + folds.size) := by
  simpa [level] using save_folds folds.toList (levelBatch n oods qs lambda) start

/-- Dense residual polynomial contributes one MLE, not one copy per context. -/
def nativeTerminal (caller : E) (saved : List Saved) (ris tail : List E) (residual : Array E) : E :=
  Concrete.mle residual tail.toArray * (caller + nativeSaved saved ris tail)

theorem residual_terminal (xs : List Step) (b residual : Array E) (tail : List E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length)) (hv : Valid xs tail.length) :
    Concrete.mle residual tail.toArray * Concrete.mle (runDense xs b) tail.toArray =
      nativeTerminal (Concrete.mle b (challenges xs ++ tail).toArray)
        (save xs 0) (challenges xs) tail residual := by
  rw [accumulated xs b tail hb hv]
  rfl

/-- End-to-end terminal weight after L0's top-variable folds and any number of
later fold/glue transitions. Only the original caller point rotates. Saved
OOD/query contexts retain offsets in the original, unrotated challenge tape. -/
theorem initial_accumulated (initial : Array E) (xs : List Step) (b : Array E)
    (tail : List E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length + initial.size))
    (hv : Valid xs tail.length) :
    Concrete.mle (runDense xs
      (initial.foldl (fun b r => foldLane b (2 ^ ((challenges xs).length + tail.length)) r) b))
      tail.toArray =
    Concrete.mle b (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)) +
      nativeSaved (save xs initial.size) (initial.toList ++ challenges xs) tail := by
  let low := (challenges xs ++ tail).toArray
  have hl : low.size = (challenges xs).length + tail.length := by simp [low]
  have hshape : (initial.foldl (fun b r => foldLane b (2 ^ low.size) r) b).size =
      2 ^ low.size := by
    rw [QueryRefinement.foldLane_blocks b initial (2 ^ low.size)
      (by rw [hb, ← hl, pow_add, Nat.mul_comm])]
    simp
  have h := accumulated xs
    (initial.foldl (fun b r => foldLane b (2 ^ low.size) r) b) tail
    (by simpa [hl] using hshape) hv
  rw [InitialTerminalRefinement.mle_foldLane_initial b initial low (by simpa [hl] using hb)] at h
  rw [InitialTerminalRefinement.rotate_initial]
  have hsave := save_chronology xs initial.toList tail
  have hzero := save_chronology xs [] tail
  simp only [Array.length_toList] at hsave
  simp only [List.length_nil, List.nil_append] at hzero
  rw [hsave]
  rw [hzero] at h
  simpa [low] using h

theorem initial_residual_terminal (initial : Array E) (xs : List Step)
    (b residual : Array E) (tail : List E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length + initial.size))
    (hv : Valid xs tail.length) :
    Concrete.mle residual tail.toArray *
      Concrete.mle (runDense xs
        (initial.foldl (fun b r => foldLane b (2 ^ ((challenges xs).length + tail.length)) r) b))
        tail.toArray =
    nativeTerminal
      (Concrete.mle b (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)))
      (save xs initial.size) (initial.toList ++ challenges xs) tail residual := by
  rw [initial_accumulated initial xs b tail hb hv]
  rfl

/-- Exactly the source per-context point construction, before either of the
two native context loops evaluates its term. -/
def Saved.sourcePoint (s : Saved) (ris tail : List E) : List E :=
  (ris.drop s.risStart).take (s.basis.dimension - tail.length) ++ tail

def Saved.queryTerm (s : Saved) (ris tail : List E) : E :=
  match s.basis with
  | .query n qs lambda =>
      s.beta * InducedTerminalRefinement.nativeBasisAt n qs (powers lambda qs.size)
        (s.sourcePoint ris tail).toArray
  | .ood _ => 0

def Saved.oodTerm (s : Saved) (ris tail : List E) : E :=
  match s.basis with
  | .ood z => s.beta * equalityProduct z.toList (s.sourcePoint ris tail)
  | .query _ _ _ => 0

/-- verify.rs evaluates all LevelCtx terms, then all OodCtx terms, adds the
original caller once, and multiplies by the single residual-polynomial MLE. -/
def sourceTerminal (caller : E) (saved : List Saved) (ris tail : List E) (residual : Array E) : E :=
  ((saved.map (fun s => s.queryTerm ris tail)).sum +
    (saved.map (fun s => s.oodTerm ris tail)).sum + caller) *
    Concrete.mle residual tail.toArray

theorem source_terms (saved : List Saved) (ris tail : List E) :
    (saved.map (fun s => s.beta * s.basis.native (s.sourcePoint ris tail))).sum =
      (saved.map (fun s => s.queryTerm ris tail)).sum +
        (saved.map (fun s => s.oodTerm ris tail)).sum := by
  induction saved with
  | nil => simp
  | cons s saved ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have ht : s.beta * s.basis.native (s.sourcePoint ris tail) =
        s.queryTerm ris tail + s.oodTerm ris tail := by
      cases h : s.basis <;> simp [Saved.queryTerm, Saved.oodTerm, h, Basis.native]
    rw [ht]
    ac_rfl

theorem nativeTerminal_eq_sourceTerminal (caller : E) (xs : List Step)
    (pre tail : List E) (residual : Array E) (hv : Valid xs tail.length) :
    nativeTerminal caller (save xs pre.length) (pre ++ challenges xs) tail residual =
      sourceTerminal caller (save xs pre.length) (pre ++ challenges xs) tail residual := by
  unfold nativeTerminal
  rw [nativeSaved_source_slices xs pre tail hv]
  change Concrete.mle residual tail.toArray *
    (caller + ((save xs pre.length).map fun s =>
      s.beta * s.basis.native (s.sourcePoint (pre ++ challenges xs) tail)).sum) = _
  rw [source_terms]
  unfold sourceTerminal
  ring

theorem initial_source_terminal (initial : Array E) (xs : List Step)
    (b residual : Array E) (tail : List E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length + initial.size))
    (hv : Valid xs tail.length) :
    Concrete.mle residual tail.toArray *
      Concrete.mle (runDense xs
        (initial.foldl (fun b r => foldLane b (2 ^ ((challenges xs).length + tail.length)) r) b))
        tail.toArray =
    sourceTerminal
      (Concrete.mle b (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)))
      (save xs initial.size) (initial.toList ++ challenges xs) tail residual := by
  rw [initial_residual_terminal initial xs b residual tail hb hv]
  simpa only [Array.length_toList] using nativeTerminal_eq_sourceTerminal
    (Concrete.mle b (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)))
    xs initial.toList tail residual hv

theorem source_terminal_acceptance (initial : Array E) (xs : List Step)
    (b residual : Array E) (tail : List E) (claim : E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length + initial.size))
    (hv : Valid xs tail.length) :
    (claim == sourceTerminal
      (Concrete.mle b (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)))
      (record xs ⟨initial.toList, []⟩).saved
      (record xs ⟨initial.toList, []⟩).ris tail residual) =
    (claim == Concrete.mle residual tail.toArray *
      Concrete.mle (runDense xs
        (initial.foldl (fun b r => foldLane b (2 ^ ((challenges xs).length + tail.length)) r) b))
        tail.toArray) := by
  rw [record_chronology]
  simp only [List.nil_append, Array.length_toList]
  rw [initial_source_terminal initial xs b residual tail hb hv]

/-- The dense terminal array includes the actual adjacent-pair tail folds. -/
def terminalWeight (initial : Array E) (xs : List Step) (b : Array E) (tail : List E) : Array E :=
  tail.toArray.foldl foldLow (runDense xs
    (initial.foldl (fun b r => foldLane b (2 ^ ((challenges xs).length + tail.length)) r) b))

theorem before_tail_size (initial : Array E) (xs : List Step) (b : Array E) (tail : List E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length + initial.size)) :
    (runDense xs
      (initial.foldl (fun b r => foldLane b (2 ^ ((challenges xs).length + tail.length)) r) b)).size =
        2 ^ tail.length := by
  apply AccumulatedTerminalAlgebra.runDense_size (xs.map Step.dense)
  rw [QueryRefinement.foldLane_blocks b initial (2 ^ ((challenges xs).length + tail.length))
    (by rw [hb, pow_add, Nat.mul_comm])]
  simp

theorem initial_source_terminal_folds (initial : Array E) (xs : List Step)
    (b residual : Array E) (tail : List E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length + initial.size))
    (hv : Valid xs tail.length) :
    Concrete.mle residual tail.toArray * (terminalWeight initial xs b tail)[0]! =
      sourceTerminal
        (Concrete.mle b (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)))
        (save xs initial.size) (initial.toList ++ challenges xs) tail residual := by
  unfold terminalWeight
  rw [← mle_eq_foldLow_terminal _ tail.toArray
    (by simpa using before_tail_size initial xs b tail hb)]
  exact initial_source_terminal initial xs b residual tail hb hv

/-- The dense Protocol terminal predicate and the native source scalar
predicate are the same Boolean, for arbitrary adversarial claim/message. -/
theorem checkTerminal_source (initial : Array E) (xs : List Step)
    (b residual : Array E) (tail : List E) (claim : E) (message : Message E)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length + initial.size))
    (hv : Valid xs tail.length) :
    (VerifierState.mk (terminalWeight initial xs b tail) claim message).checkTerminal
      (Concrete.mle residual tail.toArray) =
    (claim == sourceTerminal
      (Concrete.mle b (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)))
      (record xs ⟨initial.toList, []⟩).saved
      (record xs ⟨initial.toList, []⟩).ris tail residual) := by
  unfold VerifierState.checkTerminal
  rw [initial_source_terminal_folds initial xs b residual tail hb hv, record_chronology]
  simp

/-- Concrete full caller instantiation: the ring-map family, transformed gamma
weights, and original point claims are supplied by the checked succinct caller
formula. No caller-MLE or accumulated-terminal equivalence is a hypothesis. -/
theorem stack_terminal_equivalence {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (initial : Array E) (xs : List Step) (tail : List E) (residual : Array E)
    (familyShape : SuccinctRingWeight.FamilyShape
      ((challenges xs).length + tail.length + initial.size) family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape
      ((challenges xs).length + tail.length + initial.size) points[i])
    (hv : Valid xs tail.length) :
    let n := (challenges xs).length + tail.length + initial.size
    let b := (CausalGame.batchClaims (2 ^ n)
      (RingPCSGame.transformedClaims (2 ^ n) family points seed) lambda).weight
    Concrete.mle residual tail.toArray * (terminalWeight initial xs b tail)[0]! =
      sourceTerminal
        (SuccinctRingGroups.sourceStackWeightAt family points seed lambda
          (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)))
        (save xs initial.size) (initial.toList ++ challenges xs) tail residual := by
  dsimp only
  have hp : (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)).size =
      (challenges xs).length + tail.length + initial.size := by
    simp [Nat.add_comm]
  rw [SuccinctRingGroups.sourceStackWeightAt_eq_batch_mle family points seed lambda _
    (by simpa only [hp] using familyShape) (by simpa only [hp] using pointShapes)]
  simp only [hp]
  exact initial_source_terminal_folds initial xs _ residual tail
    (InitialBatching.batchClaims_size ..) hv

/-- Consumable by the physical scalar verifier: its exact native terminal
comparison and Protocol's actual terminal predicate are equal Booleans, with
the entire original caller stack concretely instantiated. -/
theorem stack_checkTerminal_source {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (initial : Array E) (xs : List Step) (tail : List E) (residual : Array E)
    (claim : E) (message : Message E)
    (familyShape : SuccinctRingWeight.FamilyShape
      ((challenges xs).length + tail.length + initial.size) family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape
      ((challenges xs).length + tail.length + initial.size) points[i])
    (hv : Valid xs tail.length) :
    let n := (challenges xs).length + tail.length + initial.size
    let b := (CausalGame.batchClaims (2 ^ n)
      (RingPCSGame.transformedClaims (2 ^ n) family points seed) lambda).weight
    (VerifierState.mk (terminalWeight initial xs b tail) claim message).checkTerminal
      (Concrete.mle residual tail.toArray) =
    (claim == sourceTerminal
      (SuccinctRingGroups.sourceStackWeightAt family points seed lambda
        (rotatePoint initial.size (initial ++ (challenges xs ++ tail).toArray)))
      (record xs ⟨initial.toList, []⟩).saved
      (record xs ⟨initial.toList, []⟩).ris tail residual) := by
  dsimp only
  unfold VerifierState.checkTerminal
  rw [stack_terminal_equivalence family points seed lambda initial xs tail residual
    familyShape pointShapes hv, record_chronology]
  simp

end Whir.AccumulatedTerminalRefinement
