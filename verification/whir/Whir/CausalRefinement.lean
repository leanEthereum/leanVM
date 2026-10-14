import Whir.TapeValidity
import Whir.OperationalRefinement

/-! Actual causal wire refinement, without an honest-prover relation.
`TapeValidity.challenges_valid` certifies every supplied tape without rejection.
`parsed_*` identifies every opening field with a truncated strategy execution;
`visible_*` identifies those truncations with the precise wire order, including
the indivisible queries-plus-lambda message and the invisible final tail coordinate.
`experiment_iff` exposes actual operational transitions and the concrete closing
check. Together these interfaces permit fresh-challenge counting on arbitrary
accepted messages, without exposing future tape coordinates to the strategy. -/
namespace Whir.CausalRefinement
open Concrete Protocol CausalGame OperationalRefinement

@[simp] theorem levelBatches_length (ch : Challenges) (i : Nat) :
    (levelBatches ch i).length =
      ch.levels[i]!.folds.size + ch.levels[i]!.oodPoints.size + 1 := by
  simp [levelBatches, Nat.add_assoc]

@[simp] theorem levelStart_zero (ch : Challenges) : levelStart ch 0 = 1 := by
  simp [levelStart]

@[simp] theorem levelStart_succ (ch : Challenges) (i : Nat) :
    levelStart ch (i+1) = levelStart ch i + ch.levels[i]!.folds.size +
      ch.levels[i]!.oodPoints.size + 1 := by
  simp [levelStart, List.range_succ, Nat.add_assoc]

/-- The reply at position n can be evaluated using only n+1 visible messages. -/
def response (strategy : Strategy) (input : Public) (batches : List Batch) (n : Nat) : Reply :=
  (run strategy input [] (batches.take (n+1)))[n]!

theorem response_eq (strategy : Strategy) (input : Public) (batches : List Batch) (n : Nat) :
    response strategy input batches n = (run strategy input [] batches)[n]! := by
  rw [response, ← run_take]
  simp

theorem response_prefix (strategy : Strategy) (input : Public) (left right : List Batch)
    (n : Nat) (same : left.take (n+1) = right.take (n+1)) :
    response strategy input left n = response strategy input right n := by
  simp only [response, same]

/-- Universal projection rule: no projection of an earlier response sees a suffix. -/
theorem field_prefix {R : Type*} (field : Reply → R) (strategy : Strategy)
    (input : Public) (left right : List Batch) (n : Nat)
    (same : left.take (n+1) = right.take (n+1)) :
    field (run strategy input [] left)[n]! = field (run strategy input [] right)[n]! := by
  rw [← response_eq, ← response_eq, response_prefix strategy input left right n same]

/-- Successful parsing fixes all fields to the explicit wire-position projections. -/
theorem opening_eq_decoded (c : Config) (ch : Challenges) (answers : Array Reply)
    (proof : Opening) (h : opening c ch answers = .ok proof) :
    proof = decodedOpening c ch answers := by
  unfold opening at h
  cases hc : checkReplies (visibleBatches c E.zero ch) answers.toList <;> simp [hc] at h
  exact h.symm

/-- Successful parsing requires every tag check; malformed replies cannot be
converted to arbitrary default fields and accepted. -/
theorem opening_ok_iff (c : Config) (ch : Challenges) (answers : Array Reply)
    (proof : Opening) : opening c ch answers = .ok proof ↔
      checkReplies (visibleBatches c E.zero ch) answers.toList = .ok () ∧
      proof = decodedOpening c ch answers := by
  unfold opening
  cases hc : checkReplies (visibleBatches c E.zero ch) answers.toList <;> simp
  exact eq_comm

theorem checkReplies_length (batches : List Batch) (answers : List Reply)
    (h : checkReplies batches answers = .ok ()) : answers.length = batches.length := by
  induction batches generalizing answers with
  | nil => cases answers <;> simp_all [checkReplies]
  | cons batch batches ih =>
    cases batch <;> cases answers with
    | nil => simp_all [checkReplies]
    | cons answer answers => cases answer <;> simp_all [checkReplies]

/-- Actual parser initial message, computed before the first fold challenge. -/
theorem parsed_initial (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof) :
    proof.initial = initialField (response strategy input batches 0) := by
  rw [opening_eq_decoded _ _ _ _ h, response_eq]
  simp [decodedOpening]

theorem parsed_level (c : Config) (ch : Challenges) (answers : Array Reply)
    (proof : Opening) (h : opening c ch answers = .ok proof) (i : Fin c.folds.size) :
    proof.levels[i.val]! = decodedLevel c ch answers i := by
  rw [opening_eq_decoded _ _ _ _ h]
  simp [decodedOpening]

/-- The sent fold intro is fixed before the next fold challenge. -/
theorem parsed_afterFold (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof)
    (i : Fin c.folds.size) (j : Fin ch.levels[i.val]!.folds.size) :
    proof.levels[i.val]!.afterFold[j.val]! =
      foldField (response strategy input batches (levelStart ch i + j)) := by
  rw [parsed_level _ _ _ _ h i, response_eq]
  simp [decodedLevel]

/-- Commitment chosen with the final fold response, before the OOD or query batch. -/
theorem parsed_nextOracle (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof)
    (i : Fin c.folds.size) (next : i.val+1 < c.folds.size)
    (folds : 0 < ch.levels[i.val]!.folds.size) :
    proof.levels[i.val]!.nextOracle = rootField (response strategy input batches
      (levelStart ch i + ch.levels[i.val]!.folds.size - 1)) := by
  rw [parsed_level _ _ _ _ h i, response_eq]
  simp [decodedLevel, next, folds]

/-- Both the OOD value and its intro precede the whole queries-plus-lambda message. -/
theorem parsed_ood (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof)
    (i : Fin c.folds.size) (j : Fin ch.levels[i.val]!.oodPoints.size) :
    proof.levels[i.val]!.oods[j.val]! = oodField (response strategy input batches
      (levelStart ch i + ch.levels[i.val]!.folds.size + j)) := by
  rw [parsed_level _ _ _ _ h i, response_eq]
  simp [decodedLevel]

/-- Rows and query intro may depend on the whole query batch, including lambda. -/
theorem parsed_query (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof)
    (i : Fin c.folds.size) :
    let answer := response strategy input batches
      (levelStart ch i + ch.levels[i.val]!.folds.size + ch.levels[i.val]!.oodPoints.size)
    proof.levels[i.val]!.rows = rowsField answer ∧
    proof.levels[i.val]!.intro = introField answer := by
  rw [parsed_level _ _ _ _ h i, response_eq]
  simp [decodedLevel]

theorem parsed_residual (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof)
    (levels : 0 < c.folds.size) (folds : 0 < ch.levels[c.folds.size-1]!.folds.size) :
    proof.residual = residualField (response strategy input batches
      (levelStart ch (c.folds.size-1) + ch.levels[c.folds.size-1]!.folds.size - 1)) := by
  rw [opening_eq_decoded _ _ _ _ h, response_eq]
  simp [decodedOpening, levels, folds]

theorem parsed_tail (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof)
    (j : Fin (ch.tail.size-1)) :
    proof.tailMessages[j.val]! = tailField (response strategy input batches (tailStart c ch+j)) := by
  rw [opening_eq_decoded _ _ _ _ h, response_eq]
  simp [decodedOpening]

/-- Acceptance exposes the actual verifier's successful transition trace, including
its concrete closing comparison. There is no executor-correctness premise. -/
theorem experiment_iff (input : Public) (strategy : Strategy) (tape : Tape input.config) :
    experiment input strategy tape = true ↔
    (input.claims.all fun claim => shapeValid input.config input.lanes claim.weight) = true ∧
    ∃ proof initial finish,
      opening input.config (challenges input.config tape)
        (run strategy input [] (visibleBatches input.config tape.1
          (challenges input.config tape))).toArray = .ok proof ∧
      initializeVerifier input.config (challenges input.config tape) input.lanes
        (liftRoot input.root) (batchClaims (2^input.config.logN) input.claims tape.1).weight
        (batchClaims (2^input.config.logN) input.claims tape.1).value proof = .ok initial ∧
      CheckedTrace (verifyLevel input.config (challenges input.config tape) proof)
        input.config.folds.size 0 initial finish ∧
      (closeTail (challenges input.config tape) proof finish.state).checkTerminal
        (Concrete.mle proof.residual (challenges input.config tape).tail) = true := by
  unfold experiment
  cases hc : input.claims.all (fun claim => shapeValid input.config input.lanes claim.weight)
  · simp [hc]
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, true_and]
    cases hp : opening input.config (challenges input.config tape)
      (run strategy input [] (visibleBatches input.config tape.1
        (challenges input.config tape))).toArray with
    | error e => simp
    | ok proof =>
      have hv : (verify input.config (challenges input.config tape) input.lanes
          (liftRoot input.root) (batchClaims (2^input.config.logN) input.claims tape.1).weight
          (batchClaims (2^input.config.logN) input.claims tape.1).value proof).isOk = true ↔
          verify input.config (challenges input.config tape) input.lanes
          (liftRoot input.root) (batchClaims (2^input.config.logN) input.claims tape.1).weight
          (batchClaims (2^input.config.logN) input.claims tape.1).value proof = .ok () := by
        cases verify input.config (challenges input.config tape) input.lanes
          (liftRoot input.root) (batchClaims (2^input.config.logN) input.claims tape.1).weight
          (batchClaims (2^input.config.logN) input.claims tape.1).value proof <;> simp [Except.isOk, Except.toBool]
      rw [hv, verify_ok_iff]
      constructor
      · rintro ⟨s, t, hi, ht, hc⟩
        exact ⟨proof, s, t, rfl, hi, ht, hc⟩
      · rintro ⟨p, s, t, hp, hi, ht, hc⟩
        cases hp
        exact ⟨s, t, hi, ht, hc⟩

/-- Locate an actual level in the wire stream, with an arbitrary later suffix. -/
theorem visible_level_split (c : Config) (ch : Challenges) (initial : E)
    (i : Nat) (hi : i < c.folds.size) :
    ∃ suffix, visibleBatches c initial ch =
      ([Batch.initial initial] ++ (List.range i).flatMap (levelBatches ch)) ++
        levelBatches ch i ++ suffix := by
  have hr : List.range c.folds.size =
      List.range i ++ [i] ++
        (List.range (c.folds.size-(i+1))).map (fun x => i+1+x) := by
    calc
      List.range c.folds.size =
          List.range ((i+1)+(c.folds.size-(i+1))) := congrArg List.range (by omega)
      _ = _ := by rw [List.range_add, List.range_succ]
  simp only [visibleBatches, hr, List.flatMap_append, List.flatMap_singleton]
  refine ⟨((List.range (c.folds.size-(i+1))).map (fun x => i+1+x)).flatMap
    (levelBatches ch) ++
    (List.ofFn fun j : Fin (ch.tail.size-1) => Batch.tail j ch.tail[j.val]!), ?_⟩
  simp only [List.append_assoc]

/-- Exact prefix used by a response inside a level. The later OOD, query/lambda,
levels and tail are not inputs to this response computation. -/
theorem visible_level_prefix (c : Config) (ch : Challenges) (initial : E)
    (i k : Nat) (hi : i < c.folds.size) (hk : k ≤ (levelBatches ch i).length) :
    (visibleBatches c initial ch).take (levelStart ch i + k) =
      ([Batch.initial initial] ++ (List.range i).flatMap (levelBatches ch)) ++
        (levelBatches ch i).take k := by
  obtain ⟨suffix, hs⟩ := visible_level_split c ch initial i hi
  rw [hs, List.append_assoc, List.take_append]
  have hl : ([Batch.initial initial] ++ (List.range i).flatMap (levelBatches ch)).length =
      levelStart ch i := by simp only [List.length_append, List.length_singleton, levelStart]
  rw [hl, Nat.add_sub_cancel_left, List.take_append_of_le_length hk]
  rw [List.take_of_length_le (by rw [hl]; omega)]

/-- Initial response receives exactly the initial batching challenge. -/
theorem visible_initial_prefix (c : Config) (ch : Challenges) (initial : E) :
    (visibleBatches c initial ch).take 1 = [.initial initial] := by
  simp [visibleBatches]

/-- The root/residual prefix ends at the last fold and excludes every OOD/query. -/
theorem visible_boundary_prefix (c : Config) (ch : Challenges) (initial : E)
    (i : Nat) (hi : i < c.folds.size) :
    (visibleBatches c initial ch).take (levelStart ch i + ch.levels[i]!.folds.size) =
      ([Batch.initial initial] ++ (List.range i).flatMap (levelBatches ch)) ++
        (List.ofFn fun j : Fin ch.levels[i]!.folds.size =>
          Batch.fold i j ch.levels[i]!.folds[j]) := by
  rw [visible_level_prefix c ch initial i _ hi (by simp; omega)]
  simp [levelBatches]

/-- The OOD prefix ends before the indivisible whole-query-plus-lambda batch. -/
theorem visible_before_query (c : Config) (ch : Challenges) (initial : E)
    (i : Nat) (hi : i < c.folds.size) :
    (visibleBatches c initial ch).take
      (levelStart ch i + (ch.levels[i]!.folds.size + ch.levels[i]!.oodPoints.size)) =
      ([Batch.initial initial] ++ (List.range i).flatMap (levelBatches ch)) ++
        ((List.ofFn fun j : Fin ch.levels[i]!.folds.size =>
          Batch.fold i j ch.levels[i]!.folds[j]) ++
         (List.ofFn fun j : Fin ch.levels[i]!.oodPoints.size =>
          Batch.ood i j ch.levels[i]!.oodPoints[j])) := by
  rw [visible_level_prefix c ch initial i _ hi (by simp)]
  congr 1
  simpa only [levelBatches, List.length_append, List.length_ofFn] using
    (List.take_append_length (l₁ :=
      (List.ofFn fun j : Fin ch.levels[i]!.folds.size =>
        Batch.fold i j ch.levels[i]!.folds[j]) ++
      (List.ofFn fun j : Fin ch.levels[i]!.oodPoints.size =>
        Batch.ood i j ch.levels[i]!.oodPoints[j]))
      (l₂ := [Batch.query i ch.levels[i]!.querySqueezes ch.levels[i]!.lambda]))

/-- All visible tail coordinates are strictly before the final coordinate. -/
theorem visible_tail_congr (c : Config) (initial : E) (left right : Challenges)
    (levels : left.levels = right.levels) (size : left.tail.size = right.tail.size)
    (past : ∀ j, j+1 < left.tail.size → left.tail[j]! = right.tail[j]!) :
    visibleBatches c initial left = visibleBatches c initial right := by
  unfold visibleBatches
  have hl : levelBatches left = levelBatches right := by
    funext i
    simp [levelBatches, levels]
  rw [hl]
  congr 1
  rw [← size]
  apply List.ofFn_inj.mpr
  funext j
  congr 1
  exact past j (by omega)

/-- Varying only the final tail challenge changes no adversarial response. -/
theorem terminal_response_invisible (c : Config) (initial : E) (left right : Challenges)
    (levels : left.levels = right.levels) (size : left.tail.size = right.tail.size)
    (past : ∀ j, j+1 < left.tail.size → left.tail[j]! = right.tail[j]!)
    (strategy : Strategy) (input : Public) :
    run strategy input [] (visibleBatches c initial left) =
      run strategy input [] (visibleBatches c initial right) := by
  rw [visible_tail_congr c initial left right levels size past]

/-- The actual fold kernel consumes the causal response projection just proved;
the adversary-supplied intro is not replaced with an honest polynomial. -/
theorem foldStep_parsed (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof)
    (i : Fin c.folds.size) (j : Fin ch.levels[i.val]!.folds.size)
    (block : Nat) (state : CheckedState) :
    foldStep block ch.levels[i.val]! proof.levels[i.val]! j state =
      ⟨state.n-1, state.state.fold block ch.levels[i.val]!.folds[j.val]!
        (foldField (response strategy input batches (levelStart ch i+j))), state.oracle⟩ := by
  unfold foldStep
  rw [parsed_afterFold c ch strategy input batches proof h i j]

/-- The actual OOD transition uses the earlier OOD response, while its shared
batching lambda is taken from the later query batch exactly as in the verifier. -/
theorem oodStep_parsed (c : Config) (ch : Challenges) (strategy : Strategy)
    (input : Public) (batches : List Batch) (proof : Opening)
    (h : opening c ch (run strategy input [] batches).toArray = .ok proof)
    (i : Fin c.folds.size) (j : Fin ch.levels[i.val]!.oodPoints.size)
    (state : VerifierState E × E) :
    let claim := oodField (response strategy input batches
      (levelStart ch i+ch.levels[i.val]!.folds.size+j))
    oodStep ch.levels[i.val]! proof.levels[i.val]! j state =
      (state.1.batch (eqTable ch.levels[i.val]!.oodPoints[j.val]!)
        claim.value (state.2*ch.levels[i.val]!.lambda) claim.intro,
        state.2*ch.levels[i.val]!.lambda) := by
  dsimp only
  unfold oodStep
  rw [parsed_ood c ch strategy input batches proof h i j]

/-- A final-coordinate change leaves the parsed opening itself unchanged, not
merely the transcript. The concrete closing check still consumes that coordinate. -/
theorem parsed_terminal_invisible (c : Config) (initial : E) (left right : Challenges)
    (levels : left.levels = right.levels) (size : left.tail.size = right.tail.size)
    (past : ∀ j, j+1 < left.tail.size → left.tail[j]! = right.tail[j]!)
    (strategy : Strategy) (input : Public) (p q : Opening)
    (hp : opening c left (run strategy input [] (visibleBatches c initial left)).toArray = .ok p)
    (hq : opening c right (run strategy input [] (visibleBatches c initial right)).toArray = .ok q) :
    p = q := by
  rw [opening_eq_decoded _ _ _ _ hp, opening_eq_decoded _ _ _ _ hq,
    terminal_response_invisible c initial left right levels size past strategy input]
  cases left with
  | mk ls ts =>
    cases right with
    | mk rs us =>
      dsimp only at levels size
      subst rs
      dsimp only [decodedOpening, decodedLevel, tailStart, levelStart, levelBatches]
      congr 1
      apply Array.ext
      · simp only [Array.size_ofFn, size]
      · intro j h₁ h₂
        simp

def batchKind : Batch → Nat
  | .initial _ => 0
  | .fold _ _ _ => 1
  | .ood _ _ _ => 2
  | .query _ _ _ => 3
  | .tail _ _ => 4

def replyKind : Reply → Nat
  | .initial _ => 0
  | .fold _ _ _ => 1
  | .ood _ => 2
  | .query _ _ => 3
  | .tail _ => 4

/-- Successful parsing entails exactly the scheduled tags, including their order. -/
theorem checkReplies_tags (batches : List Batch) (answers : List Reply)
    (h : checkReplies batches answers = .ok ()) :
    batches.map batchKind = answers.map replyKind := by
  induction batches generalizing answers with
  | nil => cases answers <;> simp_all [checkReplies]
  | cons batch batches ih =>
    cases batch <;> cases answers with
    | nil => simp_all [checkReplies]
    | cons answer answers =>
      cases answer <;> simp_all [checkReplies, batchKind, replyKind]
      all_goals exact ih answers h

/-- No malformed tag sequence can produce an accepted parser output. -/
theorem malformed_reject (c : Config) (ch : Challenges) (answers : Array Reply)
    (bad : (visibleBatches c E.zero ch).map batchKind ≠ answers.toList.map replyKind)
    (proof : Opening) : opening c ch answers ≠ .ok proof := by
  intro h
  exact bad (checkReplies_tags _ _ ((opening_ok_iff c ch answers proof).mp h).1)

end Whir.CausalRefinement
