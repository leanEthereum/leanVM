import Whir.WHIRFiatShamir

/-! Concrete replay of already decoded prover messages. Later response slots are
irrelevant to an earlier allocated challenge's canonical loss envelope. -/
namespace Whir.CausalStrategy
open Concrete Protocol CausalGame CausalProbability CausalExecution

/-- Only the number of already processed messages is inspected, never a future challenge. -/
def indexedStrategy (replies : Array Reply) : Strategy := fun _ past _ => replies[past.length]?.getD default

@[simp] theorem indexedStrategy_apply (replies : Array Reply) (input : Public)
    (past : History) (batch : Batch) :
    indexedStrategy replies input past batch = replies[past.length]! := by
  unfold indexedStrategy
  by_cases h : past.length < replies.size
  · simp [getElem!_pos, getElem?_pos, h]
  · simp [getElem!_neg, getElem?_neg, h]

theorem run_length (strategy : Strategy) (input : Public) (past : History) (batches : List Batch) :
    (run strategy input past batches).length = batches.length := by
  induction batches generalizing past with
  | nil => rfl
  | cons batch batches ih => simp only [run, List.length_cons, ih]

/-- The executable response slot, including the total default for absent replies. -/
theorem indexed_response (replies : Array Reply) (input : Public) (past : History)
    (batches : List Batch) (i : Nat) (hi : i < batches.length) :
    (run (indexedStrategy replies) input past batches)[i]! = replies[past.length+i]! := by
  induction batches generalizing past i with
  | nil => simp at hi
  | cons batch batches ih =>
    cases i with
    | zero => simp only [run, indexedStrategy_apply, List.getElem!_cons_zero, Nat.add_zero]
    | succ i =>
      have bound : i < batches.length := by simpa using hi
      have result := ih ((batch, replies[past.length]!) :: past) i bound
      simpa only [run, indexedStrategy_apply, List.getElem!_cons_succ, List.length_cons,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using result

theorem run_indexed_congr (left right : Array Reply) (input : Public) (past : History)
    (batches : List Batch)
    (same : ∀ i, i < batches.length → left[past.length+i]! = right[past.length+i]!) :
    run (indexedStrategy left) input past batches = run (indexedStrategy right) input past batches := by
  apply List.ext_getElem! (by simp only [run_length])
  intro i
  by_cases hi : i < batches.length
  · rw [indexed_response left input past batches i hi, indexed_response right input past batches i hi]
    exact same i hi
  · simp [getElem!_neg, run_length, hi]

/-- Extending the decoded reply array cannot change any already replayed prefix. -/
theorem run_indexed_prefix (left right : Array Reply) (input : Public) (batches : List Batch)
    (n : Nat) (same : ∀ i, i < n → left[i]! = right[i]!) :
    (run (indexedStrategy left) input [] batches).take n =
      (run (indexedStrategy right) input [] batches).take n := by
  rw [run_take, run_take]
  apply run_indexed_congr
  intro i hi
  simpa only [List.length_nil, Nat.zero_add] using same i
    (Nat.lt_of_lt_of_le hi (List.length_take_le _ _))

open CausalStateCausality CausalRefinement CausalPositions

theorem response_eq (left right : Array Reply) (input : Public) (t : Tape input.config) (n : Nat)
    (same : left[n]! = right[n]!) :
    (run (indexedStrategy left) input [] (visibleBatches input.config t.1 (challenges input.config t)))[n]! =
      (run (indexedStrategy right) input [] (visibleBatches input.config t.1 (challenges input.config t)))[n]! := by
  by_cases h : n < (visibleBatches input.config t.1 (challenges input.config t)).length
  · rw [indexed_response left input [] _ n h, indexed_response right input [] _ n h]
    simpa only [List.length_nil, Nat.zero_add] using same
  · simp [getElem!_neg, run_length, h]

theorem proof_initial_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (same : left[0]! = right[0]!) :
    (proof input (indexedStrategy left) t).initial = (proof input (indexedStrategy right) t).initial := by
  simpa only [proof, CausalTerminal.proof, decodedOpening, List.getElem!_toArray] using
    congrArg initialField (response_eq left right input t 0 same)

theorem proof_level_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size)
    (same : ∀ n, n < levelStart (challenges input.config t) (i.val+1) → left[n]! = right[n]!) :
    (proof input (indexedStrategy left) t).levels[i.val]! =
      (proof input (indexedStrategy right) t).levels[i.val]! := by
  rw [proof_level, proof_level]
  apply decodedLevel_prefix
  · rfl
  · rfl
  · intro n hn
    exact response_eq left right input t n (same n hn)

theorem initial_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (same : left[0]! = right[0]!) :
    initial input (indexedStrategy left) t = initial input (indexedStrategy right) t := by
  unfold initial
  rw [proof_initial_eq input left right t same]

theorem levelAt_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Nat) (hi : i ≤ input.config.folds.size)
    (same : ∀ n, n < levelStart (challenges input.config t) i → left[n]! = right[n]!) :
    levelAt input (indexedStrategy left) t i = levelAt input (indexedStrategy right) t i := by
  apply CausalStateCausality.levelAt_congr
  · exact initial_eq input left right t (same 0 (levelStart_pos _ _))
  · intro k hk
    rfl
  · intro k hk
    apply proof_level_eq input left right t ⟨k, by omega⟩
    intro n hn
    exact same n (lt_of_lt_of_le hn (levelStart_mono _ (by omega : k+1 ≤ i)))

theorem foldAt_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size) (j : Nat) (hj : j ≤ input.config.folds[i.val]!)
    (same : ∀ n, n < levelStart (challenges input.config t) i.val+j → left[n]! = right[n]!) :
    foldAt input (indexedStrategy left) t i j = foldAt input (indexedStrategy right) t i j := by
  apply CausalStateCausality.foldAt_congr
  · apply levelAt_eq input left right t i.val i.isLt.le
    intro n hn
    exact same n (by omega)
  · intro k hk
    rfl
  · intro k hk
    rw [proof_fold input (indexedStrategy left) t i ⟨k, by omega⟩,
      proof_fold input (indexedStrategy right) t i ⟨k, by omega⟩]
    exact congrArg foldField (response_eq left right input t
      (levelStart (challenges input.config t) i.val+k) (same _ (by omega)))

theorem foldCandidates_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size) (j : Nat)
    (same : ∀ n, n < levelStart (challenges input.config t) i.val → left[n]! = right[n]!) :
    foldCandidates input (indexedStrategy left) t i j = foldCandidates input (indexedStrategy right) t i j := by
  unfold foldCandidates
  rw [levelAt_eq input left right t i.val i.isLt.le same]

theorem proof_nextOracle_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size)
    (same : ∀ n, n < levelStart (challenges input.config t) i.val+input.config.folds[i.val]! →
      left[n]! = right[n]!) :
    (proof input (indexedStrategy left) t).levels[i.val]!.nextOracle =
      (proof input (indexedStrategy right) t).levels[i.val]!.nextOracle := by
  rw [proof_level, proof_level]
  dsimp only [decodedLevel]
  simp only [challenge_folds_size]
  split_ifs with guard
  · have response := response_eq left right input t
      (levelStart (challenges input.config t) i.val+input.config.folds[i.val]!-1)
      (same _ (by omega))
    simpa using congrArg rootField response
  · rfl

theorem proof_residual_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size) (last : ¬ i.val+1 < input.config.folds.size)
    (same : ∀ n, n < levelStart (challenges input.config t) i.val+input.config.folds[i.val]! →
      left[n]! = right[n]!) :
    (proof input (indexedStrategy left) t).residual = (proof input (indexedStrategy right) t).residual := by
  have index : input.config.folds.size-1 = i.val := by omega
  simp only [proof, CausalTerminal.proof, decodedOpening]
  rw [index, challenge_folds_size]
  split_ifs with guard
  · have response := response_eq left right input t
      (levelStart (challenges input.config t) i.val+input.config.folds[i.val]!-1)
      (same _ (by omega))
    simpa using congrArg residualField response
  · rfl

theorem followingCandidates_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size)
    (same : ∀ n, n < levelStart (challenges input.config t) i.val+input.config.folds[i.val]! →
      left[n]! = right[n]!) :
    followingCandidates input (indexedStrategy left) t i =
      followingCandidates input (indexedStrategy right) t i := by
  unfold followingCandidates
  split_ifs with next
  · rw [proof_nextOracle_eq input left right t i same]
  · rw [proof_residual_eq input left right t i next same]

theorem proof_oods_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size)
    (same : ∀ n, n < position (.query i) → left[n]! = right[n]!) :
    (proof input (indexedStrategy left) t).levels[i.val]!.oods =
      (proof input (indexedStrategy right) t).levels[i.val]!.oods := by
  rw [proof_level, proof_level]
  dsimp only [decodedLevel]
  apply congrArg Array.ofFn
  funext j
  have bound : j.val < oodCount input.config i.val := by simpa using j.isLt
  have response := response_eq left right input t
    (levelStart (challenges input.config t) i.val+
      (challenges input.config t).levels[i.val]!.folds.size+j.val)
    (same _ (by rw [position_query i t, challenge_folds_size]; omega))
  simpa using congrArg oodField response

theorem proof_levels_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (same : ∀ n, n < tailStart input.config (challenges input.config t) → left[n]! = right[n]!) :
    (proof input (indexedStrategy left) t).levels = (proof input (indexedStrategy right) t).levels := by
  dsimp only [proof, CausalTerminal.proof, decodedOpening]
  apply congrArg Array.ofFn
  funext i
  apply decodedLevel_prefix
  · rfl
  · rfl
  · intro n hn
    exact response_eq left right input t n (same n (lt_of_lt_of_le hn
      (levelStart_mono _ (by omega : i.val+1 ≤ input.config.folds.size))))

theorem terminal_residual_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (same : ∀ n, n < tailStart input.config (challenges input.config t) → left[n]! = right[n]!) :
    (proof input (indexedStrategy left) t).residual = (proof input (indexedStrategy right) t).residual := by
  by_cases positive : 0 < input.config.folds.size
  · let last : Fin input.config.folds.size := ⟨input.config.folds.size-1, by omega⟩
    have lastEnd : last.val+1 = input.config.folds.size := by dsimp [last]; omega
    apply proof_residual_eq input left right t last (by omega)
    intro n hn
    apply same n
    have next := levelStart_succ (challenges input.config t) last.val
    rw [challenge_folds_size, lastEnd] at next
    change n < levelStart (challenges input.config t) input.config.folds.size
    omega
  · simp only [proof, CausalTerminal.proof, decodedOpening, positive, false_and, ↓reduceIte]

theorem terminal_before_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (same : ∀ n, n < tailStart input.config (challenges input.config t) → left[n]! = right[n]!) :
    CausalTerminal.before input (indexedStrategy left) t =
      CausalTerminal.before input (indexedStrategy right) t := by
  have hp := proof_initial_eq input left right t (same 0 (levelStart_pos _ _))
  have hl := proof_levels_eq input left right t same
  have hr := terminal_residual_eq input left right t same
  have init : initializeVerifier input.config (challenges input.config t) input.lanes
      (liftRoot input.root) (batchClaims (2^input.config.logN) input.claims t.1).weight
      (batchClaims (2^input.config.logN) input.claims t.1).value (proof input (indexedStrategy left) t) =
    initializeVerifier input.config (challenges input.config t) input.lanes
      (liftRoot input.root) (batchClaims (2^input.config.logN) input.claims t.1).weight
      (batchClaims (2^input.config.logN) input.claims t.1).value (proof input (indexedStrategy right) t) := by
    simp only [initializeVerifier, hp, hl]
    simp [proof, CausalTerminal.proof, decodedOpening]
  have replay : replayLevels input.config (challenges input.config t) (proof input (indexedStrategy left) t) =
      replayLevels input.config (challenges input.config t) (proof input (indexedStrategy right) t) := by
    unfold replayLevels
    have step : verifyLevel input.config (challenges input.config t) (proof input (indexedStrategy left) t) =
        verifyLevel input.config (challenges input.config t) (proof input (indexedStrategy right) t) := by
      funext i s
      simp only [verifyLevel, hl, hr]
    rw [step]
  simp only [CausalTerminal.before, CausalTerminal.beforeChecked, init, replay]

theorem proof_tail_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (j : Fin (input.config.logN-input.config.folds.toList.sum)) (k : Nat) (hk : k < j.val)
    (same : ∀ n, n < position (.tail j) → left[n]! = right[n]!) :
    (proof input (indexedStrategy left) t).tailMessages[k]! =
      (proof input (indexedStrategy right) t).tailMessages[k]! := by
  simp only [proof, CausalTerminal.proof, decodedOpening]
  have bound : k < (challenges input.config t).tail.size-1 := by
    rw [CausalTerminal.tail_size]
    omega
  rw [getElem!_pos _ _ (by simpa only [Array.size_ofFn] using bound),
    getElem!_pos _ _ (by simpa only [Array.size_ofFn] using bound)]
  simp only [Array.getElem_ofFn]
  have response := response_eq left right input t (tailStart input.config (challenges input.config t)+k)
    (same _ (by rw [CausalPrefix.position_tail j t]; omega))
  simpa using congrArg tailField response

theorem tail_kernels_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (j : Fin (input.config.logN-input.config.folds.toList.sum))
    (same : ∀ n, n < position (.tail j) → left[n]! = right[n]!) :
    CausalTerminal.candidate input (indexedStrategy left) t j =
        CausalTerminal.candidate input (indexedStrategy right) t j ∧
      CausalTerminal.pending input (indexedStrategy left) t j =
        CausalTerminal.pending input (indexedStrategy right) t j := by
  have prior (n : Nat) (hn : n < tailStart input.config (challenges input.config t)) :
      left[n]! = right[n]! := same n (by rw [CausalPrefix.position_tail j t]; omega)
  have residual := terminal_residual_eq input left right t prior
  have before := terminal_before_eq input left right t prior
  constructor
  · simp only [CausalTerminal.candidate]
    rw [residual]
  · have every (k : Nat) (hk : k ≤ j.val) :
        TerminalSoundness.stateAt (challenges input.config t) (proof input (indexedStrategy left) t)
            (CausalTerminal.before input (indexedStrategy left) t) k =
          TerminalSoundness.stateAt (challenges input.config t) (proof input (indexedStrategy right) t)
            (CausalTerminal.before input (indexedStrategy right) t) k := by
      induction k with
      | zero => exact before
      | succ k ih =>
        rw [TerminalSoundness.stateAt_succ, TerminalSoundness.stateAt_succ, ih (by omega)]
        unfold tailStep
        rw [proof_tail_eq input left right t j k (by omega) same]
    exact every j le_rfl

theorem query_envelope_eq (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size)
    (same : ∀ n, n < position (.query i) → left[n]! = right[n]!) :
    WHIRFiatShamir.QueryEnvelope input (indexedStrategy left) i t =
      WHIRFiatShamir.QueryEnvelope input (indexedStrategy right) i t := by
  have boundaryPast (n : Nat) (hn : n < levelStart (challenges input.config t) i.val+input.config.folds[i.val]!) :
      left[n]! = right[n]! := same n (by rw [position_query i t]; omega)
  have level := levelAt_eq input left right t i i.isLt.le
    (fun n hn => boundaryPast n (by omega))
  have folded := foldAt_eq input left right t i input.config.folds[i.val]! le_rfl boundaryPast
  have following := followingCandidates_eq input left right t i boundaryPast
  have oods := proof_oods_eq input left right t i same
  have prior : CausalBoundary.QueryPrior input (indexedStrategy left) i t =
      CausalBoundary.QueryPrior input (indexedStrategy right) i t := by
    unfold CausalBoundary.QueryPrior CausalBoundary.boundary
    dsimp only
    rw [level, folded, following, oods]
    by_cases next : i.val+1 < input.config.folds.size
    · simp only [next, ↓reduceIte]
    · rw [proof_residual_eq input left right t i next boundaryPast]
  funext x
  unfold WHIRFiatShamir.QueryEnvelope CausalBoundary.boundary
  rw [prior, level, folded, following]
  simp only [QueryBatchSoundness.Restores, queryBatch, oodBatch, oods]
  rfl

/-- Allocation envelopes inspect only replies strictly before their own random draw. -/
theorem envelope_indexed_eq (input : Public) (left right : Array Reply)
    (q : Coordinate input.config) (t : Tape input.config)
    (same : ∀ n, n < position q → left[n]! = right[n]!) :
    WHIRFiatShamir.Envelope input (indexedStrategy left) q t =
      WHIRFiatShamir.Envelope input (indexedStrategy right) q t := by
  funext x
  cases q with
  | initial => rfl
  | fold i j =>
    let u := set (.fold i j) t x
    have prior (n : Nat) (hn : n < levelStart (challenges input.config u) i.val+j.val) :
        left[n]! = right[n]! := same n (by rw [position_fold i j u]; exact hn)
    have early (n : Nat) (hn : n < levelStart (challenges input.config u) i.val) :
        left[n]! = right[n]! := prior n (by omega)
    have state := foldAt_eq input left right u i j j.isLt.le prior
    have oldList := foldCandidates_eq input left right u i j early
    have newList := foldCandidates_eq input left right u i (j.val+1) early
    change CausalFolds.Event input (indexedStrategy left) i j u =
      CausalFolds.Event input (indexedStrategy right) i j u
    unfold CausalFolds.Event
    rw [oldList, newList, state, foldAt_succ, foldAt_succ, state]
    rfl
  | ood i j =>
    let u := set (.ood i j) t x
    have boundaryPast (n : Nat)
        (hn : n < levelStart (challenges input.config u) i.val+input.config.folds[i.val]!) :
        left[n]! = right[n]! := same n (by rw [position_ood i j u]; omega)
    change CausalBoundary.OodEvent input (indexedStrategy left) i j u =
      CausalBoundary.OodEvent input (indexedStrategy right) i j u
    unfold CausalBoundary.OodEvent
    rw [followingCandidates_eq input left right u i boundaryPast]
  | query i => exact congrFun (query_envelope_eq input left right t i same) x
  | tail j =>
    have kernels := tail_kernels_eq input left right (set (.tail j) t x) j same
    dsimp only [WHIRFiatShamir.Envelope, CausalBadEvents.Bad]
    rw [kernels.1, kernels.2]

/-- Concrete replay realizations agreeing on strict prior replies and challenges
have exactly the same allocation-time event on the whole next draw. -/
theorem allocationBad_indexed_congr (p : ParameterBounds.Profile) (s : WHIRFiatShamir.Statement p)
    (left right : Array Reply) (q : Coordinate (ParameterBounds.config p))
    (t u : Tape (ParameterBounds.config p)) (x : Sample q)
    (replies : ∀ j, j < position q → left[j]! = right[j]!)
    (tape : ∀ r, position r < position q → get r t = get r u) :
    WHIRFiatShamir.allocationBad (WHIRFiatShamir.requestOfTape s (indexedStrategy left) q t) x ↔
      WHIRFiatShamir.allocationBad (WHIRFiatShamir.requestOfTape s (indexedStrategy right) q u) x := by
  have past : WHIRFiatShamir.Prefix.ofTape q t = WHIRFiatShamir.Prefix.ofTape q u := by
    funext r hr
    exact tape r hr
  unfold WHIRFiatShamir.allocationBad WHIRFiatShamir.requestOfTape
  dsimp only
  rw [past]
  exact Iff.of_eq (congrFun (envelope_indexed_eq s.input left right q
    (WHIRFiatShamir.Prefix.ofTape q u).tape replies) x)

end Whir.CausalStrategy
