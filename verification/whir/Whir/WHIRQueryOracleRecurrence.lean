import Whir.WHIRPhysicalHistory
import Whir.WHIRPhysicalVerifier

/-! Exact query-oracle provenance. Query authentication reads the incoming raw
commitment, not a weight-batched or folded replacement. Its folded interpretation
uses the actual challenge prefix, reversing/padding only the initial top lanes.
Root slots are extracted from the actual scalar decoder, including its failures;
no row-agreement or decoder-correctness certificate is an input.

Consumers use `queryRows_zero` for the original root and
`queryRows_decoded_rootLog` for later levels. The latter derives the digest at
compressed chronological index `i-1` from successful physical scalar parsing and
scheduled syntax, including its availability. `rootLog_cons` connects this pure
log to a physical commitment trace; `foldedOracle_step` gives its separate
challenge-by-challenge algebraic interpretation. -/
namespace Whir.WHIRQueryOracleRecurrence
open Concrete Protocol CausalGame CausalProbability CausalExecution
open CausalStateCausality CausalPositions ParameterBounds
open FiatShamirGame (Digest32)
open WHIRHistory (Pending)

/-- Folding updates only the algebraic state; authentication retains the root. -/
theorem foldStep_oracle (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (j : Nat) (s : CheckedState) : (foldStep block cs p j s).oracle = s.oracle := rfl

theorem foldSteps_oracle (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (count start : Nat) (s : CheckedState) :
    (runSteps (foldStep block cs p) count start s).oracle = s.oracle := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih => exact ih (start + 1) (foldStep block cs p start s)

theorem foldAt_oracle (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i j : Nat) : (foldAt input strategy t i j).oracle = (levelAt input strategy t i).oracle :=
  foldSteps_oracle _ _ _ _ _ _

/-- OOD and query weight batching cannot affect the next commitment projection,
even when query derivation fails and the total kernel uses its empty default. -/
theorem next_oracle (c : Config) (ch : Challenges) (p : Opening)
    (i : Nat) (s : CheckedState) :
    (next c ch p i s).oracle = p.levels[i]!.nextOracle.getD #[] := rfl

theorem levelAt_zero_oracle (input : Public) (strategy : Strategy) (t : Tape input.config) :
    (levelAt input strategy t 0).oracle = liftRoot input.root := rfl

theorem levelAt_succ_oracle (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i : Nat) : (levelAt input strategy t (i + 1)).oracle =
      (proof input strategy t).levels[i]!.nextOracle.getD #[] := by
  rw [levelAt_succ, next_oracle]

/-- The boundary root lives at the actual final fold response, not the OOD or
query-introduction slot. The absent/zero-fold/final-level branch is literal none. -/
theorem proof_nextOracle_slot (input : Public) (replies : Array Reply)
    (t : Tape input.config) (i : Fin input.config.folds.size) :
    (proof input (CausalStrategy.indexedStrategy replies) t).levels[i.val]!.nextOracle =
      if i.val + 1 < input.config.folds.size ∧ 0 < input.config.folds[i.val]! then
        rootField replies[levelStart (challenges input.config t) i.val + input.config.folds[i.val]! - 1]!
      else none := by
  rw [proof_level]
  dsimp only [decodedLevel]
  simp only [challenge_folds_size]
  split_ifs with guard
  · let j : Fin input.config.folds[i.val]! := ⟨input.config.folds[i.val]! - 1, by omega⟩
    have member : Coordinate.fold i j ∈ visibleCoordinates input.config := by
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
      unfold levelCoordinates
      rw [dite_eq_left i.isLt]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j, rfl⟩))
    have bound : position (.fold i j) <
        (visibleBatches input.config t.1 (challenges input.config t)).length := by
      rw [← visibleCoordinates_map, List.length_map]
      exact List.idxOf_lt_length_iff.mpr member
    rw [position_fold] at bound
    have index : levelStart (challenges input.config t) i.val + j.val =
        levelStart (challenges input.config t) i.val + input.config.folds[i.val]! - 1 := by
      dsimp [j]; omega
    rw [index] at bound
    simp only [List.getElem!_toArray]
    rw [CausalStrategy.indexed_response _ _ [] _ _ bound]
    simp only [List.length_nil, Nat.zero_add]
  · rfl

theorem levelAt_succ_rootSlot (input : Public) (replies : Array Reply)
    (t : Tape input.config) (i : Fin input.config.folds.size) :
    (levelAt input (CausalStrategy.indexedStrategy replies) t (i.val + 1)).oracle =
      (if i.val + 1 < input.config.folds.size ∧ 0 < input.config.folds[i.val]! then
        rootField replies[levelStart (challenges input.config t) i.val + input.config.folds[i.val]! - 1]!
      else none).getD #[] := by
  rw [levelAt_succ_oracle, proof_nextOracle_slot]

/-- Association with a typed last-fold position, independent of challenge values. -/
theorem levelAt_succ_lastFold (input : Public) (replies : Array Reply)
    (t : Tape input.config) (i : Fin input.config.folds.size)
    (j : Fin input.config.folds[i.val]!) (last : j.val + 1 = input.config.folds[i.val]!)
    (hasNext : i.val + 1 < input.config.folds.size) :
    (levelAt input (CausalStrategy.indexedStrategy replies) t (i.val + 1)).oracle =
      (rootField replies[position (.fold i j)]!).getD #[] := by
  rw [levelAt_succ_rootSlot, ite_eq_left ⟨hasNext, by omega⟩, position_fold i j t]
  have index : levelStart (challenges input.config t) i.val + input.config.folds[i.val]! - 1 =
      levelStart (challenges input.config t) i.val + j.val := by omega
  rw [index]

/-- Query rows are sampled from the original base root at L0. -/
theorem queryRows_zero {p : Profile} (r : WHIRReplay.Replay p)
    (i : Fin (config p).folds.size) (zero : i.val = 0) (x : Sample (.query i)) :
    WHIRReplay.queryRows r i x =
      (QueryBatchSoundness.queries (remaining (config p) i + (config p).rates[i.val]!)
        (config p).queries[i.val]! x.1).map (fun q => (liftRoot r.statement.input.root)[q]!) := by
  unfold WHIRReplay.queryRows
  simp only [zero, levelAt_zero_oracle]

/-- Later query rows use exactly the previous level's decoded boundary root. -/
theorem queryRows_succ {p : Profile} (r : WHIRReplay.Replay p)
    (i previous : Fin (config p).folds.size) (succ : i.val = previous.val + 1)
    (j : Fin (config p).folds[previous.val]!)
    (last : j.val + 1 = (config p).folds[previous.val]!) (x : Sample (.query i)) :
    WHIRReplay.queryRows r i x =
      (QueryBatchSoundness.queries (remaining (config p) i + (config p).rates[i.val]!)
        (config p).queries[i.val]! x.1).map
        (fun q => ((rootField r.replies[position (.fold previous j)]!).getD #[])[q]!) := by
  unfold WHIRReplay.queryRows
  have h := levelAt_succ_lastFold r.statement.input r.replies r.tape previous j last
    (show previous.val + 1 < (config p).folds.size by have := i.isLt; omega)
  simp only [← succ] at h
  rw [h]

/-- Folded interpretation of an incoming commitment. L0 uses reversed padded
lanes; later commitments use low-lane folding without that reversal. -/
def foldedOracle (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i j : Nat) {N : Nat} : Fin (2 ^ (input.config.folds[i]! - j)) → Fin N → E :=
  OracleReplay.oracleAt (i == 0) input.config.folds[i]!
    (levelAt input strategy t i).oracle (challenges input.config t).levels[i]!.folds j

theorem foldedOracle_zero (input : Public) (strategy : Strategy) (t : Tape input.config)
    (j : Nat) {N : Nat} : foldedOracle input strategy t 0 j (N := N) =
      OracleReplay.oracleAt true input.config.folds[0]! (liftRoot input.root)
        (challenges input.config t).levels[0]!.folds j := rfl

theorem foldedOracle_succ (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i j : Nat) {N : Nat} : foldedOracle input strategy t (i + 1) j (N := N) =
      OracleReplay.oracleAt false input.config.folds[i + 1]!
        ((proof input strategy t).levels[i]!.nextOracle.getD #[])
        (challenges input.config t).levels[i + 1]!.folds j := by
  have base : (i + 1 == 0) = false := by simp
  simp only [foldedOracle, base, levelAt_succ_oracle]

theorem foldedOracle_step (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i j : Nat) (hj : j < input.config.folds[i]!) {N : Nat} :
    foldedOracle input strategy t i (j + 1) (N := N) =
      CandidateFolding.foldOracle
        (OracleReplay.pairedOracle (i == 0) input.config.folds[i]!
          (levelAt input strategy t i).oracle (challenges input.config t).levels[i]!.folds j hj)
        (challenges input.config t).levels[i]!.folds[j]! :=
  OracleReplay.oracleAt_succ _ _ _ _ _ _

/-- Successful scalar parsing fixes the ghost root to the actual digest callback.
Every malformed scalar branch remains rejected by the premise. -/
theorem decodeReplyScalars_root {c : Config} (q : Coordinate c)
    (lookup : Digest32 → Oracle) (rows : Oracle) (xs : List E) (response : Reply)
    (parsed : WHIRHistory.decodeReplyScalars q lookup rows xs = some response) :
    rootField response = (WHIRPhysicalVerifier.absorbedRoot q xs).map lookup := by
  cases q with
  | initial =>
    simp only [WHIRHistory.decodeReplyScalars] at parsed
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rfl
  | query i =>
    simp only [WHIRHistory.decodeReplyScalars] at parsed
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rfl
  | tail j =>
    simp only [WHIRHistory.decodeReplyScalars] at parsed
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rfl
  | ood i j =>
    cases xs with
    | nil => cases parsed
    | cons a xs => cases xs with
      | nil => cases parsed
      | cons b xs => cases xs with
        | nil => cases parsed
        | cons d xs => cases xs with
          | nil => cases parsed; rfl
          | cons e xs => cases parsed
  | fold i j =>
    cases xs with
    | nil => cases parsed
    | cons a xs => cases xs with
      | nil => cases parsed
      | cons b rest =>
        simp only [WHIRHistory.decodeReplyScalars] at parsed
        by_cases last : j.val + 1 = c.folds[i.val]!
        · by_cases hasNext : i.val + 1 < c.folds.size
          · simp only [last, hasNext, ↓reduceIte] at parsed
            cases rest with
            | nil => cases parsed
            | cons r rest => cases rest with
              | nil => cases parsed
              | cons s rest => cases rest with
                | cons d rest => cases parsed
                | nil =>
                  obtain ⟨digest, decoded, rfl⟩ := Option.map_eq_some_iff.mp parsed
                  simp [WHIRPhysicalVerifier.absorbedRoot, last, hasNext, decoded, rootField]
          · simp only [last, hasNext, ↓reduceIte] at parsed
            split at parsed
            · cases parsed
              simp [rootField, WHIRPhysicalVerifier.absorbedRoot, hasNext]
            · cases parsed
        · simp only [last, ↓reduceIte] at parsed
          split at parsed
          · cases parsed
            simp only [rootField, WHIRPhysicalVerifier.absorbedRoot, last, false_and,
              ↓reduceIte, Option.map_none]
          · cases parsed

/-- Chronological response slots, retaining non-root slots as `none`. Each digest
is read from the scalar message at its preceding canonical challenge coordinate. -/
def rootSlots (p : Profile) (roots : WHIRReplay.Roots) (s : Digest32) :
    List Pending → Array (Option Oracle)
  | m :: previous :: older =>
    let q := WHIRReplay.query p (s, previous :: older)
    (rootSlots p roots s (previous :: older)).push
      ((WHIRPhysicalVerifier.absorbedRoot q m.scalars).map
        (fun digest => roots digest (WHIRHistory.coordinateLevel q + 1)))
  | _ => #[]

/-- Actual physical decoding fixes every root position independently of supplied
query rows. All syntax, phase, nonce and position checks are still executed. -/
theorem decodeHistory_rootSlots (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List Pending) (ancestors : List (Pending × Sigma (@Sample (config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors = some out) :
    out.replies.map rootField = rootSlots p roots s messages := by
  induction messages generalizing ancestors out with
  | nil => cases parsed
  | cons m messages ih =>
    cases messages with
    | nil =>
      cases ancestors with
      | cons a ancestors => cases parsed
      | nil =>
        simp only [WHIRPhysicalHistory.decodeHistory] at parsed
        split at parsed
        · cases found : catalog s with
          | none => simp [found] at parsed
          | some statement =>
            simp [found] at parsed
            subst out
            simp [rootSlots]
        · cases parsed
    | cons previous older =>
      cases ancestors with
      | nil => cases parsed
      | cons a past =>
        rcases a with ⟨previous', q, x⟩
        simp only [WHIRPhysicalHistory.decodeHistory] at parsed
        split at parsed
        · split at parsed
          · rename_i phase
            split at parsed
            · split at parsed
              · split at parsed
                · cases prior : WHIRPhysicalHistory.decodeHistory p catalog roots rows s
                      (previous :: older) past with
                  | none => simp [prior] at parsed
                  | some before =>
                    simp only [prior, WHIRPhysicalHistory.step] at parsed
                    obtain ⟨response, decoded, rfl⟩ := Option.map_eq_some_iff.mp parsed
                    rw [Array.map_push, ih past before prior]
                    have hr := decodeReplyScalars_root q _ _ _ response decoded
                    simp only [rootSlots]
                    rw [hr, phase]
                · cases parsed
              · cases parsed
            · cases parsed
          · cases parsed
        · cases parsed

/-- Pointwise scalar root-slot association, including absent response defaults. -/
theorem decodeHistory_rootField (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List Pending) (ancestors : List (Pending × Sigma (@Sample (config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors = some out)
    (n : Nat) :
    rootField out.replies[n]! = (rootSlots p roots s messages)[n]! := by
  have mapped := decodeHistory_rootSlots p catalog roots rows s messages ancestors out parsed
  rw [← mapped]
  by_cases hn : n < out.replies.size
  · simp [getElem!_pos, hn]
  · have hm : ¬ n < (out.replies.map rootField).size := by
      simpa only [Array.size_map] using hn
    rw [getElem!_neg out.replies n hn, getElem!_neg (out.replies.map rootField) n hm]
    rfl

/-- End-to-end later query projection from successful physical scalar decoding.
The physical root log only needs to identify the displayed canonical scalar slot. -/
theorem queryRows_decoded_succ (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List Pending) (ancestors : List (Pending × Sigma (@Sample (config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors = some out)
    (i previous : Fin (config p).folds.size) (succ : i.val = previous.val + 1)
    (j : Fin (config p).folds[previous.val]!)
    (last : j.val + 1 = (config p).folds[previous.val]!) (x : Sample (.query i)) :
    WHIRReplay.queryRows out i x =
      (QueryBatchSoundness.queries (remaining (config p) i + (config p).rates[i.val]!)
        (config p).queries[i.val]! x.1).map
        (fun q => (((rootSlots p roots s messages)[position (.fold previous j)]!).getD #[])[q]!) := by
  rw [queryRows_succ out i previous succ j last x,
    decodeHistory_rootField p catalog roots rows s messages ancestors out parsed]

/-- The only schedule positions carrying a next-root digest. -/
def rootCoordinate {c : Config} : Coordinate c → Bool
  | .fold i j => decide (j.val + 1 = c.folds[i.val]! ∧ i.val + 1 < c.folds.size)
  | _ => false

/-- Raw digests, in chronological response-slot order, before compression. -/
def digestSlots (p : Profile) (s : Digest32) : List Pending → List (Option Digest32)
  | m :: previous :: older =>
    digestSlots p s (previous :: older) ++
      [WHIRPhysicalVerifier.absorbedRoot (WHIRReplay.query p (s,previous :: older)) m.scalars]
  | _ => []

/-- The canonical transmitted-root log excludes the original public root. -/
def rootLog (p : Profile) (s : Digest32) (messages : List Pending) : List Digest32 :=
  (digestSlots p s messages).filterMap id

theorem rootLog_cons (p : Profile) (s : Digest32) (m previous : Pending) (older : List Pending) :
    rootLog p s (m :: previous :: older) = rootLog p s (previous :: older) ++
      (WHIRPhysicalVerifier.absorbedRoot (WHIRReplay.query p (s,previous :: older)) m.scalars).toList := by
  simp only [rootLog, digestSlots, List.filterMap_append]
  cases WHIRPhysicalVerifier.absorbedRoot (WHIRReplay.query p (s,previous :: older)) m.scalars <;> rfl

private theorem level_root_count (c : Config) (i : Fin c.folds.size)
    (positive : 0 < c.folds[i.val]!) (hasNext : i.val + 1 < c.folds.size) :
    (levelCoordinates c i.val).countP rootCoordinate = 1 := by
  let last : Fin c.folds[i.val]! := ⟨c.folds[i.val]! - 1, by omega⟩
  have folds : (List.ofFn (Coordinate.fold i)).countP rootCoordinate = 1 := by
    rw [List.ofFn_eq_map, List.countP_map]
    have same : (List.finRange c.folds[i.val]!).countP (rootCoordinate ∘ Coordinate.fold i) =
        (List.finRange c.folds[i.val]!).count last := by
      rw [List.count_eq_countP]
      apply List.countP_congr
      intro j _
      simp only [Function.comp_apply, rootCoordinate, decide_eq_true_eq, beq_iff_eq, Fin.ext_iff]
      dsimp [last]
      omega
    rw [same]
    exact List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange last)
  have oods : (List.ofFn (Coordinate.ood i)).countP rootCoordinate = 0 := by
    apply List.countP_eq_zero.mpr
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    simp only [rootCoordinate, Bool.false_eq_true, not_false_eq_true]
  unfold levelCoordinates
  rw [dite_eq_left i.isLt]
  simp only [List.countP_append, folds, oods, List.countP_singleton, rootCoordinate,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

/-- Before any fold at level i, exactly i earlier boundary digests have occurred.
Only positivity of earlier fold counts is needed; no acceptance premise is used. -/
theorem schedule_root_count_fold (c : Config) (i : Fin c.folds.size)
    (j : Fin c.folds[i.val]!) (positive : ∀ k, k < i.val → 0 < c.folds[k]!) :
    ((WHIRHistory.schedule c).take (position (.fold i j))).countP rootCoordinate = i.val := by
  let t : Tape c := (coordinates c).symm (fun _ => 0)
  let prior := (List.range i.val).flatMap (levelCoordinates c)
  let pre := [Coordinate.initial (c := c)] ++ prior
  let folds := List.ofFn (Coordinate.fold i)
  let rest := List.ofFn (Coordinate.ood i) ++ [.query i] ++
    ((List.range (c.folds.size - (i.val + 1))).map (fun x => i.val + 1 + x)).flatMap
      (levelCoordinates c) ++
    (List.ofFn fun k : Fin (c.logN - c.folds.toList.sum - 1) =>
      Coordinate.tail ⟨k.val, by omega⟩) ++ WHIRHistory.hiddenTail c
  have range : List.range c.folds.size = List.range i.val ++ [i.val] ++
      (List.range (c.folds.size - (i.val + 1))).map (fun x => i.val + 1 + x) := by
    calc
      List.range c.folds.size =
          List.range ((i.val + 1) + (c.folds.size - (i.val + 1))) :=
        congrArg List.range (by omega)
      _ = _ := by rw [List.range_add, List.range_succ]
  have schedule : WHIRHistory.schedule c = pre ++ (folds ++ rest) := by
    simp only [WHIRHistory.schedule, visibleCoordinates, range, List.flatMap_append,
      List.flatMap_singleton, pre, prior, folds, rest, levelCoordinates, i.isLt,
      dite_true, List.append_assoc]
  have lengths : prior.length = ((List.range i.val).flatMap (levelBatches (challenges c t))).length := by
    rw [← List.length_map (f := fun q => batch q (get q t))]
    simp only [prior, List.map_flatMap]
    congr 1
    apply List.flatMap_congr
    intro k hk
    exact levelCoordinates_map c t k (lt_trans (List.mem_range.mp hk) i.isLt)
  have index : position (.fold i j) = pre.length + j.val := by
    rw [position_fold i j t]
    simp only [pre, List.length_append, List.length_singleton, lengths, levelStart]
  have taken : (WHIRHistory.schedule c).take (position (.fold i j)) = pre ++ folds.take j.val := by
    rw [schedule, index, List.take_length_add_append,
      List.take_append_of_le_length (by simpa [folds] using j.isLt.le)]
  have foldCount : (folds.take j.val).countP rootCoordinate = 0 := by
    apply List.countP_eq_zero.mpr
    intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
    have before : k < j.val := lt_of_lt_of_le hk (List.length_take_le _ _)
    simp only [folds, List.getElem_take, List.getElem_ofFn, rootCoordinate, decide_eq_true_eq]
    omega
  have priorCount : prior.countP rootCoordinate = i.val := by
    dsimp only [prior]
    rw [List.countP_flatMap]
    have same : (List.range i.val).map (List.countP rootCoordinate ∘ levelCoordinates c) =
        (List.range i.val).map (fun _ => 1) := by
      apply List.map_congr_left
      intro k hk
      have hk' := List.mem_range.mp hk
      exact level_root_count c ⟨k, by omega⟩ (positive k hk')
        (show k + 1 < c.folds.size by omega)
    rw [same]
    simp
  rw [taken, List.countP_append, foldCount]
  simp only [pre, List.countP_append, List.countP_singleton, rootCoordinate,
    Bool.false_eq_true, ↓reduceIte, priorCount, Nat.zero_add, Nat.add_zero]

theorem digestSlots_length (p : Profile) (s : Digest32) (messages : List Pending) :
    (digestSlots p s messages).length = messages.length - 1 := by
  induction messages with
  | nil => rfl
  | cons m messages ih =>
    cases messages with
    | nil => rfl
    | cons previous older => simp [digestSlots, ih]

theorem rootSlots_toList (p : Profile) (roots : WHIRReplay.Roots) (s : Digest32)
    (messages : List Pending) :
    (rootSlots p roots s messages).toList =
      (digestSlots p s messages).mapIdx (fun n d => d.map (fun digest =>
        roots digest (WHIRHistory.coordinateLevel
          (((WHIRHistory.schedule (config p))[n]?).getD .initial) + 1))) := by
  induction messages with
  | nil => rfl
  | cons m messages ih =>
    cases messages with
    | nil => rfl
    | cons previous older =>
      simp [rootSlots, digestSlots, Array.toList_push, List.mapIdx_append, ih,
        digestSlots_length, WHIRReplay.query, WHIRHistory.queryFor]

theorem decodeReplyScalars_root_present {c : Config} (q : Coordinate c)
    (lookup : Digest32 → Oracle) (rows : Oracle) (xs : List E) (response : Reply)
    (parsed : WHIRHistory.decodeReplyScalars q lookup rows xs = some response) :
    (WHIRPhysicalVerifier.absorbedRoot q xs).isSome = rootCoordinate q := by
  cases q with
  | initial => rfl
  | query i => rfl
  | tail j => rfl
  | ood i j => rfl
  | fold i j =>
    by_cases boundary : j.val + 1 = c.folds[i.val]! ∧ i.val + 1 < c.folds.size
    · obtain ⟨last, hasNext⟩ := boundary
      cases xs with
      | nil => cases parsed
      | cons a xs => cases xs with
        | nil => cases parsed
        | cons b rest =>
          simp only [WHIRHistory.decodeReplyScalars, last, hasNext, ↓reduceIte] at parsed
          cases rest with
          | nil => cases parsed
          | cons r rest => cases rest with
            | nil => cases parsed
            | cons s rest => cases rest with
              | cons d rest => cases parsed
              | nil =>
                obtain ⟨digest, decoded, _⟩ := Option.map_eq_some_iff.mp parsed
                simp [WHIRPhysicalVerifier.absorbedRoot, last, hasNext, decoded, rootCoordinate]
    · simp only [WHIRPhysicalVerifier.absorbedRoot, boundary, ↓reduceIte,
        Option.isSome_none, rootCoordinate, decide_false]

/-- Successful parsing fills every scheduled boundary digest, and no other slot.
This retains rejected hash encodings rather than silently filtering failures. -/
theorem decodeHistory_digest_shape (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List Pending) (ancestors : List (Pending × Sigma (@Sample (config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors = some out) :
    (digestSlots p s messages).map Option.isSome =
      ((WHIRHistory.schedule (config p)).take (messages.length - 1)).map rootCoordinate := by
  induction messages generalizing ancestors out with
  | nil => cases parsed
  | cons m messages ih =>
    cases messages with
    | nil => simp [digestSlots]
    | cons previous older =>
      cases ancestors with
      | nil => cases parsed
      | cons a past =>
        rcases a with ⟨previous', q, x⟩
        simp only [WHIRPhysicalHistory.decodeHistory] at parsed
        split at parsed
        · split at parsed
          · rename_i phase
            split at parsed
            · rename_i previousPosition
              split at parsed
              · split at parsed
                · cases prior : WHIRPhysicalHistory.decodeHistory p catalog roots rows s
                      (previous :: older) past with
                  | none => simp [prior] at parsed
                  | some before =>
                    simp only [prior, WHIRPhysicalHistory.step] at parsed
                    obtain ⟨response, decoded, _⟩ := Option.map_eq_some_iff.mp parsed
                    have present := decodeReplyScalars_root_present q _ _ _ response decoded
                    have slot := WHIRHistory.schedule_get_position q
                    rw [previousPosition] at slot
                    simp only [digestSlots, List.map_append, List.map_cons, List.map_nil,
                      ← phase, present, ih past before prior, List.length_cons,
                      Nat.add_sub_cancel, List.take_add_one, slot, Option.toList_some]
                · cases parsed
              · cases parsed
            · cases parsed
          · cases parsed
        · cases parsed

private theorem filterMap_rank {A : Type*} (xs : List (Option A)) (n : Nat) (x : A)
    (found : xs[n]? = some (some x)) :
    (xs.filterMap id)[((xs.take n).filterMap id).length]? = some x := by
  induction xs generalizing n with
  | nil => cases found
  | cons a xs ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst a
      rfl
    | succ n =>
      simp only [List.getElem?_cons_succ] at found
      have tail := ih n found
      cases a <;> simpa [List.filterMap_cons, List.take_succ_cons] using tail

/-- The canonical compressed digest at index i is precisely the last-fold root
slot of level i. Availability and positive earlier fold counts are schedule/shape
facts, not oracle-agreement premises. The conclusion also proves log availability. -/
theorem decoded_rootLog_slot (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List Pending) (ancestors : List (Pending × Sigma (@Sample (config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors = some out)
    (i : Fin (config p).folds.size) (j : Fin (config p).folds[i.val]!)
    (last : j.val + 1 = (config p).folds[i.val]!) (hasNext : i.val + 1 < (config p).folds.size)
    (positive : ∀ k, k < i.val → 0 < (config p).folds[k]!)
    (available : position (.fold i j) < messages.length - 1) :
    ∃ digest, (rootLog p s messages)[i.val]? = some digest ∧
      rootField out.replies[position (.fold i j)]! = some (roots digest (i.val + 1)) := by
  let n := position (.fold i j)
  have shape := decodeHistory_digest_shape p catalog roots rows s messages ancestors out parsed
  have slot := WHIRHistory.schedule_get_position (Coordinate.fold i j)
  have flag : ((digestSlots p s messages)[n]?).map Option.isSome = some true := by
    rw [← List.getElem?_map, shape, List.getElem?_map,
      List.getElem?_take_of_lt available, slot]
    simp [rootCoordinate, last, hasNext]
  cases found : (digestSlots p s messages)[n]? with
  | none => simp [found] at flag
  | some d =>
    cases d with
    | none => simp [found] at flag
    | some digest =>
      have rank := filterMap_rank (digestSlots p s messages) n digest found
      have count : ((digestSlots p s messages).take n).countP Option.isSome = i.val := by
        have taken := congrArg (List.take n) shape
        rw [← List.map_take, ← List.map_take, List.take_take, Nat.min_eq_left available.le] at taken
        have counts := congrArg (List.count true) taken
        have hb : ∀ b : Bool, (b == true) = b := by intro b; cases b <;> rfl
        simp only [List.count_eq_countP, List.countP_map, Function.comp_def, hb] at counts
        rw [counts]
        exact schedule_root_count_fold (config p) i j positive
      simp only [List.length_filterMap_eq_countP, id_eq, count] at rank
      refine ⟨digest, rank, ?_⟩
      rw [decodeHistory_rootField p catalog roots rows s messages ancestors out parsed]
      have rootAt : (rootSlots p roots s messages).toList[n]? =
          some (some (roots digest (i.val + 1))) := by
        rw [rootSlots_toList, List.getElem?_mapIdx, found]
        simp only [n, slot, Option.getD_some, WHIRHistory.coordinateLevel, Option.map_some]
      simpa only [Array.getElem!_toList] using List.getElem!_of_getElem? rootAt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A checked finite-family shape fact, not an oracle or decoder hypothesis. -/
theorem production_folds_positive :
    ∀ p : Profile, ∀ i : Fin (config p).folds.size, 0 < (config p).folds[i.val]! := by
  decide +kernel

/-- The complete later-level query endpoint: the scalar history itself supplies
the digest at compressed log index i-1. Scheduled syntax and successful parsing
discharge phase availability; no root-position association is assumed. -/
theorem queryRows_decoded_rootLog (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List Pending) (ancestors : List (Pending × Sigma (@Sample (config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors = some out)
    (scheduled : WHIRHistory.scheduledAdmissible (config p) messages = true)
    (i : Fin (config p).folds.size) (phase : WHIRReplay.query p (s,messages) = .query i)
    (later : 0 < i.val) (x : Sample (.query i)) :
    ∃ digest, (rootLog p s messages)[i.val - 1]? = some digest ∧
      WHIRReplay.queryRows out i x =
        (QueryBatchSoundness.queries (remaining (config p) i + (config p).rates[i.val]!)
          (config p).queries[i.val]! x.1).map (fun q => (roots digest i.val)[q]!) := by
  have nonempty : messages ≠ [] := by
    intro empty
    subst messages
    cases parsed
  have depth := WHIRHistory.scheduledAdmissible_depth (config p) messages scheduled
  let cursor : Fin (WHIRHistory.depth (config p)) :=
    ⟨messages.length - 1, by have := List.length_pos_iff.mpr nonempty; omega⟩
  have current : position (.query i) = messages.length - 1 := by
    rw [← phase]
    change position (WHIRHistory.queryFor (config p) (s,messages)) = _
    rw [WHIRHistory.queryFor_at (config p) s messages cursor
      (by dsimp [cursor]; have := List.length_pos_iff.mpr nonempty; omega)]
    exact WHIRHistory.position_schedule_get (config p) cursor
  let previous : Fin (config p).folds.size := ⟨i.val - 1, by omega⟩
  have succ : i.val = previous.val + 1 := by dsimp [previous]; omega
  have positive := production_folds_positive p previous
  let j : Fin (config p).folds[previous.val]! := ⟨(config p).folds[previous.val]! - 1, by omega⟩
  have last : j.val + 1 = (config p).folds[previous.val]! := by dsimp [j]; omega
  have available : position (.fold previous j) < messages.length - 1 := by
    rw [← current, position_fold previous j out.tape, position_query i out.tape]
    have growth := CausalRefinement.levelStart_succ (challenges (config p) out.tape) previous.val
    rw [← succ, challenge_folds_size] at growth
    omega
  obtain ⟨digest, found, root⟩ := decoded_rootLog_slot p catalog roots rows s messages ancestors
    out parsed previous j last (by rw [← succ]; exact i.isLt)
    (fun k hk => production_folds_positive p ⟨k, by omega⟩) available
  refine ⟨digest, found, ?_⟩
  rw [queryRows_succ out i previous succ j last x, root]
  simp only [Option.getD_some, ← succ]

end Whir.WHIRQueryOracleRecurrence
