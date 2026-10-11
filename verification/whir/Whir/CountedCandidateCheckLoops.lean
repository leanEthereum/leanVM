import Whir.CountedCandidateCheck

/-! Non-field resource units for the actual finite record preparation loops. Lookup comparisons, output slots and row words are charged separately from field arithmetic. Root/response shapes are consumer restrictions, not a consequence of acceptance used to bound arbitrary raw replies. -/
namespace Whir.CountedCandidateCheck
open Concrete Protocol CausalGame SupportedCandidateExtraction PCSRewindExtractor
open scoped BigOperators

/-- One comparison for each actually visited record, stopping at the first hit. -/
def countedLookup {N : Nat} {F : Type*} : List (Fin N × F) → Fin N → Option F × Nat
  | [], _ => (none, 0)
  | (position, value) :: rest, target =>
    if target = position then (some value, 1)
    else
      let tail := countedLookup rest target
      (tail.1, tail.2 + 1)

theorem countedLookup_value {N : Nat} {F : Type*} (records : List (Fin N × F)) (q : Fin N) :
    (countedLookup records q).1 = RewindRowExtraction.lookup records q := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    cases record
    simp only [countedLookup, RewindRowExtraction.lookup]
    split <;> simp [ih]

theorem countedLookup_cost {N : Nat} {F : Type*} (records : List (Fin N × F)) (q : Fin N) :
    (countedLookup records q).2 ≤ records.length := by
  induction records with
  | nil => simp [countedLookup]
  | cons record records ih =>
    cases record
    simp only [countedLookup, List.length_cons]
    split <;> simp_all

def countedFilledRecords (input : Public) (records : List (Record input.config)) :
    Array (Option (Array K)) × Nat :=
  let looked := Array.ofFn fun q : Fin (blockLength input.config) => countedLookup records q
  (looked.map Prod.fst, (looked.map Prod.snd).toList.sum)

theorem countedFilledRecords_value (input : Public) (records : List (Record input.config)) :
    (countedFilledRecords input records).1 = filledRecords input records := by
  simp [countedFilledRecords, filledRecords, Array.map_ofFn, Function.comp_def, countedLookup_value]

theorem countedFilledRecords_cost (input : Public) (records : List (Record input.config)) :
    (countedFilledRecords input records).2 ≤ blockLength input.config * records.length := by
  simp only [countedFilledRecords, Array.toList_map, Array.toList_ofFn,
    List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _q : Fin (blockLength input.config), records.length := by
      apply Finset.sum_le_sum
      intro q _
      exact countedLookup_cost records q
    _ = _ := by simp

/-- Actual receivedLaneCached tables materialize one slot per node per occupied lane. Missing entries are zero filled through the same source accessor. -/
def countedReceivedTables (input : Public) (records : List (Record input.config)) :
    Array (Array E) × Nat :=
  let filled := countedFilledRecords input records
  let received := Array.ofFn fun lane : Fin input.lanes =>
    Array.ofFn (receivedLaneCached input filled.1 lane)
  (received, filled.2 + input.lanes * blockLength input.config)

theorem countedReceivedTables_value (input : Public) (records : List (Record input.config)) :
    (countedReceivedTables input records).1 =
      Array.ofFn (fun lane : Fin input.lanes => Array.ofFn (receivedLane input records lane)) := by
  simp [countedReceivedTables, countedFilledRecords_value, receivedLane]

theorem countedReceivedTables_cost (input : Public) (records : List (Record input.config)) :
    (countedReceivedTables input records).2 ≤
      blockLength input.config * records.length + input.lanes * blockLength input.config := by
  have h := countedFilledRecords_cost input records
  dsimp [countedReceivedTables]
  omega

/-- No successful output can hide an unbounded array allocation: the literal output dimension is fixed before running the extractor. -/
theorem output_length (input : Public) (w : Witness input.config input.lanes) :
    (Array.ofFn w).size = input.lanes * width input.config := by simp

/-- Configuration scalars and public structural slots. -/
def publicHeaderWords (c : Config) : Nat :=
  8 + c.folds.size + c.rates.size + c.queries.size + c.oodCounts.size

/-- Consumed 64-bit words plus structural slots. E weights and values each contain three K-sized words. Prover time and discarded raw allocation are not asserted to be bounded by this public/retained-record admission count. -/
def consumedWords (input : Public) (records : List (Record input.config)) : Nat :=
  publicHeaderWords input.config + input.root.size + (input.root.toList.map Array.size).sum +
    (input.claims.toList.map (fun claim => 3 * claim.weight.size + 4)).sum +
    (records.map (fun record => record.2.size + 2)).sum

theorem consumedWords_bound (input : Public) (records : List (Record input.config))
    (recordLimit claimLimit : Nat) (consumer : ConsumerInput input recordLimit claimLimit records) :
    consumedWords input records ≤ publicHeaderWords input.config +
      blockLength input.config * (input.lanes + 1) +
      claimLimit * (3 * laneCount input.config * width input.config + 4) +
      recordLimit * (input.lanes + 2) := by
  have root : (input.root.toList.map Array.size).sum = blockLength input.config * input.lanes := by
    have eq : input.root.toList.map Array.size = input.root.toList.map (fun _ => input.lanes) := by
      apply List.map_congr_left
      intro row member
      exact consumer.rootLanes row member
    rw [eq]
    simp [consumer.rootRows]
  have claims := List.sum_le_length_nsmul
    (input.claims.toList.map (fun claim => 3 * claim.weight.size + 4))
    (3 * (laneCount input.config * width input.config) + 4) (by
      intro size member
      obtain ⟨claim, hc, rfl⟩ := List.mem_map.mp member
      rw [consumer.claimWeights claim hc])
  have rows := List.sum_le_length_nsmul (records.map (fun record => record.2.size + 2))
    (input.lanes + 2) (by
      intro size member
      obtain ⟨record, hr, rfl⟩ := List.mem_map.mp member
      rw [consumer.recordRows record hr])
  simp at claims rows
  have cb := Nat.mul_le_mul_right (3 * (laneCount input.config * width input.config) + 4) consumer.claims
  have rb := Nat.mul_le_mul_right (input.lanes + 2) consumer.recordCount
  unfold consumedWords
  rw [root, consumer.rootRows]
  simp [Nat.mul_assoc] at claims rows ⊢
  nlinarith

/-- The real short-circuit all loop, retaining the number of visited entries. -/
def countedAll {F : Type*} (predicate : F → Bool) : List F → Bool × Nat
  | [] => (true, 0)
  | x :: xs =>
    if predicate x then
      let tail := countedAll predicate xs
      (tail.1, tail.2 + 1)
    else (false, 1)

theorem countedAll_value {F : Type*} (predicate : F → Bool) (xs : List F) :
    (countedAll predicate xs).1 = xs.all predicate := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [countedAll, List.all_cons]; split <;> simp_all

theorem countedAll_cost {F : Type*} (predicate : F → Bool) (xs : List F) :
    (countedAll predicate xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [countedAll]
  | cons x xs ih => simp only [countedAll, List.length_cons]; split <;> simp_all

/-- One row-size comparison plus up to three base-component comparisons per actually visited E entry. This is not charged as a field operation. -/
def countedRowMatches (c : Config) (lanes : Nat) (encoded : Array (Array E)) (record : Record c) :
    Bool × Nat :=
  if record.2.size == lanes then
    let checked := countedAll (fun lane : Fin (laneCount c) =>
      (encoded[lane.val]!)[record.1.val]! == E.ofK (recordLane lanes record.2 lane.val))
      (List.finRange (laneCount c))
    (checked.1, 1 + 3 * checked.2)
  else (false, 1)

theorem countedRowMatches_value (c : Config) (lanes : Nat) (encoded : Array (Array E)) (record : Record c) :
    (countedRowMatches c lanes encoded record).1 = rowMatches c lanes encoded record := by
  unfold countedRowMatches rowMatches
  split <;> simp_all [countedAll_value]

theorem countedRowMatches_cost (c : Config) (lanes : Nat) (encoded : Array (Array E)) (record : Record c) :
    (countedRowMatches c lanes encoded record).2 ≤ 1 + 3 * laneCount c := by
  unfold countedRowMatches
  split
  · dsimp only
    have h := countedAll_cost (fun lane : Fin (laneCount c) =>
      (encoded[lane.val]!)[record.1.val]! == E.ofK (recordLane lanes record.2 lane.val))
      (List.finRange (laneCount c))
    simpa using Nat.add_le_add_left (Nat.mul_le_mul_left 3 h) 1
  · omega

def countedFilter {F : Type*} (predicate : F → Bool × Nat) :
    List F → List F × Nat
  | [] => ([], 0)
  | x :: xs =>
    let checked := predicate x
    let tail := countedFilter predicate xs
    (if checked.1 then x :: tail.1 else tail.1, checked.2 + tail.2)

theorem countedFilter_value {F : Type*} (predicate : F → Bool × Nat) (xs : List F) :
    (countedFilter predicate xs).1 = xs.filter (fun x => (predicate x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countedFilter, List.filter_cons, ih]

theorem countedFilter_cost {F : Type*} (predicate : F → Bool × Nat) (xs : List F)
    (bound : Nat) (charges : ∀ x ∈ xs, (predicate x).2 ≤ bound) :
    (countedFilter predicate xs).2 ≤ xs.length * bound := by
  induction xs with
  | nil => simp [countedFilter]
  | cons x xs ih =>
    have head := charges x (by simp)
    have tail := ih (fun x hx => charges x (by simp [hx]))
    dsimp [countedFilter]
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Cache is shared with every record. The source coordinate deduplication is retained literally; its insertion scan upper charge is length*(length+1). The row-match comparison counter is from the actual short-circuit lane loop. -/
def countedCommonCoordinates (c : Config) (lanes : Nat) (candidate : Array E)
    (records : List (Record c)) : Finset (Fin (blockLength c)) × Nat :=
  let encoded := encodedLanes c candidate
  let matched := countedFilter (countedRowMatches c lanes encoded) records
  let coordinates := matched.1.map Prod.fst
  (coordinates.toFinset, matched.2 + coordinates.length * (coordinates.length + 1))

theorem countedCommonCoordinates_value (c : Config) (lanes : Nat) (candidate : Array E)
    (records : List (Record c)) :
    (countedCommonCoordinates c lanes candidate records).1 = commonCoordinates c lanes candidate records := by
  simp [countedCommonCoordinates, commonCoordinates, countedFilter_value, countedRowMatches_value]

theorem countedCommonCoordinates_cost (c : Config) (lanes : Nat) (candidate : Array E)
    (records : List (Record c)) :
    (countedCommonCoordinates c lanes candidate records).2 ≤
      records.length * (1 + 3 * laneCount c) + records.length * (records.length + 1) := by
  have row := countedFilter_cost (countedRowMatches c lanes (encodedLanes c candidate)) records
    (1 + 3 * laneCount c) (by intros; apply countedRowMatches_cost)
  have length : (countedFilter (countedRowMatches c lanes (encodedLanes c candidate)) records).1.length ≤
      records.length := by
    rw [countedFilter_value]
    exact List.length_filter_le _ _
  dsimp [countedCommonCoordinates]
  simp only [List.length_map]
  nlinarith

end Whir.CountedCandidateCheck
