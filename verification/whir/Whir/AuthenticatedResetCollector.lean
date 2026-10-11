import Whir.RewindRowExtraction

/-! A black-box collector runs COMPLETE verifier trials. Acceptance, including
all tag/shape/algebra/authentication checks, gates every recorded response.
The executable path never reads a root preimage to manufacture a record. -/
namespace Whir.AuthenticatedResetSupport
open Concrete Protocol CausalGame CausalProbability KnowledgeExtraction RewindRowExtraction

/-- The actual verifier on supplied black-box replies. -/
def acceptedReplies (input : Public) (tape : Tape input.config) (answers : List Reply) : Bool :=
  let c := input.config
  let ch := challenges c tape
  if !(input.claims.all fun claim => shapeValid c input.lanes claim.weight) then false
  else
    let statement := batchClaims (2 ^ c.logN) input.claims tape.1
    match opening c ch answers.toArray with
    | .error _ => false
    | .ok proof => (verify c ch input.lanes (liftRoot input.root)
        statement.weight statement.value proof).isOk

theorem acceptedReplies_actual (input : Public) (strategy : Strategy) (tape : Tape input.config) :
    acceptedReplies input tape (run strategy input []
      (visibleBatches input.config tape.1 (challenges input.config tape))) =
        experiment input strategy tape := by rfl

/-- Rejection or a malformed position list returns no data, not a default row. -/
def acceptedRecords (input : Public) (tape : Tape input.config)
    (level : Fin input.config.folds.size) (depth : Nat) (answers : List Reply) :
    List (Fin (2 ^ depth) × Array E) :=
  if acceptedReplies input tape answers then
    let ch := challenges input.config tape
    let proof := decodedOpening input.config ch answers.toArray
    match deriveQueries depth input.config.queries[level.val]! ch.levels[level.val]!.querySqueezes with
    | none => []
    | some positions =>
      if valid : positions.size = input.config.queries[level.val]! ∧
          ∀ i : Fin input.config.queries[level.val]!, positions[i.val]! < 2 ^ depth then
        List.ofFn fun i : Fin input.config.queries[level.val]! =>
          (⟨positions[i.val]!, valid.2 i⟩, proof.levels[level.val]!.rows[i.val]!)
      else []
  else []

def trialRecords (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (depth : Nat) :
    List (Fin (2 ^ depth) × Array E) :=
  acceptedRecords prover.input tape level depth (run prover.respond prover.input []
    (visibleBatches prover.input.config tape.1 (challenges prover.input.config tape)))

theorem acceptedRecords_length_le (input : Public) (tape : Tape input.config)
    (level : Fin input.config.folds.size) (depth : Nat) (answers : List Reply) :
    (acceptedRecords input tape level depth answers).length ≤ input.config.queries[level.val]! := by
  unfold acceptedRecords
  split
  · dsimp only
    split
    · simp
    · split <;> simp
  · simp

theorem rejected_no_records (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (depth : Nat)
    (rejected : experiment prover.input prover.respond tape = false) :
    trialRecords prover tape level depth = [] := by
  simp [trialRecords, acceptedRecords, acceptedReplies_actual, rejected]

/-- All records, not just records from an honest strategy, satisfy the actual
verifier's authentication equation. The depth premise is purely static shape. -/
theorem trialRecords_authenticated (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (depth : Nat)
    (shape : (CausalExecution.foldAt prover.input prover.respond tape level
      prover.input.config.folds[level.val]!).n + prover.input.config.rates[level.val]! = depth) :
    ∀ record ∈ trialRecords prover tape level depth,
      record.2 = (CausalExecution.levelAt prover.input prover.respond tape level).oracle[record.1.val]! := by
  intro record member
  unfold trialRecords acceptedRecords at member
  split at member
  · rename_i accepted
    rw [acceptedReplies_actual] at accepted
    obtain ⟨positions, sampled, rowCount, auth⟩ := accepted_queries_authenticated
      prover.input prover.respond tape accepted level
    rw [shape] at sampled
    simp only [sampled] at member
    split at member
    · rename_i valid
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      have authentic := auth i.val (by rw [valid.1]; exact i.isLt)
      simpa [bne, CausalExecution.proof, CausalTerminal.proof] using authentic
    · simp at member
  · simp at member

/-- Each message is obtained by legal strict-prefix replay; earlier replies are
never passed to the black box by the extractor. -/
def trialProgram (input : Public) (historyPrefix : List Batch) : List Batch →
    (List Reply → RewindProgram input.config input.lanes) → RewindProgram input.config input.lanes
  | [], finish => finish []
  | message :: rest, finish =>
    .query historyPrefix message (fun reply =>
      trialProgram input (historyPrefix ++ [message]) rest (fun replies => finish (reply :: replies)))

/-- A collection of full trials, stopped only by its supplied output checker. -/
def collectAcceptedProgram (input : Public) (level : Fin input.config.folds.size) (depth : Nat) :
    List (Tape input.config) → (List (Fin (2 ^ depth) × Array E) → Option (Witness input.config input.lanes)) →
      RewindProgram input.config input.lanes
  | [], finish => .finish (finish [])
  | tape :: tapes, finish =>
    trialProgram input [] (visibleBatches input.config tape.1 (challenges input.config tape))
      (fun replies => collectAcceptedProgram input level depth tapes
        (fun records => finish (acceptedRecords input tape level depth replies ++ records)))

def collectedRecords (prover : CommittedProver) (level : Fin prover.input.config.folds.size)
    (depth : Nat) (tapes : List (Tape prover.input.config)) : List (Fin (2 ^ depth) × Array E) :=
  tapes.flatMap (fun tape => trialRecords prover tape level depth)

theorem collectedRecords_length_le (prover : CommittedProver) (level : Fin prover.input.config.folds.size)
    (depth : Nat) (tapes : List (Tape prover.input.config)) :
    (collectedRecords prover level depth tapes).length ≤ tapes.length * prover.input.config.queries[level.val]! := by
  induction tapes with
  | nil => simp [collectedRecords]
  | cons tape tapes ih =>
    simpa only [collectedRecords, trialRecords, List.flatMap_cons, List.length_append,
      List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add (acceptedRecords_length_le prover.input tape level depth _) ih

theorem replayPast_append (input : Public) (strategy : Strategy) (past : History)
    (left right : List Batch) :
    replayPast input strategy past (left ++ right) =
      replayPast input strategy (replayPast input strategy past left) right := by
  induction left generalizing past with
  | nil => rfl
  | cons message left ih => simp only [List.cons_append, replayPast, ih]

/-- Count every response and every replay, including rejected trials. This is
an interaction count, not a unit-cost runtime claim: verifier field arithmetic,
coordinate comparisons, list/array allocation and the prover's own work are
separate. The data bound counts retained authenticated coordinate/row records;
arbitrary untrusted reply allocation is not charged as field arithmetic. -/
def trialCalls : Nat → Nat → Nat
  | _, 0 => 0
  | start, count + 1 => trialCalls (start + 1) count + start + 1

theorem run_trialProgram (input : Public) (strategy : Strategy) (historyPrefix messages : List Batch)
    (maxReplay extra : Nat) (within : historyPrefix.length + messages.length ≤ maxReplay)
    (finish : List Reply → RewindProgram input.config input.lanes) :
    runRewind input strategy maxReplay (messages.length + extra)
      (trialProgram input historyPrefix messages finish) =
    let result := runRewind input strategy maxReplay extra
      (finish (run strategy input (replayPast input strategy [] historyPrefix) messages))
    ⟨result.output, result.responseCalls + trialCalls historyPrefix.length messages.length⟩ := by
  induction messages generalizing historyPrefix finish with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, trialProgram, run, trialCalls, Nat.add_zero]
  | cons message messages ih =>
    have current : historyPrefix.length ≤ maxReplay := by simp only [List.length_cons] at within; omega
    have later : (historyPrefix ++ [message]).length + messages.length ≤ maxReplay := by
      simpa [List.length_cons, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using within
    rw [List.length_cons, show messages.length + 1 + extra = (messages.length + extra) + 1 by omega]
    simp only [trialProgram, runRewind, ite_eq_left current]
    rw [ih (historyPrefix ++ [message]) later]
    simp only [run, replayPast_append, replayPast, List.length_append, List.length_singleton,
      trialCalls]
    congr 1
    omega

def collectionFuel (input : Public) (tapes : List (Tape input.config)) : Nat :=
  (tapes.map fun tape => (visibleBatches input.config tape.1 (challenges input.config tape)).length).sum

def collectionCalls (input : Public) (tapes : List (Tape input.config)) : Nat :=
  (tapes.map fun tape => trialCalls 0
    (visibleBatches input.config tape.1 (challenges input.config tape)).length).sum

theorem run_collectAcceptedProgram (prover : CommittedProver)
    (level : Fin prover.input.config.folds.size) (depth maxReplay : Nat)
    (tapes : List (Tape prover.input.config))
    (within : ∀ tape ∈ tapes,
      (visibleBatches prover.input.config tape.1 (challenges prover.input.config tape)).length ≤ maxReplay)
    (finish : List (Fin (2 ^ depth) × Array E) → Option (Witness prover.input.config prover.input.lanes)) :
    runRewind prover.input prover.respond maxReplay (collectionFuel prover.input tapes)
      (collectAcceptedProgram prover.input level depth tapes finish) =
        ⟨finish (collectedRecords prover level depth tapes), collectionCalls prover.input tapes⟩ := by
  induction tapes generalizing finish with
  | nil => simp [collectAcceptedProgram, collectionFuel, collectionCalls, collectedRecords, runRewind]
  | cons tape tapes ih =>
    simp only [collectAcceptedProgram, collectionFuel, List.map_cons, List.sum_cons]
    rw [run_trialProgram _ _ [] _ maxReplay _ (by simpa using within tape (by simp))]
    dsimp only
    simp only [collectionFuel] at ih
    rw [ih (fun t ht => within t (by simp [ht]))]
    simp [replayPast, collectedRecords, trialRecords, collectionCalls, Nat.add_comm]

/-- Acceptance itself ensures data availability for each actual sampled
coordinate; parsing success is proved, not assumed of the malicious prover. -/
theorem trialRecords_contains (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (depth : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64)
    (query : RewindCoverage.QueryTape depth prover.input.config.queries[level.val]!)
    (squeezes : (challenges prover.input.config tape).levels[level.val]!.querySqueezes = Array.ofFn query)
    (accepted : experiment prover.input prover.respond tape = true)
    (i : Fin prover.input.config.queries[level.val]!) :
    ∃ record ∈ trialRecords prover tape level depth,
      record.1 = RewindCoverage.sampledPosition depth _ positive noWrap query i := by
  unfold trialRecords acceptedRecords
  rw [acceptedReplies_actual, accepted]
  simp only [ite_true]
  rw [squeezes, SamplingProbability.deriveQueries_eq depth _ positive noWrap]
  have valid : (Concrete.tab prover.input.config.queries[level.val]! fun j =>
      SamplingProbability.concretePlace prover.input.config.queries[level.val]! depth j
        (Layout.rawQuery depth (fun k => (Array.ofFn query)[k]!.toNat) j)).size =
      prover.input.config.queries[level.val]! ∧
      ∀ j : Fin prover.input.config.queries[level.val]!,
        (Concrete.tab prover.input.config.queries[level.val]! fun j =>
          SamplingProbability.concretePlace prover.input.config.queries[level.val]! depth j
            (Layout.rawQuery depth (fun k => (Array.ofFn query)[k]!.toNat) j))[j.val]! < 2 ^ depth := by
    constructor
    · simp
    · intro j
      rw [ArrayLayout.getElem!_tab _ _ _ j.isLt,
        ← RewindCoverage.sampledPosition_actual depth _ positive noWrap query j]
      exact (RewindCoverage.sampledPosition depth _ positive noWrap query j).isLt
  simp only [dite_eq_left valid]
  refine ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  apply Fin.ext
  simpa only [Prod.fst, Fin.val_mk, ArrayLayout.getElem!_tab _ _ _ i.isLt] using
    (RewindCoverage.sampledPosition_actual depth _ positive noWrap query i).symm

#print axioms run_trialProgram
#print axioms run_collectAcceptedProgram
#print axioms trialRecords_contains

#print axioms trialRecords_authenticated
#print axioms rejected_no_records
#print axioms collectedRecords_length_le
end Whir.AuthenticatedResetSupport
