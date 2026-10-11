import Whir.KnowledgeExtraction
import Whir.CausalPrefix
import Whir.RewindCoverage

/-! Fixed-input reset access and deterministic reconstruction from authenticated records. Every response is obtained by replaying the same committed prover history with fixed coins. Coverage and authentication are explicit access premises, not consequences of acceptance or primitive collision resistance. This interface cannot change public claims and grants no Fiat-Shamir reset ability. -/
namespace Whir.RewindRowExtraction
open Concrete Protocol CausalGame KnowledgeExtraction

structure QueryRequest where
  level : Nat
  squeezes : Array E
  lambda : E

def QueryRequest.batch (request : QueryRequest) : Batch :=
  .query request.level request.squeezes request.lambda

structure Collected where
  replies : List Reply
  responseCalls : Nat

/-- Replays are real black-box calls. A prefix is replayed once for each request; replies are never supplied by the extractor. -/
def collect (input : Public) (strategy : Strategy) (historyPrefix : List Batch) :
    List QueryRequest → Collected
  | [] => ⟨[], 0⟩
  | request :: rest =>
    let past := replayPast input strategy [] historyPrefix
    let answer := strategy input past request.batch
    let result := collect input strategy historyPrefix rest
    ⟨answer :: result.replies, result.responseCalls + historyPrefix.length + 1⟩

theorem collect_replies (input : Public) (strategy : Strategy) (historyPrefix : List Batch)
    (requests : List QueryRequest) :
    (collect input strategy historyPrefix requests).replies = requests.map (fun request =>
      strategy input (replayPast input strategy [] historyPrefix) request.batch) := by
  induction requests with
  | nil => rfl
  | cons request rest ih => simp [collect, ih]

theorem collect_responseCalls (input : Public) (strategy : Strategy) (historyPrefix : List Batch)
    (requests : List QueryRequest) :
    (collect input strategy historyPrefix requests).responseCalls =
      requests.length * (historyPrefix.length + 1) := by
  induction requests with
  | nil => simp [collect]
  | cons request rest ih => simp [collect, ih, Nat.add_mul, Nat.mul_add]; omega

/-- The collector expressed in the bounded reset machine. Its continuation consumes replies actually returned by the black box. -/
def collectProgram (input : Public) (historyPrefix : List Batch) :
    List QueryRequest → (List Reply → Option (Witness input.config input.lanes)) →
      RewindProgram input.config input.lanes
  | [], finish => .finish (finish [])
  | request :: rest, finish =>
    .query historyPrefix request.batch (fun reply =>
      collectProgram input historyPrefix rest (fun replies => finish (reply :: replies)))

theorem run_collectProgram (input : Public) (strategy : Strategy) (historyPrefix : List Batch)
    (maxReplay : Nat) (within : historyPrefix.length ≤ maxReplay)
    (requests : List QueryRequest) (finish : List Reply → Option (Witness input.config input.lanes)) :
    runRewind input strategy maxReplay requests.length
      (collectProgram input historyPrefix requests finish) =
        ⟨finish (collect input strategy historyPrefix requests).replies,
          (collect input strategy historyPrefix requests).responseCalls⟩ := by
  induction requests generalizing finish with
  | nil => rfl
  | cons request rest ih =>
    simp only [collectProgram, List.length_cons, runRewind, ite_eq_left within]
    rw [ih]
    rfl


open CausalProbability in
/-- The prefix is taken from the verifier's actual wire stream, not selected by an oracle-access assumption. -/
def queryPrefix (input : Public) (tape : Tape input.config)
    (level : Fin input.config.folds.size) : List Batch :=
  (visibleBatches input.config tape.1 (challenges input.config tape)).take
    (position (.query level))

open CausalProbability in
def resetRequest (input : Public) (level : Fin input.config.folds.size)
    (sample : Sample (.query level)) : QueryRequest :=
  ⟨level.val, Array.ofFn sample.1, sample.2⟩

open CausalProbability in
/-- An allowed reset changes only the current query coordinate. The committed input and all earlier verifier messages remain identical. -/
theorem queryPrefix_reset (input : Public) (tape : Tape input.config)
    (level : Fin input.config.folds.size) (sample : Sample (.query level)) :
    queryPrefix input (set (.query level) tape sample) level =
      queryPrefix input tape level :=
  visible_prefix (.query level) tape sample

open CausalProbability in
theorem resetRequest_actual_batch (input : Public) (tape : Tape input.config)
    (level : Fin input.config.folds.size) (sample : Sample (.query level)) :
    (resetRequest input level sample).batch =
      challengeBatch (.query level) (set (.query level) tape sample) := by
  rw [challengeBatch_eq, get_set]
  rfl

open CausalProbability in
/-- Independent product-seed query coordinates are each replayed at this same real verifier prefix, with fixed prover coins. -/
def collectResets (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (rounds : Nat)
    (seed : Fin rounds → Sample (.query level)) : Collected :=
  collect prover.input prover.respond (queryPrefix prover.input tape level)
    (List.ofFn fun round => resetRequest prover.input level (seed round))

open CausalProbability in
theorem collectResets_responseCalls (prover : CommittedProver)
    (tape : Tape prover.input.config) (level : Fin prover.input.config.folds.size)
    (rounds : Nat) (seed : Fin rounds → Sample (.query level)) :
    (collectResets prover tape level rounds seed).responseCalls =
      rounds * ((queryPrefix prover.input tape level).length + 1) := by
  simp [collectResets, collect_responseCalls]

open CausalProbability in
theorem collectResets_responseCalls_le (prover : CommittedProver)
    (tape : Tape prover.input.config) (level : Fin prover.input.config.folds.size)
    (rounds : Nat) (seed : Fin rounds → Sample (.query level)) :
    (collectResets prover tape level rounds seed).responseCalls ≤
      rounds * (position (.query level) + 1) := by
  rw [collectResets_responseCalls]
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right (List.length_take_le _ _) 1

/-- Acceptance supplies authentic query rows through the actual verifier guard. This is an ideal-oracle equality, not a proof that a digest exposes its full preimage. -/
theorem accepted_queries_authenticated (input : Public) (strategy : Strategy)
    (tape : Tape input.config) (accepted : experiment input strategy tape = true)
    (level : Fin input.config.folds.size) :
    ∃ positions,
      deriveQueries ((CausalExecution.foldAt input strategy tape level
        input.config.folds[level.val]!).n + input.config.rates[level.val]!)
        input.config.queries[level.val]!
        (challenges input.config tape).levels[level.val]!.querySqueezes = some positions ∧
      (CausalExecution.proof input strategy tape).levels[level.val]!.rows.size = positions.size ∧
      ∀ j, j < positions.size →
        ((CausalExecution.proof input strategy tape).levels[level.val]!.rows[j]! !=
          (CausalExecution.levelAt input strategy tape level).oracle[positions[j]!]!) = false := by
  have result := OperationalRefinement.verifyLevel_success input.config
    (challenges input.config tape) (CausalExecution.proof input strategy tape) level _ _
    (CausalExecution.accepted_level input strategy tape accepted level level.isLt)
  dsimp only at result
  have endEq := ExecutionShapes.foldAt_end input strategy tape level level.isLt
  dsimp only [CausalExecution.block] at endEq
  rw [← endEq] at result
  obtain ⟨_, _, positions, sampled, rowCount, auth, _⟩ := result
  exact ⟨positions, sampled, rowCount, by simpa only [ExecutionShapes.foldAt_oracle] using auth⟩

open CausalProbability in
/-- All accepted reset trials at a query authenticate against this same prefix-fixed oracle. Current query randomness cannot replace it. -/
theorem reset_oracle_fixed (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (level : Fin input.config.folds.size) (sample : Sample (.query level)) :
    (CausalExecution.levelAt input strategy (set (.query level) tape sample) level).oracle =
      (CausalExecution.levelAt input strategy tape level).oracle := by
  have fixed := CausalStateCausality.levelAt_set input strategy (.query level) tape sample
    level level.isLt.le (by rw [CausalPositions.position_query level tape]; omega)
  exact congrArg CheckedState.oracle fixed
/-- Parsing is restricted to actual query replies. A malformed tag supplies no row. -/
def rows (reply : Reply) : Option Oracle :=
  match reply with
  | .query rows _ => some rows
  | _ => none

section Records
variable {F : Type*} [Zero F] {N : Nat}
omit [Zero F]

/-- Coordinates refer to one fixed committed word. This is not an oracle call. -/
def lookup : List (Fin N × F) → Fin N → Option F
  | [], _ => none
  | (position, value) :: rest, target =>
    if target = position then some value else lookup rest target

/-- Count the coordinate comparisons executed by exactly the same lookup. -/
def countedLookup : List (Fin N × F) → Fin N → Option F × Nat
  | [], _ => (none, 0)
  | (position, value) :: rest, target =>
    if target = position then (some value, 1)
    else
      let result := countedLookup rest target
      (result.1, result.2 + 1)

omit [Zero F] in
theorem countedLookup_value (records : List (Fin N × F)) (target : Fin N) :
    (countedLookup records target).1 = lookup records target := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
    rcases record with ⟨position, value⟩
    simp only [countedLookup, lookup]
    split_ifs <;> simp_all

omit [Zero F] in
theorem countedLookup_comparisons (records : List (Fin N × F)) (target : Fin N) :
    (countedLookup records target).2 ≤ records.length := by
  induction records with
  | nil => simp [countedLookup]
  | cons record rest ih =>
    rcases record with ⟨position, value⟩
    simp only [countedLookup]
    split_ifs <;> simp_all

omit [Zero F] in
theorem lookup_authenticated (records : List (Fin N × F)) (committed : Fin N → F)
    (authenticated : ∀ record ∈ records, record.2 = committed record.1)
    (target : Fin N) (covered : ∃ record ∈ records, record.1 = target) :
    lookup records target = some (committed target) := by
  induction records with
  | nil => simp at covered
  | cons record rest ih =>
    rcases record with ⟨position, value⟩
    simp only [lookup]
    split_ifs with same
    · subst target
      simpa using congrArg some (authenticated (position, value) (by simp))
    · apply ih (fun record member => authenticated record (by simp [member]))
      obtain ⟨record, member, positionEq⟩ := covered
      rcases List.mem_cons.mp member with first | later
      · subst record
        exact False.elim (same positionEq.symm)
      · exact ⟨record, later, positionEq⟩

/-- Missing coordinates fail. The complete-word interface does not invent authenticated answers or fill erasures with guessed values. -/
def assemble (records : List (Fin N × F)) : Option (Vector F N) :=
  if complete : ∀ i, (lookup records i).isSome = true then
    some (Vector.ofFn fun i => (lookup records i).get (complete i))
  else none

theorem assemble_eq_committed (records : List (Fin N × F)) (committed : Fin N → F)
    (authenticated : ∀ record ∈ records, record.2 = committed record.1)
    (covered : ∀ target, ∃ record ∈ records, record.1 = target) :
    assemble records = some (Vector.ofFn committed) := by
  have complete : ∀ i, (lookup records i).isSome = true := by
    intro target
    rw [lookup_authenticated records committed authenticated target (covered target)]
    rfl
  simp only [assemble, dite_eq_left complete]
  congr 2
  funext target
  simp [lookup_authenticated records committed authenticated target (covered target)]

/-- One coordinate-by-coordinate pass. Assembly may scan twice, once for coverage and once for values, so the complete assembler uses at most twice this bound. Field arithmetic and verifier work are not included. -/
def assemblyComparisons (records : List (Fin N × F)) : Nat :=
  ∑ i : Fin N, (countedLookup records i).2

theorem assemblyComparisons_le (records : List (Fin N × F)) :
    assemblyComparisons records ≤ N * records.length := by
  calc
    assemblyComparisons records ≤ ∑ _ : Fin N, records.length :=
      Finset.sum_le_sum fun i _ => countedLookup_comparisons records i
    _ = N * records.length := by simp

end Records

/-- Compose authenticated access-log reconstruction with the actual supported-row decoder. No dense-root reads occur inside this algorithm. Coverage remains a caller obligation, not an assumed sampling probability. -/
def extractRecords (n rate : Nat) (noWrap : n + rate ≤ 64)
    (records : List (Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n × E)) :
    Option (Array K) :=
  (assemble records).bind (ConcreteRowExtraction.extractRow n rate noWrap)

/-- Execute the certified counter of the same complete source-row decoder after real record assembly. Incomplete access performs no decoder arithmetic. Comparisons, memory and reset response calls remain separately charged. -/
def countedExtractRecords (n rate : Nat) (noWrap : n + rate ≤ 64)
    (records : List (Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n × E)) :
    Option (Array K) × Nat :=
  match assemble records with
  | none => (none, 0)
  | some received => ConcreteRowExtraction.countedExtractRow n rate noWrap received

theorem countedExtractRecords_value (n rate : Nat) (noWrap : n + rate ≤ 64)
    (records : List (Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n × E)) :
    (countedExtractRecords n rate noWrap records).1 = extractRecords n rate noWrap records := by
  unfold countedExtractRecords extractRecords
  cases assembled : assemble records with
  | none => rfl
  | some received =>
    simpa using ConcreteRowExtraction.countedExtractRow_value n rate noWrap received

theorem countedExtractRecords_polynomial_cost (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate))
    (records : List (Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n × E)) :
    (countedExtractRecords n rate noWrap records).2 ≤
      ConcreteRowExtraction.rowArithmeticPolynomial (2 ^ (n + rate)) := by
  unfold countedExtractRecords
  cases assembled : assemble records with
  | none => exact Nat.zero_le _
  | some received =>
    exact ConcreteRowExtraction.countedExtractRow_polynomial_cost n rate noWrap redundancy received

#print axioms countedExtractRecords_value
#print axioms countedExtractRecords_polynomial_cost

theorem extractRecords_recovers (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate)) (a : Array K) (shape : a.size = 2 ^ n)
    (committed : Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n → E)
    (records : List (Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n × E))
    (authenticated : ∀ record ∈ records, record.2 = committed record.1)
    (covered : ∀ target, ∃ record ∈ records, record.1 = target)
    (radius : 2 * hammingDist committed
      (fun i => (encode n rate (a.map E.ofK))[i.val]!) ≤ 2 ^ (n + rate) - 2 ^ n) :
    extractRecords n rate noWrap records = some a := by
  rw [extractRecords, assemble_eq_committed records committed authenticated covered,
    Option.bind_some]
  apply ConcreteRowExtraction.extractRow_recovers n rate noWrap redundancy a shape
  have getEq : (Vector.ofFn committed).get = committed := by
    funext i
    simp
  rwa [getEq]

/-- Parse a queried leaf lane without inspecting the public dense root. Invalid tags, indices, counts, or missing lane entries fail. Authentication must be established by the access reduction. -/
def parseLane (depth count lane : Nat) (request : QueryRequest) (reply : Reply) :
    Option (List (Fin (2 ^ depth) × E)) := do
  let positions ← deriveQueries depth count request.squeezes
  let leaves ← rows reply
  if valid : positions.size = count ∧ leaves.size = count ∧
      ∀ i : Fin count, positions[i.val]! < 2 ^ depth ∧ lane < leaves[i.val]!.size then
    return List.ofFn fun i : Fin count =>
      (⟨positions[i.val]!, (valid.2.2 i).1⟩, (leaves[i.val]!)[lane]!)
  else none

theorem parseLane_length (depth count lane : Nat) (request : QueryRequest) (reply : Reply)
    (records : List (Fin (2 ^ depth) × E))
    (parsed : parseLane depth count lane request reply = some records) :
    records.length = count := by
  unfold parseLane at parsed
  cases hp : deriveQueries depth count request.squeezes <;> simp [hp] at parsed
  cases hr : rows reply <;> simp [hr] at parsed
  obtain ⟨valid, rfl⟩ := parsed
  simp

/-- Every returned coordinate/value is from the actual query reply, with its order and repeated positions preserved. -/
theorem parseLane_authenticated (depth count lane : Nat) (request : QueryRequest)
    (reply : Reply) (records : List (Fin (2 ^ depth) × E))
    (committed : Fin (2 ^ depth) → E)
    (parsed : parseLane depth count lane request reply = some records)
    (auth : ∀ positions leaves,
      deriveQueries depth count request.squeezes = some positions → rows reply = some leaves →
      ∀ i : Fin count, ∀ bound : positions[i.val]! < 2 ^ depth,
        (leaves[i.val]!)[lane]! = committed ⟨positions[i.val]!, bound⟩) :
    ∀ record ∈ records, record.2 = committed record.1 := by
  unfold parseLane at parsed
  cases hp : deriveQueries depth count request.squeezes <;> simp [hp] at parsed
  cases hr : rows reply <;> simp [hr] at parsed
  obtain ⟨valid, rfl⟩ := parsed
  intro record member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  exact auth _ _ hp hr i _

theorem parseLane_contains_sampled (depth count lane : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) (request : QueryRequest) (reply : Reply)
    (tape : RewindCoverage.QueryTape depth count) (squeezes : request.squeezes = Array.ofFn tape)
    (records : List (Fin (2 ^ depth) × E))
    (parsed : parseLane depth count lane request reply = some records) (i : Fin count) :
    ∃ record ∈ records, record.1 = RewindCoverage.sampledPosition depth count positive noWrap tape i := by
  unfold parseLane at parsed
  rw [squeezes, SamplingProbability.deriveQueries_eq depth count positive noWrap] at parsed
  cases hr : rows reply <;> simp [hr] at parsed
  obtain ⟨valid, rfl⟩ := parsed
  refine ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  apply Fin.ext
  exact (RewindCoverage.sampledPosition_actual depth count positive noWrap tape i).symm

/-- The extractor consumes only the returned reset answers, not a freely readable committed word. A failed parse fails the whole extraction. -/
def parseReplies (depth count lane : Nat) :
    List QueryRequest → List Reply → Option (List (Fin (2 ^ depth) × E))
  | [], [] => some []
  | request :: requests, reply :: replies => do
    let first ← parseLane depth count lane request reply
    let rest ← parseReplies depth count lane requests replies
    return first ++ rest
  | _, _ => none

/-- Every parsed record from a selected real response remains in the aggregate access log. -/
theorem parseReplies_map_contains (depth count lane : Nat) (requests : List QueryRequest)
    (answer : QueryRequest → Reply) (records : List (Fin (2 ^ depth) × E))
    (parsed : parseReplies depth count lane requests (requests.map answer) = some records)
    (request : QueryRequest) (member : request ∈ requests)
    (first : List (Fin (2 ^ depth) × E))
    (parsedFirst : parseLane depth count lane request (answer request) = some first)
    (record : Fin (2 ^ depth) × E) (inFirst : record ∈ first) : record ∈ records := by
  induction requests generalizing records with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.map_cons, parseReplies] at parsed
    cases hf : parseLane depth count lane head (answer head) <;> simp [hf] at parsed
    cases ht : parseReplies depth count lane rest (rest.map answer) <;> simp [ht] at parsed
    cases parsed
    rcases List.mem_cons.mp member with same | later
    · subst request
      have equal := Option.some.inj (hf.symm.trans parsedFirst)
      subst first
      exact List.mem_append_left _ inFirst
    · exact List.mem_append_right _ (ih _ ht later)

theorem parseReplies_map_parsed (depth count lane : Nat) (requests : List QueryRequest)
    (answer : QueryRequest → Reply) (records : List (Fin (2 ^ depth) × E))
    (parsed : parseReplies depth count lane requests (requests.map answer) = some records)
    (request : QueryRequest) (member : request ∈ requests) :
    ∃ first, parseLane depth count lane request (answer request) = some first := by
  induction requests generalizing records with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.map_cons, parseReplies] at parsed
    cases hf : parseLane depth count lane head (answer head) <;> simp [hf] at parsed
    cases ht : parseReplies depth count lane rest (rest.map answer) <;> simp [ht] at parsed
    rcases List.mem_cons.mp member with same | later
    · subst request
      exact ⟨_, hf⟩
    · exact ih _ ht later

/-- Successful real-response parsing converts sampler coverage to complete access-log coverage. No missing answer is silently substituted. -/
theorem parsed_cover_of_sampler (depth count lane rounds : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) (seed : Fin rounds → RewindCoverage.QueryTape depth count)
    (requests : Fin rounds → QueryRequest) (squeezes : ∀ round, (requests round).squeezes = Array.ofFn (seed round))
    (answer : QueryRequest → Reply) (records : List (Fin (2 ^ depth) × E))
    (parsed : parseReplies depth count lane (List.ofFn requests)
      ((List.ofFn requests).map answer) = some records)
    (coverage : RewindCoverage.Covers depth count rounds positive noWrap seed) :
    ∀ target, ∃ record ∈ records, record.1 = target := by
  intro target
  obtain ⟨round, i, hit⟩ := coverage target
  have member : requests round ∈ List.ofFn requests := List.mem_ofFn.mpr ⟨round, rfl⟩
  obtain ⟨first, parsedFirst⟩ := parseReplies_map_parsed depth count lane _ answer records parsed _ member
  obtain ⟨record, inFirst, position⟩ := parseLane_contains_sampled depth count lane positive noWrap
    (requests round) (answer (requests round)) (seed round) (squeezes round) first parsedFirst i
  exact ⟨record, parseReplies_map_contains depth count lane _ answer records parsed _ member
    first parsedFirst record inFirst, position.trans hit⟩

theorem parseReplies_length (depth count lane : Nat) (requests : List QueryRequest)
    (replies : List Reply) (records : List (Fin (2 ^ depth) × E))
    (parsed : parseReplies depth count lane requests replies = some records) :
    records.length = requests.length * count := by
  induction requests generalizing replies records with
  | nil =>
    cases replies <;> simp [parseReplies] at parsed
    cases parsed
    simp
  | cons request requests ih =>
    cases replies with
    | nil => simp [parseReplies] at parsed
    | cons reply replies =>
      simp only [parseReplies] at parsed
      cases hf : parseLane depth count lane request reply <;> simp [hf] at parsed
      cases ht : parseReplies depth count lane requests replies <;> simp [ht] at parsed
      cases parsed
      simp [parseLane_length _ _ _ _ _ _ hf, ih _ _ ht, Nat.add_mul, Nat.add_comm]

def castRecords {N M : Nat} (same : N = M) (records : List (Fin N × E)) :
    List (Fin M × E) :=
  records.map fun record => (Fin.cast same record.1, record.2)

theorem castRecords_cancel {N M : Nat} (same : N = M) (records : List (Fin N × E)) :
    castRecords same.symm (castRecords same records) = records := by
  subst M
  simp [castRecords]

def extractReplies (n rate : Nat) (noWrap : n + rate ≤ 64) (count lane : Nat)
    (requests : List QueryRequest) (replies : List Reply) : Option (Array K) :=
  (parseReplies (n + rate) count lane requests replies).bind
    (fun records => extractRecords n rate noWrap
      (castRecords (ConcreteRowExtraction.domain_size (n + rate) noWrap).symm records))

theorem extractReplies_recovers (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate)) (count lane : Nat)
    (requests : List QueryRequest) (replies : List Reply)
    (a : Array K) (shape : a.size = 2 ^ n)
    (committed : Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n → E)
    (records : List (Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n × E))
    (parsed : parseReplies (n + rate) count lane requests replies =
      some (castRecords (ConcreteRowExtraction.domain_size (n + rate) noWrap) records))
    (authenticated : ∀ record ∈ records, record.2 = committed record.1)
    (covered : ∀ target, ∃ record ∈ records, record.1 = target)
    (radius : 2 * hammingDist committed
      (fun i => (encode n rate (a.map E.ofK))[i.val]!) ≤ 2 ^ (n + rate) - 2 ^ n) :
    extractReplies n rate noWrap count lane requests replies = some a := by
  rw [extractReplies, parsed, Option.bind_some, castRecords_cancel]
  exact extractRecords_recovers n rate noWrap redundancy a shape committed records
    authenticated covered radius

open CausalProbability in
/-- Actual fixed-public reset-and-decode algorithm. The caller provides only fresh challenge coordinates and a tape whose already-sent prefix is replayed. -/
def extractResetLane (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (rounds : Nat)
    (seed : Fin rounds → Sample (.query level)) (n rate : Nat) (noWrap : n + rate ≤ 64)
    (lane : Nat) : Option (Array K) :=
  extractReplies n rate noWrap prover.input.config.queries[level.val]! lane
    (List.ofFn fun round => resetRequest prover.input level (seed round))
    (collectResets prover tape level rounds seed).replies

open CausalProbability in
/-- Correctness for the actual black-box reset collector. Successful authenticated access and proximity remain separate premises; no dense-root access is performed by the function. -/
theorem extractResetLane_recovers (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (rounds : Nat)
    (seed : Fin rounds → Sample (.query level)) (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate)) (lane : Nat)
    (a : Array K) (shape : a.size = 2 ^ n)
    (committed : Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n → E)
    (records : List (Fin (ConcreteRowExtraction.domain (n + rate) noWrap).n × E))
    (parsed : parseReplies (n + rate) prover.input.config.queries[level.val]! lane
      (List.ofFn fun round => resetRequest prover.input level (seed round))
      (collectResets prover tape level rounds seed).replies =
        some (castRecords (ConcreteRowExtraction.domain_size (n + rate) noWrap) records))
    (authenticated : ∀ record ∈ records, record.2 = committed record.1)
    (covered : ∀ target, ∃ record ∈ records, record.1 = target)
    (radius : 2 * hammingDist committed
      (fun i => (encode n rate (a.map E.ofK))[i.val]!) ≤ 2 ^ (n + rate) - 2 ^ n) :
    extractResetLane prover tape level rounds seed n rate noWrap lane = some a :=
  extractReplies_recovers n rate noWrap redundancy _ lane _ _ a shape committed records
    parsed authenticated covered radius

/-- At most two coordinate lookup passes in the implemented assembly. This counts comparisons, separately from decoder field and polynomial operations. -/
theorem parsed_assemblyComparisons_le (depth count lane : Nat)
    (requests : List QueryRequest) (replies : List Reply)
    (records : List (Fin (2 ^ depth) × E))
    (parsed : parseReplies depth count lane requests replies = some records) :
    2 * assemblyComparisons records ≤ 2 * (2 ^ depth * (requests.length * count)) := by
  apply Nat.mul_le_mul_left
  simpa [parseReplies_length depth count lane requests replies records parsed] using
    assemblyComparisons_le records

#print axioms collect_replies
#print axioms collect_responseCalls
#print axioms run_collectProgram
#print axioms queryPrefix_reset
#print axioms resetRequest_actual_batch
#print axioms collectResets_responseCalls
#print axioms collectResets_responseCalls_le
#print axioms accepted_queries_authenticated
#print axioms reset_oracle_fixed
#print axioms countedLookup_value
#print axioms countedLookup_comparisons
#print axioms lookup_authenticated
#print axioms assemble_eq_committed
#print axioms assemblyComparisons_le
#print axioms extractRecords_recovers
#print axioms parseLane_length
#print axioms parseLane_authenticated
#print axioms parseReplies_length
#print axioms parseLane_contains_sampled
#print axioms parseReplies_map_contains
#print axioms parseReplies_map_parsed
#print axioms parsed_cover_of_sampler
#print axioms castRecords_cancel
#print axioms extractReplies_recovers
#print axioms extractResetLane_recovers
#print axioms parsed_assemblyComparisons_le
end Whir.RewindRowExtraction
