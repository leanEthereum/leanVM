import Whir.PublicMerkleLog
import Whir.WHIRModeFinal

/-! Ordinary Merkle hashing as actual public compression requests. Every chunk
is a verification-purpose primitive call. Ordered replay consumes the observed
answers, including arbitrary stateful simulator replies; it never evaluates a
hidden total hash or assumes repeated replies are consistent. -/
namespace Whir.PublicMerkleProgram
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame

variable {R S : Type}

/-- Operational mode-program executions, with the complete public query/reply
trace. No reference oracle occurs in the relation. -/
inductive Runs : Program R → List Observation → R → Prop where
  | done (r : R) : Runs (.done r) [] r
  | ask {q : Query} {next : Digest32 → Program R} {trace : List Observation} {r : R}
      (answer : Digest32) : Runs (next answer) trace r → Runs (.ask q next) (⟨q,answer⟩ :: trace) r

theorem runReal_runs (C : PrimitiveOracle) (iv : Digest32) (p : Program R) :
    Runs p (runReal C iv p).view.observations (runReal C iv p).view.result := by
  induction p with
  | done r => exact .done r
  | ask q next ih => exact .ask (realAnswer C iv q) (ih (realAnswer C iv q))

theorem runIdeal_runs {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p) :
    Runs p (runIdeal sim ro iv state p remaining cap counted).view.observations
      (runIdeal sim ro iv state p remaining cap counted).view.result := by
  induction p generalizing state remaining with
  | done r => exact .done r
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      exact .ask (runRO ro (sim.answer state input)).1.2
        (ih _ (runRO ro (sim.answer state input)).1.1 (remaining-1) (by omega) (counted.2 _))
    | construction q valid =>
      exact .ask (ro (constructionKey Q iv q (counted.1.trans cap)))
        (ih _ state (remaining-pathCost q) (by omega) (counted.2 _))

theorem Runs.bind_iff (p : Program R) (next : R → Program S) {trace : List Observation} {result : S} :
    Runs (WHIRModeFinal.bind p next) trace result ↔
      ∃ before value after, trace = before ++ after ∧ Runs p before value ∧ Runs (next value) after result := by
  induction p generalizing trace result with
  | done r =>
    constructor
    · intro h
      exact ⟨[],r,trace,rfl,.done r,h⟩
    · rintro ⟨before,value,after,he,hp,hn⟩
      cases hp
      simpa only [List.nil_append] using he ▸ hn
  | ask q cont ih =>
    constructor
    · intro h
      cases h with
      | ask answer h =>
        obtain ⟨before,value,after,he,hp,hn⟩ := (ih answer).mp h
        exact ⟨⟨q,answer⟩ :: before,value,after,by simp [he],.ask answer hp,hn⟩
    · rintro ⟨before,value,after,he,hp,hn⟩
      cases hp with
      | ask answer hp =>
        subst trace
        exact .ask answer ((ih answer).mpr ⟨_,value,after,rfl,hp,hn⟩)

theorem Runs.result_unique {p : Program R} {trace : List Observation} {a b : R}
    (ha : Runs p trace a) (hb : Runs p trace b) : a = b := by
  induction ha with
  | done r => cases hb; rfl
  | ask answer h ih => cases hb with | ask _ h' => exact ih h'

/-- The impossible empty chunk-list branch is discharged by a proof, not a
fallback digest. Empty input itself has one final empty chunk. -/
def hashFrom (cv : Digest32) (count : Nat) : (bs : List (List Byte)) → bs ≠ [] → Program Digest32
  | [], h => False.elim (h rfl)
  | [b], _ => .ask (.primitive .verification (PublicMerkleLog.node cv count b true)) Program.done
  | b :: next :: rest, _ =>
    .ask (.primitive .verification (PublicMerkleLog.node cv count b false)) fun answer =>
      hashFrom answer (count+b.length) (next :: rest) (by simp)

/-- Close each 256-bit reply over stored bytes before it becomes another CV;
do not retain a function that recomputes the whole preceding hash chain. -/
private def withStoredDigest {T : Type} (d : Digest32) (next : Digest32 → T) : T :=
  let bytes := Array.ofFn d
  next (fun i => bytes[i.val]'(by simp only [bytes, Array.size_ofFn]; exact i.isLt))

private theorem withStoredDigest_eq {T : Type} (d : Digest32) (next : Digest32 → T) :
    withStoredDigest d next = next d := by
  simp [withStoredDigest]

private def hashFromStored (cv : Digest32) (count : Nat) :
    (bs : List (List Byte)) → bs ≠ [] → Program Digest32
  | [], h => False.elim (h rfl)
  | [b], _ => .ask (.primitive .verification (PublicMerkleLog.node cv count b true))
      (fun answer => withStoredDigest answer Program.done)
  | b :: next :: rest, _ =>
    .ask (.primitive .verification (PublicMerkleLog.node cv count b false)) fun answer =>
      withStoredDigest answer (fun cv => hashFromStored cv (count+b.length) (next :: rest) (by simp))

@[csimp] theorem hashFrom_stored : hashFrom = hashFromStored := by
  funext cv count bs hne
  induction bs generalizing cv count with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil => simp only [hashFrom, hashFromStored, withStoredDigest_eq]
    | cons next rest =>
      simp only [hashFrom, hashFromStored, withStoredDigest_eq, ih]

def hash (bytes : List Byte) : Program Digest32 :=
  hashFrom DuplexCompression.parameterIV 0 (PublicMerkleLog.chunks bytes) (PublicMerkleLog.chunks_nonempty bytes)

theorem hashFrom_counted (cv : Digest32) (count : Nat) (bs : List (List Byte)) (hne : bs ≠ []) :
    Counts bs.length (hashFrom cv count bs hne) := by
  induction bs generalizing cv count with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil => simp [hashFrom, Counts, Query.cost]
    | cons next rest =>
      simp only [hashFrom, Counts, Query.cost, List.length_cons]
      refine ⟨by omega, fun answer => ?_⟩
      simpa using ih answer (count+b.length) (by simp)

theorem hash_counted (bytes : List Byte) : Counts (PublicMerkleLog.chunks bytes).length (hash bytes) :=
  hashFrom_counted _ _ _ _

theorem hash_bind_counted (bytes : List Byte) (next : Digest32 → Program R) (budget : Nat)
    (after : ∀ d, Counts budget (next d)) :
    Counts ((PublicMerkleLog.chunks bytes).length+budget) (WHIRModeFinal.bind (hash bytes) next) :=
  WHIRModeFinal.bind_counted _ _ _ _ (hash_counted bytes) after

theorem hashFrom_real_run (C : PrimitiveOracle) (iv cv : Digest32) (count : Nat)
    (bs : List (List Byte)) (hne : bs ≠ []) :
    PublicMerkleLog.run (fun n => some (C n)) cv count bs =
      some (runReal C iv (hashFrom cv count bs hne)).view.result := by
  induction bs generalizing cv count with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simpa only [PublicMerkleLog.run, Option.bind_eq_bind, Option.bind_some,
        hashFrom, runReal, prepend, realAnswer] using ih (C (PublicMerkleLog.node cv count b false)) (count+b.length) (by simp)

theorem hash_real_result (C : PrimitiveOracle) (iv : Digest32) (bytes : List Byte) :
    (runReal C iv (hash bytes)).view.result = PublicMerkleLog.hash C bytes := by
  unfold PublicMerkleLog.hash
  rw [hashFrom_real_run C iv _ _ _ (PublicMerkleLog.chunks_nonempty bytes)]
  rfl

/-- The pure hash API uses the existing ordinary fold with eagerly stored
replies. Unlike evaluating a mode Program, this allocates no public trace. -/
private def storedQuery (C : PrimitiveOracle) (n : Node) : Option Digest32 :=
  withStoredDigest (C n) Option.some

private theorem storedQuery_eq (C : PrimitiveOracle) :
    storedQuery C = (fun n => some (C n)) := by
  funext n
  exact withStoredDigest_eq _ _

def hashStored (C : PrimitiveOracle) (bytes : List Byte) : Digest32 :=
  let result := PublicMerkleLog.run (storedQuery C) DuplexCompression.parameterIV 0 (PublicMerkleLog.chunks bytes)
  result.get (by
    dsimp only [result]
    rw [storedQuery_eq]
    obtain ⟨d,hd⟩ := PublicMerkleLog.run_nonempty C (PublicMerkleLog.chunks bytes)
      (PublicMerkleLog.chunks_nonempty bytes) DuplexCompression.parameterIV 0
    rw [hd]
    rfl)

@[csimp] theorem ordinaryHash_stored : PublicMerkleLog.hash = hashStored := by
  funext C bytes
  obtain ⟨d,hd⟩ := PublicMerkleLog.run_nonempty C (PublicMerkleLog.chunks bytes)
    (PublicMerkleLog.chunks_nonempty bytes) DuplexCompression.parameterIV 0
  simp only [PublicMerkleLog.hash, hashStored, storedQuery_eq, hd]
  rfl

def hashBlake2sStored : List Byte → Digest32 := hashStored blake2sOracle

/-- Rewrite the imported wrapper as well: its previously compiled body must
not retain the old unstored fold. Neither implementation calls itself. -/
@[csimp] theorem ordinaryBlake2s_stored :
    PublicMerkleLog.hashBlake2s = hashBlake2sStored := by
  exact congrFun ordinaryHash_stored blake2sOracle

theorem hash_bind_real_result (C : PrimitiveOracle) (iv : Digest32) (bytes : List Byte)
    (next : Digest32 → Program R) :
    (runReal C iv (WHIRModeFinal.bind (hash bytes) next)).view.result =
      (runReal C iv (next (PublicMerkleLog.hash C bytes))).view.result := by
  rw [WHIRModeFinal.bind_real_result, hash_real_result]

theorem hashFrom_real_observations (C : PrimitiveOracle) (iv cv : Digest32) (count : Nat)
    (bs : List (List Byte)) (hne : bs ≠ []) :
    (runReal C iv (hashFrom cv count bs hne)).view.observations =
      (PublicMerkleLog.planFrom C cv count bs).map (fun e => ⟨.primitive .verification e.1,e.2⟩) := by
  induction bs generalizing cv count with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simpa only [hashFrom, runReal, prepend, realAnswer, PublicMerkleLog.planFrom, List.map_cons] using
        congrArg (List.cons (⟨.primitive .verification (PublicMerkleLog.node cv count b false),
          C (PublicMerkleLog.node cv count b false)⟩ : Observation))
          (ih (C (PublicMerkleLog.node cv count b false)) (count+b.length) (by simp))

theorem hash_real_observations (C : PrimitiveOracle) (iv : Digest32) (bytes : List Byte) :
    (runReal C iv (hash bytes)).view.observations =
      (PublicMerkleLog.plan C bytes).map (fun e => ⟨.primitive .verification e.1,e.2⟩) :=
  hashFrom_real_observations _ _ _ _ _ _

/-- Consume a literal public verification query, rejecting a missing record,
wrong purpose, wrong node, or construction observation. -/
def readObservation (n : Node) : List Observation → Option (Digest32 × List Observation)
  | ⟨.primitive .verification actual,answer⟩ :: rest => if actual = n then some (answer,rest) else none
  | _ => none

def replayFrom (cv : Digest32) (count : Nat) : List (List Byte) → List Observation →
    Option (Digest32 × List Observation)
  | [], _ => none
  | [b], trace => readObservation (PublicMerkleLog.node cv count b true) trace
  | b :: next :: rest, trace => do
    let (answer,remaining) ← readObservation (PublicMerkleLog.node cv count b false) trace
    replayFrom answer (count+b.length) (next :: rest) remaining

def replay (bytes : List Byte) : List Observation → Option (Digest32 × List Observation) :=
  replayFrom DuplexCompression.parameterIV 0 (PublicMerkleLog.chunks bytes)

theorem hashFrom_replay {cv : Digest32} {count : Nat} {bs : List (List Byte)} {hne : bs ≠ []}
    {trace : List Observation} {digest : Digest32} (run : Runs (hashFrom cv count bs hne) trace digest)
    (suffix : List Observation) : replayFrom cv count bs (trace ++ suffix) = some (digest,suffix) := by
  induction bs generalizing cv count trace digest with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil =>
      cases run with
      | ask answer h =>
        cases h
        simp [replayFrom, readObservation]
    | cons next rest =>
      cases run with
      | ask answer h =>
        simpa only [replayFrom, List.cons_append, readObservation, ↓reduceIte,
          Option.bind_eq_bind, Option.bind_some] using ih h

theorem hash_replay {bytes : List Byte} {trace : List Observation} {digest : Digest32}
    (run : Runs (hash bytes) trace digest) (suffix : List Observation) :
    replay bytes (trace ++ suffix) = some (digest,suffix) := hashFrom_replay run suffix

theorem hash_ideal_replay {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (bytes : List Byte)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining (hash bytes))
    (suffix : List Observation) :
    replay bytes ((runIdeal sim ro iv state (hash bytes) remaining cap counted).view.observations ++ suffix) =
      some ((runIdeal sim ro iv state (hash bytes) remaining cap counted).view.result,suffix) :=
  hash_replay (runIdeal_runs sim ro iv state _ remaining cap counted) suffix

theorem hashFrom_trace {cv : Digest32} {count : Nat} {bs : List (List Byte)} {hne : bs ≠ []}
    {trace : List Observation} {digest : Digest32} (run : Runs (hashFrom cv count bs hne) trace digest) :
    trace.length = bs.length ∧ ∀ o ∈ trace, ∃ n, o.query = .primitive .verification n := by
  induction bs generalizing cv count trace digest with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil =>
      cases run with
      | ask answer h =>
        cases h
        simp
    | cons next rest =>
      cases run with
      | ask answer h =>
        obtain ⟨length,purpose⟩ := ih h
        constructor
        · simp [length]
        · intro o ho
          rcases List.mem_cons.mp ho with rfl | hm
          · exact ⟨_,rfl⟩
          · exact purpose o hm

theorem hash_trace {bytes : List Byte} {trace : List Observation} {digest : Digest32}
    (run : Runs (hash bytes) trace digest) :
    trace.length = (PublicMerkleLog.chunks bytes).length ∧
      ∀ o ∈ trace, ∃ n, o.query = .primitive .verification n := hashFrom_trace run

end Whir.PublicMerkleProgram
