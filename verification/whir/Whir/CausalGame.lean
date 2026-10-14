import Whir.Protocol
import Whir.Soundness
import Whir.FieldCardinality

/-! Causal adversaries for the actual dense verifier. The honest `prove` function
may accept a complete challenge tape; an adversary in this game never receives it.
Query squeezes and their adjacent batching scalar form one verifier message. -/
namespace Whir.CausalGame
open Concrete Protocol

structure Claim where
  weight : Array E
  value : E
  deriving Repr, Inhabited

abbrev BaseOracle := Array (Array K)

/-- The commitment message contains exactly the occupied base-field lanes. -/
abbrev Witness (c : Config) (lanes : Nat) :=
  Fin (lanes * 2 ^ (c.logN - c.folds[0]!)) → K

def paddedWitness (c : Config) (lanes : Nat) (witness : Witness c lanes) : Array E :=
  let words := Array.ofFn witness
  tab (2 ^ c.logN) fun i => E.ofK (words[i]?.getD 0)

def liftRoot (root : BaseOracle) : Oracle := root.map fun row => row.map E.ofK

structure Public where
  config : Config
  lanes : Nat
  root : BaseOracle
  claims : Array Claim
  deriving Repr, Inhabited

/-- Each constructor is one verifier message, not one coordinate of that message. -/
inductive Batch where
  | initial (lambda : E)
  | fold (level round : Nat) (r : E)
  | ood (level index : Nat) (point : Array E)
  | query (level : Nat) (squeezes : Array E) (lambda : E)
  | tail (round : Nat) (r : E)
  deriving Repr, Inhabited

/-- Boundary data is sent with the last fold response, before OOD/query randomness.
Only the appropriate boundary field is parsed at a level boundary. -/
inductive Reply where
  | initial (message : Message E)
  | fold (message : Message E) (next : Option Oracle) (residual : Array E)
  | ood (claim : OodClaim)
  | query (rows : Oracle) (intro : Message E)
  | tail (message : Message E)
  deriving Repr, Inhabited

/-- Reverse chronological history, allowing constant-time extension. -/
abbrev History := List (Batch × Reply)
abbrev Strategy := Public → History → Batch → Reply

/-- The only interface through which an adversary selects a response. -/
def run (strategy : Strategy) (input : Public) (past : History) : List Batch → List Reply
  | [] => []
  | batch :: rest =>
    let answer := strategy input past batch
    answer :: run strategy input ((batch, answer) :: past) rest

/-- Executed response prefixes use only the corresponding challenge prefix. -/
theorem run_take (strategy : Strategy) (input : Public) (n : Nat)
    (past : History) (batches : List Batch) :
    (run strategy input past batches).take n = run strategy input past (batches.take n) := by
  induction n generalizing past batches with
  | zero => simp [run]
  | succ n ih =>
    cases batches with
    | nil => simp [run]
    | cons batch rest => simp [run, ih]

/-- No suffix, including an unrevealed final challenge, can change earlier replies. -/
theorem prefix_independent (strategy : Strategy) (input : Public) (n : Nat)
    (past : History) (left right : List Batch) (same : left.take n = right.take n) :
    (run strategy input past left).take n = (run strategy input past right).take n := by
  rw [run_take, run_take, same]

/-- Raw independent field elements required by one production-shaped level. -/
def remaining (c : Config) (i : Nat) : Nat := c.logN - (c.folds.toList.take (i + 1)).sum

def oodCount (c : Config) (i : Nat) : Nat :=
  if i + 1 < c.folds.size then c.oodCounts[i + 1]! else 0

def queryChunks (c : Config) (i : Nat) : Nat :=
  let per := 192 / (remaining c i + c.rates[i]!)
  (c.queries[i]! + per - 1) / per

abbrev LevelTape (c : Config) (i : Fin c.folds.size) :=
  (Fin c.folds[i.val]! → E) ×
  (Fin (oodCount c i.val) → Fin (remaining c i.val) → E) ×
  (Fin (queryChunks c i.val) → E) × E

abbrev Tape (c : Config) :=
  E × (∀ i : Fin c.folds.size, LevelTape c i) ×
  (Fin (c.logN - c.folds.toList.sum) → E)

/-- Sampling has no prover-dependent rejection or postselection. -/
def challenges (c : Config) (tape : Tape c) : Challenges :=
  ⟨Array.ofFn (fun i : Fin c.folds.size =>
    let t := tape.2.1 i
    ⟨Array.ofFn t.1, Array.ofFn (fun j => Array.ofFn (t.2.1 j)),
      Array.ofFn t.2.2.1, t.2.2.2⟩), Array.ofFn tape.2.2⟩

/-- Batching all externally supplied claims happens after commitment, before intro. -/
def batchClaims (width : Nat) (claims : Array Claim) (lambda : E) : Claim := Id.run do
  let mut out : Claim := ⟨tab width fun _ => E.zero, E.zero⟩
  let mut power := E.one
  for claim in claims do
    out := ⟨weightGlue out.weight claim.weight power, out.value + power * claim.value⟩
    power := power * lambda
  return out

/-- One level's wire order. Queries and lambda are one indivisible message. -/
def levelBatches (ch : Challenges) (i : Nat) : List Batch :=
  let cs := ch.levels[i]!
  (List.ofFn fun j : Fin cs.folds.size => Batch.fold i j cs.folds[j]) ++
  (List.ofFn fun j : Fin cs.oodPoints.size => Batch.ood i j cs.oodPoints[j]) ++
  [Batch.query i cs.querySqueezes cs.lambda]

/-- Position immediately before a level's first fold response. -/
def levelStart (ch : Challenges) (i : Nat) : Nat :=
  1 + ((List.range i).flatMap (levelBatches ch)).length

def tailStart (c : Config) (ch : Challenges) : Nat := levelStart ch c.folds.size

/-- The final tail challenge has no following prover message. -/
def visibleBatches (c : Config) (initial : E) (ch : Challenges) : List Batch :=
  [.initial initial] ++ (List.range c.folds.size).flatMap (levelBatches ch) ++
    (List.ofFn fun j : Fin (ch.tail.size - 1) => Batch.tail j ch.tail[j.val]!)

/-- Check precisely the wire tags, in wire order, with the original parser errors. -/
def checkReplies : List Batch → List Reply → Except String Unit
  | [], [] => .ok ()
  | [], _ :: _ => .error "trailing response"
  | .initial _ :: bs, .initial _ :: rs => checkReplies bs rs
  | .fold _ _ _ :: bs, .fold _ _ _ :: rs => checkReplies bs rs
  | .ood _ _ _ :: bs, .ood _ :: rs => checkReplies bs rs
  | .query _ _ _ :: bs, .query _ _ :: rs => checkReplies bs rs
  | .tail _ _ :: bs, .tail _ :: rs => checkReplies bs rs
  | .initial _ :: _, _ => .error "initial response"
  | .fold _ _ _ :: _, _ => .error "fold response"
  | .ood _ _ _ :: _, _ => .error "OOD response"
  | .query _ _ _ :: _, _ => .error "query response"
  | .tail _ _ :: _, _ => .error "tail response"

def initialField : Reply → Message E
  | .initial m => m
  | _ => default

def foldField : Reply → Message E
  | .fold m _ _ => m
  | _ => default

def rootField : Reply → Option Oracle
  | .fold _ next _ => next
  | _ => none

def residualField : Reply → Array E
  | .fold _ _ residual => residual
  | _ => #[]

def oodField : Reply → OodClaim
  | .ood claim => claim
  | _ => default

def rowsField : Reply → Oracle
  | .query rows _ => rows
  | _ => #[]

def introField : Reply → Message E
  | .query _ intro => intro
  | _ => default

def tailField : Reply → Message E
  | .tail m => m
  | _ => default

/-- Total projections are used only after all wire tags have been checked. Each
field reads one response position; no field reads later responses. -/
def decodedLevel (c : Config) (ch : Challenges) (answers : Array Reply) (i : Nat) :
    LevelProof :=
  let cs := ch.levels[i]!
  let start := levelStart ch i
  let query := start + cs.folds.size + cs.oodPoints.size
  ⟨Array.ofFn (fun j : Fin cs.folds.size => foldField answers[start + j.val]!),
    if i + 1 < c.folds.size ∧ 0 < cs.folds.size then
      rootField answers[start + cs.folds.size - 1]! else none,
    Array.ofFn (fun j : Fin cs.oodPoints.size =>
      oodField answers[start + cs.folds.size + j.val]!),
    rowsField answers[query]!, introField answers[query]!⟩

def decodedOpening (c : Config) (ch : Challenges) (answers : Array Reply) : Opening :=
  let last := c.folds.size - 1
  let count := ch.levels[last]!.folds.size
  ⟨initialField answers[0]!,
    Array.ofFn (fun i : Fin c.folds.size => decodedLevel c ch answers i.val),
    if 0 < c.folds.size ∧ 0 < count then
      residualField answers[levelStart ch last + count - 1]! else #[],
    Array.ofFn (fun j : Fin (ch.tail.size - 1) =>
      tailField answers[tailStart c ch + j.val]!)⟩

/-- Decode arbitrary replies; malformed tags and extra/missing replies reject.
The challenge values are not used by the tag check or field projections. -/
def opening (c : Config) (ch : Challenges) (answers : Array Reply) : Except String Opening := do
  checkReplies (visibleBatches c E.zero ch) answers.toList
  return decodedOpening c ch answers

/-- The accepting experiment invokes the actual length/authentication/algebra
verifier, after deriving an opening through only causal response calls. -/
def experiment (input : Public) (strategy : Strategy) (tape : Tape input.config) : Bool :=
  let c := input.config
  let ch := challenges c tape
  if !(input.claims.all fun claim => shapeValid c input.lanes claim.weight) then false
  else
    let statement := batchClaims (2 ^ c.logN) input.claims tape.1
    let answers := run strategy input [] (visibleBatches c tape.1 ch)
    match opening c ch answers.toArray with
    | .error _ => false
    | .ok proof => (verify c ch input.lanes (liftRoot input.root) statement.weight statement.value proof).isOk

/-- All claims in this opening must be explained by one commitment-fixed candidate.
The existential candidate list precedes both the claims and the adaptive strategy. -/
noncomputable def AdaptiveListBinding (c : Config)
    (listBound : Nat) (error : Nat → ℚ) : Prop := by
  classical
  exact ∀ (lanes : Nat) (root : BaseOracle), ∃ candidates : Finset (Witness c lanes),
    candidates.card ≤ listBound ∧
    ∀ (claims : Array Claim) (strategy : Strategy),
      Soundness.uniformProb (Finset.univ.filter fun tape : Tape c =>
        experiment ⟨c, lanes, root, claims⟩ strategy tape = true ∧
        ¬ ∃ witness ∈ candidates,
          ∀ claim ∈ claims.toList,
            dot (paddedWitness c lanes witness) claim.weight = claim.value) ≤ error claims.size

end Whir.CausalGame
