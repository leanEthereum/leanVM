import Whir.ByteCodec
import Whir.CausalProbability
import Whir.CausalPrefix
import Whir.TypedFiatShamirGame
import Whir.DuplexRefinement

/-! Concrete PCS transport syntax at conditional #552, revision
`ff6a275304a3b577118b066ddcff83bfafa5998d`. This is a hand-port of the
Rust call schedule, not a theorem about compilation of Rust. Scalars are the
three little-endian words; a root is two scalars with zero spare limbs.
Merkle rows and paths, and the reconstructed linear coefficient, are not
absorbed. The caller binds the initial root and claims upstream; the initial
batching scalar adds no observation. No injectivity of a digest is asserted.
PoW is a separate nonce event, with no amplification of the PCS error. -/
namespace Whir.WHIRHistory
open Concrete Protocol CausalGame CausalProbability FiatShamirGame

/-- Concatenation intentionally forgets individual `observe` call boundaries. -/
def scalarBytes (xs : List E) : List Byte :=
  xs.flatMap (fun x => List.ofFn (ByteCodec.encodeE x))

theorem scalarBytes_length (xs : List E) : (scalarBytes xs).length = 24 * xs.length := by
  induction xs with
  | nil => simp [scalarBytes]
  | cons x xs ih =>
    change (List.ofFn (ByteCodec.encodeE x) ++ scalarBytes xs).length = _
    rw [List.length_append, List.length_ofFn, ih, List.length_cons]
    omega

/-- A bounded parser, retaining an unconsumed suffix for the next wire field. -/
def parseScalars : Nat → List Byte → Option (List E × List Byte)
  | 0, bs => some ([], bs)
  | n+1, bs =>
    if h : 24 ≤ bs.length then
      let x := ByteCodec.decodeE (fun i => bs[i.val]'(by omega))
      (parseScalars n (bs.drop 24)).map (fun p => (x :: p.1, p.2))
    else none

theorem parseScalars_append (xs : List E) (suffix : List Byte) :
    parseScalars xs.length (scalarBytes xs ++ suffix) = some (xs, suffix) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hlen : 24 ≤ (scalarBytes (x :: xs) ++ suffix).length := by
      simp [scalarBytes_length]; omega
    simp only [List.length_cons, parseScalars, hlen, dite_true]
    have first : (fun i : Fin 24 =>
        (scalarBytes (x :: xs) ++ suffix)[i.val]'(by have := i.isLt; omega)) =
        ByteCodec.encodeE x := by
      funext i
      simp only [scalarBytes, List.flatMap_cons, List.append_assoc]
      rw [List.getElem_append_left (by simpa only [List.length_ofFn] using i.isLt)]
      exact List.getElem_ofFn _
    rw [first, ByteCodec.decodeE_encodeE]
    simpa [scalarBytes, List.drop_append] using
      congrArg (Option.map (fun p : List E × List Byte => (x :: p.1, p.2))) ih

theorem scalarBytes_injective : Function.Injective scalarBytes := by
  intro xs ys h
  have hl := congrArg List.length h
  rw [scalarBytes_length, scalarBytes_length] at hl
  have hn : xs.length = ys.length := by omega
  have hx := parseScalars_append xs []
  have hy := parseScalars_append ys []
  simp only [List.append_nil] at hx hy
  rw [h, hn, hy] at hx
  exact (Prod.mk.inj (Option.some.inj hx)).1.symm

def parseExact (n : Nat) (bs : List Byte) : Option (List E) := do
  let (xs, rest) ← parseScalars n bs
  if rest = [] then some xs else none

theorem parseExact_roundtrip (xs : List E) :
    parseExact xs.length (scalarBytes xs) = some xs := by
  have h := parseScalars_append xs []
  simp only [List.append_nil] at h
  simp [parseExact, h]

def rootScalars (root : Digest32) : List E :=
  let p := ByteCodec.hashToScalars root
  [p.1, p.2]

def rootBytes (root : Digest32) : List Byte := scalarBytes (rootScalars root)

def parseRoot (bs : List Byte) : Option Digest32 := do
  let xs ← parseExact 2 bs
  match xs with
  | [a,b] => ByteCodec.scalarsToHash (a,b)
  | _ => none

theorem parseRoot_roundtrip (root : Digest32) : parseRoot (rootBytes root) = some root := by
  have h := parseExact_roundtrip (rootScalars root)
  simp only [rootScalars, List.length_cons, List.length_nil] at h
  simp [parseRoot, rootBytes, h, rootScalars, ByteCodec.scalarsToHash_hashToScalars]

theorem rootBytes_injective : Function.Injective rootBytes := by
  intro a b h
  have := congrArg parseRoot h
  simpa only [parseRoot_roundtrip, Option.some.injEq] using this

/-- WHIR sends only the constant and quadratic coefficients, in that order. -/
def messageScalars (m : Message E) : List E := [m.u0, m.u2]

/-- The missing linear coefficient is reconstructed, never serialized. -/
def decodeMessage (xs : List E) : Option (Message E) :=
  match xs with
  | [a,b] => some ⟨a,b⟩
  | _ => none

theorem message_roundtrip (m : Message E) : decodeMessage (messageScalars m) = some m := by
  cases m; rfl

/-- Last-level residuals are absorbed in full; earlier boundaries absorb a
48-byte digest encoding, not the extracted full oracle. -/
def boundaryScalars (c : Config) (i : Nat) (digest : Digest32) (residual : Array E) : List E :=
  if i + 1 < c.folds.size then rootScalars digest else residual.toList

/-- Projection of actual causal replies to the absorbed scalar stream. The
root digest is explicit side input: relating it to `Reply.fold.next` is the
Merkle extraction game's responsibility. Query rows are deliberately erased.
Tag mismatches reject here, without affecting the fixed challenge cap. -/
def replyScalars {c : Config} (q : Coordinate c) (digest : Digest32) : Reply → Option (List E) :=
  match q with
  | .initial => fun r => match r with
    | .initial m => some (messageScalars m)
    | _ => none
  | .fold i j => fun r => match r with
    | .fold m _ residual => some (messageScalars m ++
        if j.val + 1 = c.folds[i.val]! then boundaryScalars c i.val digest residual else [])
    | _ => none
  | .ood _ _ => fun r => match r with
    | .ood claim => some (claim.value :: messageScalars claim.intro)
    | _ => none
  | .query _ => fun r => match r with
    | .query _ m => some (messageScalars m)
    | _ => none
  | .tail _ => fun r => match r with
    | .tail m => some (messageScalars m)
    | _ => none

theorem query_rows_unbound {c : Config} (i : Fin c.folds.size) (d : Digest32)
    (rows rows' : Oracle) (m : Message E) :
    replyScalars (.query i) d (.query rows m) = replyScalars (.query i) d (.query rows' m) := rfl

theorem fold_oracle_unbound {c : Config} (i : Fin c.folds.size)
    (j : Fin c.folds[i.val]!) (d : Digest32) (a b : Option Oracle)
    (m : Message E) (residual : Array E) :
    replyScalars (.fold i j) d (.fold m a residual) =
      replyScalars (.fold i j) d (.fold m b residual) := rfl

/-- Each call consumes a complete field element, including unused query bits.
The lambda is the last coordinate of the same allocation as the query chunks. -/
def scalarCount {c : Config} : Coordinate c → Nat
  | .ood i _ => remaining c i.val
  | .query i => queryChunks c i.val + 1
  | _ => 1

def sampleScalars {c : Config} (q : Coordinate c) : Sample q → List E :=
  match q with
  | .initial => fun x => [x]
  | .fold _ _ => fun x => [x]
  | .ood _ _ => List.ofFn
  | .query _ => fun x => List.ofFn x.1 ++ [x.2]
  | .tail _ => fun x => [x]

theorem sampleScalars_length {c : Config} (q : Coordinate c) (x : Sample q) :
    (sampleScalars q x).length = scalarCount q := by
  cases q <;> simp [sampleScalars, scalarCount]

/-- The final tail squeeze is real, but has no following adversarial response. -/
def hiddenTail (c : Config) : List (Coordinate c) :=
  if h : 0 < c.logN - c.folds.toList.sum then
    [.tail ⟨c.logN - c.folds.toList.sum - 1, by omega⟩]
  else []

def schedule (c : Config) : List (Coordinate c) := visibleCoordinates c ++ hiddenTail c

def depth (c : Config) : Nat := (schedule c).length

theorem schedule_visible (c : Config) (t : Tape c) :
    (visibleCoordinates c).map (fun q => batch q (get q t)) =
      visibleBatches c t.1 (challenges c t) := visibleCoordinates_map c t

theorem hiddenTail_no_response (c : Config) (j : Fin (c.logN - c.folds.toList.sum))
    (last : j.val + 1 = c.logN - c.folds.toList.sum) (t : Tape c) (x : E)
    (strategy : Strategy) (input : Public) :
    run strategy input [] (visibleBatches c (set (.tail j) t x).1 (challenges c (set (.tail j) t x))) =
      run strategy input [] (visibleBatches c t.1 (challenges c t)) :=
  final_tail_response j last t x strategy input

/-- One canonical pending input. Empty scalar input is permitted, in particular
for initial batching and adjacent squeezes. PoW nonces are not `observe` calls. -/
structure Pending where
  scalars : List E
  nonce : Option (Nat × E)

  deriving DecidableEq
def encodePending (m : Pending) : List Byte × Option (Nat × Scalar24) :=
  (scalarBytes m.scalars, m.nonce.map (fun p => (p.1, ByteCodec.encodeE p.2)))

def decodePending (n : Nat) (wire : List Byte × Option (Nat × Scalar24)) : Option Pending := do
  let scalars ← parseExact n wire.1
  pure ⟨scalars, wire.2.map (fun p => (p.1, ByteCodec.decodeE p.2))⟩

theorem pending_roundtrip (m : Pending) :
    decodePending m.scalars.length (encodePending m) = some m := by
  rcases m with ⟨xs, nonce⟩
  simp only [decodePending, encodePending, parseExact_roundtrip]
  cases nonce <;> simp [ByteCodec.decodeE_encodeE]

theorem encodePending_injective : Function.Injective encodePending := by
  rintro ⟨xs,n⟩ ⟨ys,m⟩ h
  have hx : xs = ys := scalarBytes_injective (congrArg Prod.fst h)
  subst ys
  have hn := congrArg Prod.snd h
  have hi : Function.Injective (fun p : Nat × E => (p.1, ByteCodec.encodeE p.2)) := by
    intro a b he
    change (a.1, ByteCodec.encodeE a.2) = (b.1, ByteCodec.encodeE b.2) at he
    exact Prod.ext (Prod.mk.inj he).1 (ByteCodec.encodeE_injective (Prod.mk.inj he).2)
  have hm : n = m := Option.map_injective hi hn
  subst m
  rfl

/-- Execute the exact special nonce transition, not a guessed ordinary absorb. -/
def pendingModel (m : DuplexRefinement.Model) (p : Pending) : DuplexRefinement.Model :=
  let m := DuplexRefinement.modelAbsorb m (scalarBytes p.scalars)
  match p.nonce with
  | none => m
  | some (bits, nonce) => DuplexRefinement.modelNonce m (ByteCodec.encodeE nonce) bits

def requestModel {c : Config} (m : DuplexRefinement.Model) (p : Pending)
    (q : Coordinate c) : DuplexRefinement.Model :=
  DuplexRefinement.modelSqueeze (pendingModel m p) (24 * scalarCount q)

/-- Canonical syntax keys retain whole typed ancestor answers. This encoder
changes only the absorbed-message representation, not the dependent alphabet. -/
def encodeInput {c : Config}
    (input : TypedFiatShamirGame.FullInput Digest32 Pending (Coordinate c) Sample) :
    TypedFiatShamirGame.FullInput Digest32 (List Byte × Option (Nat × Scalar24)) (Coordinate c) Sample :=
  ⟨input.statement, input.messages.map encodePending,
    input.ancestors.map (fun p => (encodePending p.1, p.2))⟩

theorem encodeInput_injective (c : Config) : Function.Injective (@encodeInput c) := by
  intro a b h
  have hs := congrArg TypedFiatShamirGame.FullInput.statement h
  have hm := congrArg TypedFiatShamirGame.FullInput.messages h
  have ha := congrArg TypedFiatShamirGame.FullInput.ancestors h
  have hm' := (List.map_injective_iff.mpr encodePending_injective) hm
  have hi : Function.Injective (fun p : Pending × Sigma (@Sample c) => (encodePending p.1, p.2)) := by
    intro x y he
    change (encodePending x.1, x.2) = (encodePending y.1, y.2) at he
    exact Prod.ext (encodePending_injective (Prod.mk.inj he).1) (Prod.mk.inj he).2
  have ha' := (List.map_injective_iff.mpr hi) ha
  change a.statement = b.statement at hs
  cases a; cases b; simp_all

/-- Syntax admission is independent of acceptance: arbitrary pending bytes and
malformed replies may occur, but extra challenge positions are rejected. -/
def admissible (c : Config) (messages : List Pending) : Bool := decide (messages.length ≤ depth c)

theorem admitted_depth (c : Config) (messages : List Pending)
    (h : admissible c messages = true) : messages.length ≤ depth c := by
  simpa [admissible] using h

/-- A single global cache across statements and branches, with the final
invisible request charged as well. No accepted-proof hypothesis appears. -/
theorem cache_cap (c : Config)
    (query : Digest32 × List Pending → Coordinate c)
    (oracle : TypedFiatShamirGame.Oracle (A := Sample) query)
    (K : Nat) (requests : List (Digest32 × List Pending))
    (final : Digest32 × List Pending)
    (cache : TypedFiatShamirGame.Cache (Digest32 × List Pending) (fun key => Sample (query key)))
    (budget : requests.length ≤ K)
    (admitted : ∀ key ∈ requests, admissible c key.2 = true)
    (finalAdmitted : admissible c final.2 = true) :
    (TypedFiatShamirGame.serve query oracle (requests ++ [final]) cache).2 ≤ depth c * (K+1) := by
  classical
  exact TypedFiatShamirGame.serve_cap query oracle (depth c) K requests final cache budget
    (fun key hk => admitted_depth c key.2 (admitted key hk))
    (admitted_depth c final.2 finalAdmitted)

/-- Primitive events generated by the PCS schedule. The auxiliary nonce is
opaque to the PCS algebra; verification of its predicate is separate. -/
inductive Event where
  | observe (xs : List E)
  | nonce (bits : Nat) (value : E)
  | squeeze (bytes : Nat)

def challengeEvents {c : Config} (q : Coordinate c) (bits : Nat) (nonce : E) : List Event :=
  (match q with | .query _ => [.nonce bits nonce] | _ => []) ++
    [.squeeze (24 * scalarCount q)]

def coordinateLevel {c : Config} : Coordinate c → Nat
  | .fold i _ => i.val
  | .ood i _ => i.val
  | .query i => i.val
  | _ => 0

/-- Merkle side data contributes no event. This compiler checks all reply tags,
including those on rejecting branches, and never reads a future challenge. -/
def visibleEvents {c : Config} (digests : Nat → Digest32) (bits : Nat → Nat)
    (nonces : Nat → E) : List (Coordinate c) → List Reply → Option (List Event)
  | [], [] => some []
  | q :: qs, r :: rs => do
    let xs ← replyScalars q (digests (coordinateLevel q)) r
    let rest ← visibleEvents digests bits nonces qs rs
    pure (challengeEvents q (bits (coordinateLevel q)) (nonces (coordinateLevel q)) ++ [.observe xs] ++ rest)
  | _, _ => none

def wireEvents (c : Config) (digests : Nat → Digest32) (bits : Nat → Nat)
    (nonces : Nat → E) (replies : List Reply) : Option (List Event) := do
  let visible ← visibleEvents digests bits nonces (visibleCoordinates c) replies
  pure (visible ++ (hiddenTail c).map (fun q => Event.squeeze (24 * scalarCount q)))

def modelEvent (m : DuplexRefinement.Model) : Event → DuplexRefinement.Model
  | .observe xs => DuplexRefinement.modelAbsorb m (scalarBytes xs)
  | .nonce bits value => DuplexRefinement.modelNonce m (ByteCodec.encodeE value) bits
  | .squeeze n => DuplexRefinement.modelSqueeze m n

def modelEvents (m : DuplexRefinement.Model) (events : List Event) : DuplexRefinement.Model :=
  events.foldl modelEvent m

/-- The executable mode checks cursor limits and the actual PoW predicate.
Failure rejects; no continuation, retry, or grinding credit is added. -/
def executeEvent (compress : DuplexRefinement.Compression)
    (powOK : Digest32 → Scalar24 → Nat → Bool)
    (s : DuplexRefinement.State) : Event → Option DuplexRefinement.State
  | .observe xs => some (DuplexRefinement.absorb compress s (scalarBytes xs))
  | .nonce bits value =>
    match DuplexRefinement.verifyNonce compress powOK s (ByteCodec.encodeE value) bits with
    | .ok (t, true) => some t
    | _ => none
  | .squeeze n =>
    match DuplexRefinement.squeeze compress s n with
    | .ok (t, _) => some t
    | .error _ => none

def executeEvents (compress : DuplexRefinement.Compression)
    (powOK : Digest32 → Scalar24 → Nat → Bool) :
    DuplexRefinement.State → List Event → Option DuplexRefinement.State
  | s, [] => some s
  | s, e :: es => do
    let t ← executeEvent compress powOK s e
    executeEvents compress powOK t es

theorem executeEvent_represents (compress : DuplexRefinement.Compression)
    (powOK : Digest32 → Scalar24 → Nat → Bool) (iv : Digest32)
    (m : DuplexRefinement.Model) (s t : DuplexRefinement.State) (e : Event)
    (h : DuplexRefinement.Represents compress iv m s)
    (ok : executeEvent compress powOK s e = some t) :
    DuplexRefinement.Represents compress iv (modelEvent m e) t := by
  cases e with
  | observe xs =>
    simp only [executeEvent, Option.some.injEq] at ok
    subst t
    exact DuplexRefinement.absorb_represents compress iv m s h (scalarBytes xs)
  | nonce bits value =>
    simp only [executeEvent] at ok
    split at ok
    next u he =>
      cases ok
      exact DuplexRefinement.verifyNonce_represents compress powOK iv m s t h
        (ByteCodec.encodeE value) bits true he
    next => contradiction
  | squeeze n =>
    simp only [executeEvent] at ok
    split at ok
    next u bs he =>
      cases ok
      exact DuplexRefinement.squeeze_represents compress iv m s t h n bs he
    next => contradiction

theorem executeEvents_represents (compress : DuplexRefinement.Compression)
    (powOK : Digest32 → Scalar24 → Nat → Bool) (iv : Digest32)
    (events : List Event) (m : DuplexRefinement.Model) (s t : DuplexRefinement.State)
    (h : DuplexRefinement.Represents compress iv m s)
    (ok : executeEvents compress powOK s events = some t) :
    DuplexRefinement.Represents compress iv (modelEvents m events) t := by
  induction events generalizing m s with
  | nil =>
    simp only [executeEvents, Option.some.injEq] at ok
    subst t
    exact h
  | cons e es ih =>
    simp only [executeEvents] at ok
    cases he : executeEvent compress powOK s e with
    | none => simp [he] at ok
    | some u =>
      simp only [he] at ok
      exact ih (modelEvent m e) u (executeEvent_represents compress powOK iv m s u e h he) ok

/-- Canonical semantic runs, rather than the unobservable boundaries between
individual `observe` calls. Length and cursor are part of the real frame. -/
inductive SemanticFrame where
  | absorb (previous : Nat) (scalars : List E)
  | nonce (previous bits : Nat) (value : E)

def encodeFrame : SemanticFrame → Frame
  | .absorb previous xs => .absorb previous (scalarBytes xs)
  | .nonce previous bits x => .nonce previous bits (ByteCodec.encodeE x)

def parseFrame : Frame → Option SemanticFrame
  | .absorb previous bytes =>
    (parseExact (bytes.length / 24) bytes).map (SemanticFrame.absorb previous)
  | .nonce previous bits bytes => some (.nonce previous bits (ByteCodec.decodeE bytes))

theorem frame_roundtrip (f : SemanticFrame) : parseFrame (encodeFrame f) = some f := by
  cases f with
  | absorb previous xs =>
    simp only [encodeFrame, parseFrame, scalarBytes_length]
    simp [parseExact_roundtrip]
  | nonce previous bits value => simp [encodeFrame, parseFrame, ByteCodec.decodeE_encodeE]

theorem encodeFrame_injective : Function.Injective encodeFrame := by
  intro a b h
  have := congrArg parseFrame h
  simpa only [frame_roundtrip, Option.some.injEq] using this

structure SemanticHistory where
  domain : Digest32
  statement : Digest32
  frames : List SemanticFrame

def encodeHistory (h : SemanticHistory) : FramedHistory :=
  ⟨h.domain, h.statement, h.frames.map encodeFrame⟩

def parseFrames : List Frame → Option (List SemanticFrame)
  | [] => some []
  | f :: fs => do
    let x ← parseFrame f
    let xs ← parseFrames fs
    pure (x :: xs)

theorem frames_roundtrip (fs : List SemanticFrame) :
    parseFrames (fs.map encodeFrame) = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [parseFrames, frame_roundtrip, ih]

def parseHistory (h : FramedHistory) : Option SemanticHistory :=
  (parseFrames h.frames).map (fun fs => ⟨h.domain,h.statement,fs⟩)

theorem history_roundtrip (h : SemanticHistory) :
    parseHistory (encodeHistory h) = some h := by
  cases h
  simp [parseHistory, encodeHistory, frames_roundtrip]

theorem encodeHistory_injective : Function.Injective encodeHistory := by
  intro a b h
  have := congrArg parseHistory h
  simpa only [history_roundtrip, Option.some.injEq] using this

theorem scalarBytes_append (xs ys : List E) :
    scalarBytes (xs ++ ys) = scalarBytes xs ++ scalarBytes ys := by
  exact List.flatMap_append

theorem scalarBytes_empty (xs : List E) : scalarBytes xs = [] ↔ xs = [] := by
  constructor
  · intro h
    have hl := congrArg List.length h
    rw [scalarBytes_length] at hl
    exact List.length_eq_zero_iff.mp (by simpa using hl)
  · rintro rfl
    rfl

/-- A concrete scalar-run lift of the #552 ghost state. This remembers no
unbound proof fields and no boundaries between adjacent scalar observations. -/
structure SemanticModel where
  history : SemanticHistory
  run : List E := []
  previous : Nat := 0
  consumed : Nat := 0

def encodeModel (m : SemanticModel) : DuplexRefinement.Model :=
  ⟨encodeHistory m.history, scalarBytes m.run, m.previous, m.consumed⟩

def closeSemantic (m : SemanticModel) : SemanticModel :=
  if m.run = [] then m else
    {m with
      history := {m.history with frames := m.history.frames ++ [.absorb m.previous m.run]}
      run := []
      previous := 0}

theorem closeSemantic_encode (m : SemanticModel) :
    encodeModel (closeSemantic m) = DuplexRefinement.closeRun (encodeModel m) := by
  by_cases h : m.run = []
  · simp [closeSemantic, DuplexRefinement.closeRun, encodeModel, scalarBytes_empty, h]
  · simp only [closeSemantic, DuplexRefinement.closeRun, encodeModel, scalarBytes_empty, h,
      ↓reduceIte, encodeHistory, List.map_append, List.map_cons, List.map_nil, encodeFrame]
    rfl

def semanticEvent (m : SemanticModel) : Event → SemanticModel
  | .observe xs => if xs = [] then m else
      {m with
        run := m.run ++ xs
        previous := if m.consumed = 0 then m.previous else m.consumed
        consumed := 0}
  | .nonce bits value =>
      let m := closeSemantic m
      {history := {m.history with frames := m.history.frames ++ [.nonce m.consumed bits value]}}
  | .squeeze n => if n = 0 then m else {closeSemantic m with consumed := m.consumed + n}

theorem semanticEvent_encode (m : SemanticModel) (e : Event) :
    encodeModel (semanticEvent m e) = modelEvent (encodeModel m) e := by
  cases e with
  | observe xs =>
    by_cases h : xs = []
    · simp [semanticEvent, modelEvent, DuplexRefinement.modelAbsorb, scalarBytes_empty, h]
    · simp [semanticEvent, modelEvent, DuplexRefinement.modelAbsorb, scalarBytes_empty, h,
        encodeModel, scalarBytes_append]
      rfl
  | nonce bits value =>
    simp only [semanticEvent, modelEvent, DuplexRefinement.modelNonce,
      ← closeSemantic_encode]
    simp [encodeModel, encodeHistory, encodeFrame, scalarBytes]
  | squeeze n =>
    by_cases h : n = 0
    · simp [semanticEvent, modelEvent, DuplexRefinement.modelSqueeze, h]
    · simp only [semanticEvent, modelEvent, DuplexRefinement.modelSqueeze, h, ↓reduceIte,
        ← closeSemantic_encode]
      rfl

def semanticEvents (m : SemanticModel) (events : List Event) : SemanticModel :=
  events.foldl semanticEvent m

theorem semanticEvents_encode (m : SemanticModel) (events : List Event) :
    encodeModel (semanticEvents m events) = modelEvents (encodeModel m) events := by
  induction events generalizing m with
  | nil => rfl
  | cons e es ih =>
    change encodeModel (semanticEvents (semanticEvent m e) es) =
      modelEvents (modelEvent (encodeModel m) e) es
    rw [ih, semanticEvent_encode]

/-- Every compiled PCS trace, including concatenated observations and empty
squeezes, has a checked executable canonical semantic-history parser. -/
theorem compiled_history_parses (m : SemanticModel) (events : List Event) :
    parseHistory (DuplexRefinement.closeRun (modelEvents (encodeModel m) events)).history =
      some (closeSemantic (semanticEvents m events)).history := by
  rw [← semanticEvents_encode, ← closeSemantic_encode]
  exact history_roundtrip _

/-- Inverse of the absorbed-field projection. `lookup` is the separately
extracted commitment table; `rows` are separately authenticated ordered rows.
Neither is serialized or postulated to be recoverable from a hash alone. -/
def decodeReplyScalars {c : Config} (q : Coordinate c) (lookup : Digest32 → Oracle)
    (rows : Oracle) (xs : List E) : Option Reply :=
  match q with
  | .initial => (decodeMessage xs).map Reply.initial
  | .tail _ => (decodeMessage xs).map Reply.tail
  | .ood _ _ => match xs with
    | [y,a,b] => some (.ood ⟨y,⟨a,b⟩⟩)
    | _ => none
  | .query _ => (decodeMessage xs).map (Reply.query rows)
  | .fold i j => match xs with
    | a :: b :: rest =>
      if j.val + 1 = c.folds[i.val]! then
        if i.val + 1 < c.folds.size then
          match rest with
          | [r,s] => (ByteCodec.scalarsToHash (r,s)).map
              (fun digest => .fold ⟨a,b⟩ (some (lookup digest)) #[])
          | _ => none
        else if rest.length = 2 ^ remaining c i.val then
          some (.fold ⟨a,b⟩ none rest.toArray)
        else none
      else if rest = [] then some (.fold ⟨a,b⟩ none #[]) else none
    | _ => none

/-- Canonicalization removes precisely the proof fields absent from this wire
position. It does not assert that arbitrary unauthenticated input equals its
canonicalization. -/
def canonicalReply {c : Config} (q : Coordinate c) (digest : Digest32)
    (lookup : Digest32 → Oracle) (rows : Oracle) : Reply → Option Reply :=
  match q with
  | .initial => fun r => match r with | .initial m => some (.initial m) | _ => none
  | .tail _ => fun r => match r with | .tail m => some (.tail m) | _ => none
  | .ood _ _ => fun r => match r with | .ood o => some (.ood o) | _ => none
  | .query _ => fun r => match r with | .query _ m => some (.query rows m) | _ => none
  | .fold i j => fun r => match r with
    | .fold m _ residual =>
      if j.val + 1 = c.folds[i.val]! then
        if i.val + 1 < c.folds.size then some (.fold m (some (lookup digest)) #[])
        else if residual.size = 2 ^ remaining c i.val then some (.fold m none residual)
        else none
      else some (.fold m none #[])
    | _ => none

/-- Checked inverse on arbitrary replies, including malformed tags and wrong
residual lengths. The only normalization is explicit external authentication
data and fields which the original parser ignores. -/
theorem replyScalars_roundtrip {c : Config} (q : Coordinate c) (digest : Digest32)
    (lookup : Digest32 → Oracle) (rows : Oracle) (reply : Reply) :
    (replyScalars q digest reply).bind (decodeReplyScalars q lookup rows) =
      canonicalReply q digest lookup rows reply := by
  cases q <;> cases reply <;>
    simp only [replyScalars, canonicalReply, decodeReplyScalars, Option.bind_none,
      Option.bind_some, messageScalars, decodeMessage, Option.map_some]
  case fold.fold i j message next residual =>
    cases message
    have hh : c.folds[i.val]! = c.folds[i.val] := by simp
    simp only [hh] at *
    by_cases h : j.val + 1 = c.folds[i.val]
    · by_cases hi : i.val + 1 < c.folds.size
      · simp [h, hi, boundaryScalars, rootScalars, ByteCodec.scalarsToHash_hashToScalars]
      · simp [h, hi, boundaryScalars]
    · simp [h]

/-- Counts are fixed by the public schedule, including rejecting messages. -/
def replyScalarCount {c : Config} : Coordinate c → Nat
  | .fold i j => 2 + if j.val + 1 = c.folds[i.val]! then
      if i.val + 1 < c.folds.size then 2 else 2 ^ remaining c i.val
      else 0
  | .ood _ _ => 3
  | _ => 2

def parseReply {c : Config} (q : Coordinate c) (lookup : Digest32 → Oracle)
    (rows : Oracle) (bytes : List Byte) : Option Reply :=
  (parseExact (replyScalarCount q) bytes).bind (decodeReplyScalars q lookup rows)

theorem parseReply_roundtrip {c : Config} (q : Coordinate c) (lookup : Digest32 → Oracle)
    (rows : Oracle) (xs : List E) (size : xs.length = replyScalarCount q) :
    parseReply q lookup rows (scalarBytes xs) = decodeReplyScalars q lookup rows xs := by
  simp only [parseReply, ← size, parseExact_roundtrip, Option.bind_some]

/-- Erase auxiliary phases without splitting a whole-vector request. -/
def requestSizes (events : List Event) : List Nat :=
  events.filterMap (fun e => match e with | .squeeze n => some n | _ => none)

theorem visibleEvents_sizes {c : Config} (digests : Nat → Digest32) (bits : Nat → Nat)
    (nonces : Nat → E) (qs : List (Coordinate c)) (replies : List Reply) (events : List Event)
    (ok : visibleEvents digests bits nonces qs replies = some events) :
    requestSizes events = qs.map (fun q => 24 * scalarCount q) := by
  induction qs generalizing replies events with
  | nil =>
    cases replies with
    | nil => cases ok; rfl
    | cons r rs => cases ok
  | cons q qs ih =>
    cases replies with
    | nil => cases ok
    | cons r rs =>
      simp only [visibleEvents] at ok
      cases hx : replyScalars q (digests (coordinateLevel q)) r with
      | none => simp [hx] at ok
      | some xs =>
        cases hr : visibleEvents digests bits nonces qs rs with
        | none => simp [hx, hr] at ok
        | some rest =>
          simp [hx, hr] at ok
          subst events
          have hrest := ih rs rest hr
          have hb := congrArg (List.cons (24 * scalarCount q)) hrest
          cases q <;> simpa [requestSizes, challengeEvents, List.filterMap_append] using hb

theorem wireEvents_sizes (c : Config) (digests : Nat → Digest32) (bits : Nat → Nat)
    (nonces : Nat → E) (replies : List Reply) (events : List Event)
    (ok : wireEvents c digests bits nonces replies = some events) :
    requestSizes events = (schedule c).map (fun q => 24 * scalarCount q) := by
  unfold wireEvents at ok
  cases hv : visibleEvents digests bits nonces (visibleCoordinates c) replies with
  | none => simp [hv] at ok
  | some vs =>
    simp [hv] at ok
    subst events
    have hs := visibleEvents_sizes digests bits nonces _ _ _ hv
    simp only [requestSizes, List.filterMap_append, List.filterMap_map] at hs ⊢
    rw [hs]
    simp [schedule]

/-- This cap follows from compiling the fixed syntax, not from acceptance. -/
theorem wireEvents_depth (c : Config) (digests : Nat → Digest32) (bits : Nat → Nat)
    (nonces : Nat → E) (replies : List Reply) (events : List Event)
    (ok : wireEvents c digests bits nonces replies = some events) :
    (requestSizes events).length = depth c := by
  rw [wireEvents_sizes c digests bits nonces replies events ok, List.length_map]
  rfl

/-- Reverse-chronological keys select the next dependent alphabet by their
syntactic length. The fallback is unreachable for nonempty admitted requests. -/
def queryFor (c : Config) (key : Digest32 × List Pending) : Coordinate c :=
  ((schedule c)[key.2.length - 1]?).getD .initial

theorem queryFor_at (c : Config) (s : Digest32) (messages : List Pending)
    (n : Fin (depth c)) (size : messages.length = n.val + 1) :
    queryFor c (s,messages) = (schedule c)[n.val]'n.isLt := by
  have hn : n.val < (schedule c).length := n.isLt
  simp [queryFor, size, hn]
  rfl

/-- Fixed-position syntax recognizer. Scalar sizes and nonce presence are
checked before any algebra or authentication; malformed scalar values may
still reject later. PoW difficulty obeys the source's 63-bit hard limit. -/
def scheduledAdmissible (c : Config) (messages : List Pending) : Bool :=
  admissible c messages &&
    (messages.reverse.zipIdx.all fun (m, n) =>
      let q := ((schedule c)[n]?).getD .initial
      let previous := ((schedule c)[n-1]?).getD .initial
      decide (m.scalars.length = if n = 0 then 0 else replyScalarCount previous) &&
        match q with
        | .query _ => m.nonce.isSome && m.nonce.all (fun p => decide (p.1 ≤ 63))
        | _ => m.nonce.isNone)

theorem scheduledAdmissible_depth (c : Config) (messages : List Pending)
    (h : scheduledAdmissible c messages = true) : messages.length ≤ depth c := by
  simp only [scheduledAdmissible, Bool.and_eq_true] at h
  exact admitted_depth c messages h.1

/-- Concrete dependent-alphabet instantiation of the one-global-cache cap.
All branches use the same parser and include the invisible final request. -/
theorem scheduled_cache_cap (c : Config)
    (oracle : TypedFiatShamirGame.Oracle (A := Sample) (queryFor c))
    (K : Nat) (requests : List (Digest32 × List Pending))
    (final : Digest32 × List Pending)
    (cache : TypedFiatShamirGame.Cache (Digest32 × List Pending)
      (fun key => Sample (queryFor c key)))
    (budget : requests.length ≤ K)
    (admitted : ∀ key ∈ requests, scheduledAdmissible c key.2 = true)
    (finalAdmitted : scheduledAdmissible c final.2 = true) :
    (TypedFiatShamirGame.serve (queryFor c) oracle (requests ++ [final]) cache).2 ≤ depth c * (K+1) := by
  classical
  exact TypedFiatShamirGame.serve_cap (queryFor c) oracle (depth c) K requests final cache budget
    (fun key hk => scheduledAdmissible_depth c key.2 (admitted key hk))
    (scheduledAdmissible_depth c final.2 finalAdmitted)

/-- Definitionally `RingPCSGame.Prefix × E` at the initial coordinate:
gamma, six map scalars, then the WHIR batching lambda. There is no intervening
observation in `RingFamily::sample` or `stack_open`, so this is one allocation. -/
abbrev StackSample {c : Config} : Coordinate c → Type
  | .initial => (E × (Fin 6 → E)) × E
  | q => Sample q

def stackScalarCount {c : Config} : Coordinate c → Nat
  | .initial => 8
  | q => scalarCount q

def stackSampleScalars {c : Config} (q : Coordinate c) : StackSample q → List E :=
  match q with
  | .initial => fun x => [x.1.1] ++ List.ofFn x.1.2 ++ [x.2]
  | .fold i j => sampleScalars (.fold i j)
  | .ood i j => sampleScalars (.ood i j)
  | .query i => sampleScalars (.query i)
  | .tail j => sampleScalars (.tail j)

theorem stackSampleScalars_length {c : Config} (q : Coordinate c) (x : StackSample q) :
    (stackSampleScalars q x).length = stackScalarCount q := by
  cases q <;> simp [stackSampleScalars, stackScalarCount, sampleScalars_length]

/-- This replacement groups the seven adjacent ring-switch draws with lambda,
without adding an allocation or a prover response between them. -/
def stackWireEvents (c : Config) (digests : Nat → Digest32) (bits : Nat → Nat)
    (nonces : Nat → E) (replies : List Reply) : Option (List Event) := do
  let events ← wireEvents c digests bits nonces replies
  match events with
  | .squeeze _ :: rest => some (.squeeze 192 :: rest)
  | _ => none

theorem stackWireEvents_depth (c : Config) (digests : Nat → Digest32) (bits : Nat → Nat)
    (nonces : Nat → E) (replies : List Reply) (events : List Event)
    (ok : stackWireEvents c digests bits nonces replies = some events) :
    (requestSizes events).length = depth c := by
  simp only [stackWireEvents] at ok
  cases hw : wireEvents c digests bits nonces replies with
  | none => simp [hw] at ok
  | some es =>
    simp only [hw] at ok
    cases es with
    | nil => cases ok
    | cons e rest =>
      cases e <;> cases ok
      simpa [requestSizes] using wireEvents_depth c digests bits nonces replies _ hw

theorem coordinate_mem_schedule {c : Config} (q : Coordinate c) : q ∈ schedule c := by
  obtain hv | ⟨j, rfl, last⟩ := CausalPrefix.visible_or_last q
  · exact List.mem_append_left _ hv
  · apply List.mem_append_right
    have hp : 0 < c.logN - c.folds.toList.sum := by omega
    simp only [hiddenTail, hp, dite_true, List.mem_singleton]
    congr 1
    apply Fin.ext
    dsimp
    omega

theorem schedule_idxOf {c : Config} (q : Coordinate c) :
    (schedule c).idxOf q = position q := by
  by_cases hv : q ∈ visibleCoordinates c
  · exact List.idxOf_append_of_mem hv
  · obtain ⟨j, rfl, last⟩ := (CausalPrefix.visible_or_last q).resolve_left hv
    have hp : 0 < c.logN - c.folds.toList.sum := by omega
    have hj : j = (⟨c.logN - c.folds.toList.sum - 1, by omega⟩ :
        Fin (c.logN - c.folds.toList.sum)) := by apply Fin.ext; dsimp; omega
    rw [schedule, List.idxOf_append_of_notMem hv]
    unfold position
    rw [List.idxOf_of_notMem hv]
    simp only [hiddenTail, hp, dite_true, ← hj]
    simp

theorem schedule_get_position {c : Config} (q : Coordinate c) :
    (schedule c)[position q]? = some q := by
  rw [← schedule_idxOf]
  exact List.getElem?_idxOf (coordinate_mem_schedule q)

theorem position_lt_depth {c : Config} (q : Coordinate c) : position q < depth c := by
  rw [← schedule_idxOf]
  exact List.idxOf_lt_length_of_mem (coordinate_mem_schedule q)

private theorem coordinateLevel_mem (c : Config) (i : Nat) (q : Coordinate c)
    (h : q ∈ levelCoordinates c i) : coordinateLevel q = i := by
  unfold levelCoordinates at h
  split_ifs at h with hi
  · simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at h
    rcases h with (⟨j,rfl⟩ | ⟨j,rfl⟩) | rfl <;> rfl
  · simp at h

theorem levelCoordinates_nodup (c : Config) (i : Nat) : (levelCoordinates c i).Nodup := by
  unfold levelCoordinates
  split_ifs <;>
    simp [List.nodup_append, List.nodup_ofFn, Function.Injective]
  rintro a b (⟨j,rfl⟩ | rfl) <;> simp

theorem visibleCoordinates_nodup (c : Config) : (visibleCoordinates c).Nodup := by
  have hl : ((List.range c.folds.size).flatMap (levelCoordinates c)).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun i _ => levelCoordinates_nodup c i, ?_⟩
    apply (List.nodup_range (n := c.folds.size)).imp
    intro i j hij q hi hj
    exact hij ((coordinateLevel_mem c i q hi).symm.trans (coordinateLevel_mem c j q hj))
  have initial_not : Coordinate.initial ∉ (List.range c.folds.size).flatMap (levelCoordinates c) := by
    simp only [List.mem_flatMap, not_exists]
    intro i
    unfold levelCoordinates
    split_ifs <;> simp
  have tail_not (j : Fin (c.logN - c.folds.toList.sum)) :
      Coordinate.tail j ∉ (List.range c.folds.size).flatMap (levelCoordinates c) := by
    simp only [List.mem_flatMap, not_exists]
    intro i
    unfold levelCoordinates
    split_ifs <;> simp
  unfold visibleCoordinates
  apply List.Nodup.append
  · simpa using List.nodup_cons.mpr ⟨initial_not, hl⟩
  · apply List.nodup_ofFn_ofInjective
    intro a b he
    apply Fin.ext
    exact congrArg (fun k : Fin (c.logN - c.folds.toList.sum) => k.val) (Coordinate.tail.inj he)
  · intro q hq ht
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with impossible | hq
    · cases impossible
    · exact tail_not _ hq

theorem schedule_nodup (c : Config) : (schedule c).Nodup := by
  apply List.Nodup.append (visibleCoordinates_nodup c)
  · unfold hiddenTail
    split_ifs <;> simp
  · intro q hv hh
    unfold hiddenTail at hh
    split_ifs at hh with hp
    · simp only [List.mem_singleton] at hh
      subst q
      simp only [visibleCoordinates, List.mem_append, List.mem_singleton, List.mem_flatMap,
        List.mem_ofFn] at hv
      rcases hv with ((impossible | ⟨i,_,hi⟩) | ⟨j,hj⟩)
      · cases impossible
      · unfold levelCoordinates at hi
        split_ifs at hi <;> simp at hi
      · have he : j.val = c.logN - c.folds.toList.sum - 1 := by
          exact congrArg Fin.val (Coordinate.tail.inj hj)
        have := j.isLt
        omega
    · simp at hh

theorem position_schedule_get (c : Config) (i : Fin (depth c)) :
    position ((schedule c)[i.val]'i.isLt) = i.val := by
  rw [← schedule_idxOf]
  exact (schedule_nodup c).idxOf_getElem i.val i.isLt

/-- Removing newer requests preserves every older syntax check, including the
fixed alphabet, reply length and actual nonce-difficulty guard. -/
theorem scheduledAdmissible_drop (c : Config) (messages : List Pending) (n : Nat)
    (admitted : scheduledAdmissible c messages = true) :
    scheduledAdmissible c (messages.drop n) = true := by
  simp only [scheduledAdmissible, Bool.and_eq_true, List.all_eq_true,
    List.forall_mem_zipIdx'] at admitted ⊢
  constructor
  · have hb := admitted_depth c messages admitted.1
    simp only [admissible, decide_eq_true_eq, List.length_drop]
    omega
  · intro i hi
    have hi' : i < messages.reverse.length := by
      simp only [List.length_reverse, List.length_drop] at hi ⊢
      omega
    simpa only [List.reverse_drop, List.getElem_take] using admitted.2 i hi'

theorem scheduledAdmissible_tail (c : Config) (messages : List Pending)
    (admitted : scheduledAdmissible c messages = true) :
    scheduledAdmissible c messages.tail = true := by
  simpa only [List.drop_one] using scheduledAdmissible_drop c messages 1 admitted

end Whir.WHIRHistory
