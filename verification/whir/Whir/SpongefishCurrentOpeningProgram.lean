import Whir.SpongefishCurrentSourceJoinProbability
import Whir.PrunedMerkleCoverage
import Whir.SpongefishCurrentReplayProvenance
import Whir.PCSBCSConstructionReplayTrace

/-! Current #607 opening walk inside the counted source program. The replay of the static call list records exactly one `SourceEvent` per call, both in the actual cursor replay and in the semantic mode replay under arbitrary answers. The opening walk re-reads the opening segment of those events exactly like `SpongefishCurrentOpeningAcceptance.run` and authenticates each query batch with the existing whole-hash Merkle program. The full source program runs the old counted source program and then this walk as public verification hashing, so its real run returns the native `Collected` and every hashed opening input is in the program's primitive log. -/
namespace Whir.SpongefishCurrentOpeningProgram
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishCurrentModeQueries
open SpongefishCurrentAcceptedJoin SpongefishCurrentOpeningAcceptance
set_option autoImplicit false

/-! ## One source event per replayed call -/

/-- The event appended by one successful call. -/
def CallEvent : Call → SourceEvent → Prop
  | .read kind, e => ∃ value : kind.Value, e = .prover kind (kind.codec.bytes value)
  | .draw g, e => ∃ bytes : List Byte, bytes.length = g.bytes ∧ e = .verifier bytes
  | .hint, e => ∃ bytes : List Byte, e = .hint bytes

theorem read_events (c : Compression) (cur next : Cursor) (kind : WireKind) (value : kind.Value)
    (ok : SpongefishPCSRoundFrames.read c cur kind = some (next,value)) :
    next.events = cur.events ++ [.prover kind (kind.codec.bytes value)] := by
  unfold SpongefishPCSRoundFrames.read at ok
  cases hp : kind.codec.parse cur.narg with
  | none => simp [hp] at ok
  | some pair =>
    rcases pair with ⟨v,rest⟩
    simp only [hp] at ok
    rcases ok with ⟨rfl,rfl⟩
    rfl

theorem squeezeGroup_events (c : Compression) (cur next : Cursor) (g : Group) (bytes : List Byte)
    (ok : squeezeGroup c cur g = .ok (next,bytes)) :
    next.events = cur.events ++ [.verifier bytes] ∧ bytes.length = g.bytes := by
  cases hs : squeeze c cur.state g.bytes with
  | error e => simp [squeezeGroup,hs] at ok
  | ok pair =>
    rcases pair with ⟨s,out⟩
    simp only [squeezeGroup,hs] at ok
    cases ok
    exact ⟨rfl,(squeeze_exact_cursor c cur.state s g.bytes out hs).2⟩

theorem takeHint_events (cur next : Cursor) (ok : takeHint cur = some next) :
    ∃ bytes, cur.hints.head? = some bytes ∧ next.events = cur.events ++ [.hint bytes] := by
  unfold takeHint at ok
  cases hh : cur.hints with
  | nil => simp [hh] at ok
  | cons bytes rest =>
    simp only [hh,Option.some.injEq] at ok
    subst ok
    exact ⟨bytes,rfl,rfl⟩

theorem actualCall_events (c : Compression) (cur next : Cursor) (call : Call)
    (ok : SpongefishCurrentPrimitiveEventCompiler.actualCall c cur call = .ok next) :
    ∃ e, next.events = cur.events ++ [e] ∧ CallEvent call e := by
  cases call with
  | read kind =>
    simp only [SpongefishCurrentPrimitiveEventCompiler.actualCall] at ok
    cases hr : SpongefishPCSRoundFrames.read c cur kind with
    | none => simp [hr] at ok
    | some pair =>
      rcases pair with ⟨mid,value⟩
      simp only [hr,Except.ok.injEq] at ok
      subst ok
      exact ⟨_,read_events c cur mid kind value hr,value,rfl⟩
  | draw g =>
    simp only [SpongefishCurrentPrimitiveEventCompiler.actualCall] at ok
    cases hs : squeezeGroup c cur g with
    | error e => simp [hs] at ok
    | ok pair =>
      rcases pair with ⟨mid,bytes⟩
      simp only [hs,Except.ok.injEq] at ok
      subst ok
      obtain ⟨events,length⟩ := squeezeGroup_events c cur mid g bytes hs
      exact ⟨_,events,bytes,length,rfl⟩
  | hint =>
    simp only [SpongefishCurrentPrimitiveEventCompiler.actualCall] at ok
    cases ht : takeHint cur with
    | none => simp [ht] at ok
    | some mid =>
      simp only [ht,Except.ok.injEq] at ok
      subst ok
      obtain ⟨bytes,_,events⟩ := takeHint_events cur mid ht
      exact ⟨_,events,bytes,rfl⟩

/-- An accepted actual replay appends exactly one event per call, of the call's shape: reads append their canonical prover bytes, draws their squeezed bytes of the group's length, hints their hint bytes. -/
theorem actualReplay_events (c : Compression) :
    ∀ (calls : List Call) (cur next : Cursor),
      SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur calls = .ok next →
      ∃ evs, next.events = cur.events ++ evs ∧ List.Forall₂ CallEvent calls evs
  | [], cur, next, ok => by
    simp only [SpongefishCurrentPrimitiveEventCompiler.actualReplay,Except.ok.injEq] at ok
    subst ok
    exact ⟨[],by simp,.nil⟩
  | call :: calls, cur, next, ok => by
    simp only [SpongefishCurrentPrimitiveEventCompiler.actualReplay] at ok
    cases hc : SpongefishCurrentPrimitiveEventCompiler.actualCall c cur call with
    | error e => simp [hc] at ok
    | ok mid =>
      simp only [hc] at ok
      obtain ⟨e,first,shape⟩ := actualCall_events c cur mid call hc
      obtain ⟨evs,rest,shapes⟩ := actualReplay_events c calls mid next ok
      exact ⟨e :: evs,by rw [rest,first,List.append_assoc]; rfl,.cons shape shapes⟩

theorem actualReplay_events_length (c : Compression) (calls : List Call) (cur next : Cursor)
    (ok : SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur calls = .ok next) :
    ∃ evs, next.events = cur.events ++ evs ∧ evs.length = calls.length := by
  obtain ⟨evs,events,shapes⟩ := actualReplay_events c calls cur next ok
  exact ⟨evs,events,shapes.length_eq.symm⟩

/-! ## The same count in the semantic replay under arbitrary answers -/

open SpongefishCurrentMixedModeCompiler in
theorem collect_length (m : Pending) (positions : List Nat)
    (valid : ∀ p ∈ positions, DuplexEncoding.Admissible (coordinate m (p/32)))
    (cache : Cache) (trace : List Observation) (result : Cache × List Byte)
    (run : PublicMerkleProgram.Runs (collect m positions valid cache) trace result) :
    result.2.length = positions.length := by
  induction positions generalizing cache trace result with
  | nil =>
    cases run
    rfl
  | cons p ps ih =>
    simp only [collect] at run
    obtain ⟨_,⟨next,d⟩,after,_,_,rest⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp run
    obtain ⟨_,⟨last,bs⟩,_,_,tail,final⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp rest
    cases final
    simp [ih _ _ _ _ tail]

open SpongefishCurrentMixedModeCompiler in
/-- Every accepted semantic replay, under every sequence of construction answers (in particular every ideal simulator), appends exactly one event per call with the call's shape. -/
theorem replayProgram_events :
    ∀ (calls : List Call) (cur next : SemanticCursor) (trace : List Observation),
      PublicMerkleProgram.Runs (replayProgram cur calls) trace (.ok next) →
      ∃ evs, next.data.events = cur.data.events ++ evs ∧ List.Forall₂ CallEvent calls evs
  | [], cur, next, trace, run => by
    simp only [replayProgram] at run
    cases run
    exact ⟨[],by simp,.nil⟩
  | .read kind :: calls, cur, next, trace, run => by
    simp only [replayProgram] at run
    cases hp : kind.codec.parse cur.data.narg with
    | none =>
      simp only [hp] at run
      cases run
    | some pair =>
      rcases pair with ⟨value,rest⟩
      simp only [hp] at run
      obtain ⟨evs,events,shapes⟩ := replayProgram_events calls _ next trace run
      refine ⟨.prover kind (kind.codec.bytes value) :: evs,?_,.cons ⟨value,rfl⟩ shapes⟩
      rw [events]
      simp [readNext,boundData]
  | .hint :: calls, cur, next, trace, run => by
    simp only [replayProgram] at run
    cases hh : cur.data.hints with
    | nil =>
      simp only [hh] at run
      cases run
    | cons bytes rest =>
      simp only [hh] at run
      obtain ⟨evs,events,shapes⟩ := replayProgram_events calls _ next trace run
      refine ⟨.hint bytes :: evs,?_,.cons ⟨bytes,rfl⟩ shapes⟩
      rw [events]
      simp [hintNext]
  | .draw g :: calls, cur, next, trace, run => by
    simp only [replayProgram] at run
    split at run
    next zero =>
      obtain ⟨evs,events,shapes⟩ := replayProgram_events calls _ next trace run
      refine ⟨.verifier [] :: evs,?_,.cons ⟨[],by simp [zero],rfl⟩ shapes⟩
      rw [events]
      simp
    next =>
      split at run
      next guard =>
        obtain ⟨_,⟨cache,bytes⟩,after,_,collected,rest⟩ :=
          (PublicMerkleProgram.Runs.bind_iff _ _).mp run
        have length := collect_length _ _ _ _ _ _ collected
        obtain ⟨evs,events,shapes⟩ := replayProgram_events calls _ next after rest
        refine ⟨.verifier bytes :: evs,?_,.cons ⟨bytes,?_,rfl⟩ shapes⟩
        · rw [events]
          simp [drawn]
        · simpa [positions] using length
      next => cases run

theorem replayProgram_ideal_events {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State)
    (cur : SpongefishCurrentMixedModeCompiler.SemanticCursor) (calls : List Call)
    (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining (SpongefishCurrentMixedModeCompiler.replayProgram cur calls))
    (next : SpongefishCurrentMixedModeCompiler.SemanticCursor)
    (ok : (runIdeal sim ro iv state (SpongefishCurrentMixedModeCompiler.replayProgram cur calls)
      remaining cap counted).view.result = .ok next) :
    ∃ evs, next.data.events = cur.data.events ++ evs ∧ List.Forall₂ CallEvent calls evs := by
  have run := PublicMerkleProgram.runIdeal_runs sim ro iv state _ remaining cap counted
  rw [ok] at run
  exact replayProgram_events calls cur next _ run

/-- The old counted source program, under arbitrary answers: an accepted replay result carries the constructor's instance event followed by exactly one event per call of the static call list. -/
theorem program_events {p : ParameterBounds.Profile} (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (trace : List Observation)
    (data : SpongefishCurrentMixedModeCompiler.Data)
    (run : PublicMerkleProgram.Runs (SpongefishCurrentSourceJoinProbability.program iv tag
      instanceBytes layout before payloadCalls messages grinding prefixProgram) trace (some (.ok data))) :
    ∃ evs, data.events = .publicBytes instanceBytes :: evs ∧
      List.Forall₂ CallEvent
        (SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding) evs := by
  unfold SpongefishCurrentSourceJoinProbability.program SpongefishCurrentInitializedMode.afterPrefix at run
  obtain ⟨_,input,_,_,_,rest⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp run
  unfold SpongefishCurrentInitializedMode.program at rest
  obtain ⟨_,result,_,_,_,rest⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp rest
  cases result with
  | none => cases rest
  | some actual =>
    obtain ⟨_,replayed,_,_,replayRun,final⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp rest
    cases replayed with
    | error failure => cases final
    | ok cur =>
      cases final
      obtain ⟨evs,events,shapes⟩ := replayProgram_events _ _ cur _ replayRun
      exact ⟨evs,events,shapes⟩

/-! ## The opening walk over recorded events -/

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

abbrev Decoder := List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths

open PrunedMerkleProgram

/-- A prover event decoded with the expected codec. -/
def takeProver (kind : WireKind) : List SourceEvent → Option (kind.Value × List SourceEvent)
  | .prover _ bytes :: rest => (kind.codec.parse bytes).map fun parsed => (parsed.1,rest)
  | _ => none

def takeVerifier : List SourceEvent → Option (List Byte × List SourceEvent)
  | .verifier bytes :: rest => some (bytes,rest)
  | _ => none

def takeHintBytes : List SourceEvent → Option (List Byte × List SourceEvent)
  | .hint bytes :: rest => some (bytes,rest)
  | _ => none

def takeMessage (evs : List SourceEvent) : Option (Protocol.Message E × List SourceEvent) :=
  (takeProver (.vector 2) evs).map fun parsed => (⟨parsed.1 0,parsed.1 1⟩,parsed.2)

/-- Query proof of work read from its challenge and nonce events. -/
def powWalk (grinding : Fin (cfg).folds.size → Fin 64) (evs : List SourceEvent)
    (col : Collected p) : Coord p → Option (List SourceEvent × Collected p)
  | .query i =>
    if (grinding i).val = 0 then some (evs,col) else do
      let (bytes,rest) ← takeVerifier evs
      let (nonce,after) ← takeProver .nonce rest
      pure (after,{col with pows := col.pows ++
        [⟨i,grinding i,fun k => bytes[k.val]?.getD 0,nonce⟩]})
  | .initial => some (evs,col)
  | .fold _ _ => some (evs,col)
  | .ood _ _ => some (evs,col)
  | .tail _ => some (evs,col)

def drawWalk (evs : List SourceEvent) (q : Coord p) :
    Option (List SourceEvent × PCSBCSRounds.Raw q) :=
  if PCSBCSRounds.rawWidth q = 0 then some (evs,decodeSample q []) else
    (takeVerifier evs).map fun drawn => (drawn.2,decodeSample q drawn.1)

/-- Replies that hash nothing, in native wire order. -/
def replyPure (evs : List SourceEvent) (col : Collected p) : Coord p → Option (List SourceEvent × Collected p)
  | .initial => do
    let (m,rest) ← takeMessage evs
    pure (rest,{col with replies := col.replies.push (.initial m)})
  | .fold i j => do
    let (m,rest) ← takeMessage evs
    if isLastFold i j then
      if i.val + 1 < (cfg).folds.size then do
        let (root,after) ← takeProver .root rest
        let replies := col.replies.push (.fold m (some #[]) #[])
        pure (after,{col with replies := replies, roots := col.roots.push root})
      else do
        let (residual,after) ← takeProver (.vector (2^CausalGame.remaining cfg i.val)) rest
        pure (after,{col with replies := col.replies.push (.fold m none (Array.ofFn residual))})
    else pure (rest,{col with replies := col.replies.push (.fold m none #[])})
  | .ood _ _ => do
    let (y,rest) ← takeProver .scalar evs
    let (m,after) ← takeMessage rest
    pure (after,{col with replies := col.replies.push (.ood ⟨y,m⟩)})
  | .query _ => none
  | .tail j =>
    if isVisibleTail j then do
      let (m,rest) ← takeMessage evs
      pure (rest,{col with replies := col.replies.push (.tail m)})
    else some (evs,col)

def rowWords (lanes : Nat) (i : Fin (cfg).folds.size) : Nat :=
  if i.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p i.val

/-- The whole-hash version of `SpongefishCurrentOpeningAcceptance.openQuery`: the same pruned Merkle plan and the same row decoder. -/
def openProgram (lanes : Nat) (i : Fin (cfg).folds.size) (root : Digest32)
    (proof : MerkleTransport.PrunedMerklePaths) (x : CausalProbability.Sample (.query i)) :
    HashProgram (Option WHIRPhysicalVerifier.Opened) :=
  (plan proof root (ParameterBounds.length cfg i.val) (WHIRPhysicalVerifier.queryIndices p i x)
    (rowWords lanes i) (WHIRPhysicalVerifier.leafWords p i.val)).map
    (WHIRPhysicalVerifier.finishRows (i.val == 0) (rowWords lanes i) (WHIRPhysicalVerifier.leafWords p i.val))

/-- Query reply: hint event, decoded proof, authenticated rows, prover message. -/
def replyQuery (decode : Decoder) (lanes : Nat) (evs : List SourceEvent) (col : Collected p)
    (i : Fin (cfg).folds.size) : HashProgram (Option (List SourceEvent × Collected p)) :=
  match takeHintBytes evs with
  | none => .done none
  | some (hint,rest) =>
    match decode (WHIRPhysicalVerifier.queryIndices p i (CausalProbability.get (.query i) col.tape))
        (rowWords lanes i) hint with
    | none => .done none
    | some proof =>
      match col.roots[i.val]? with
      | none => .done none
      | some root =>
        (openProgram lanes i root proof (CausalProbability.get (.query i) col.tape)).map fun result =>
          match result with
          | none => none
          | some opened => (takeMessage rest).map fun read =>
            let replies := col.replies.push (.query opened.rows read.1)
            (read.2,{col with replies := replies, openings := col.openings ++ [⟨i,root,hint,proof,opened⟩]})

def replyWalk (decode : Decoder) (lanes : Nat) (evs : List SourceEvent) (col : Collected p) :
    Coord p → HashProgram (Option (List SourceEvent × Collected p))
  | .query i => replyQuery decode lanes evs col i
  | .initial => .done (replyPure evs col .initial)
  | .fold i j => .done (replyPure evs col (.fold i j))
  | .ood i j => .done (replyPure evs col (.ood i j))
  | .tail j => .done (replyPure evs col (.tail j))

def stepWalk (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat)
    (state : List SourceEvent × Collected p) (q : Coord p) :
    HashProgram (Option (List SourceEvent × Collected p)) :=
  match powWalk grinding state.1 state.2 q with
  | none => .done none
  | some (evs,col) =>
    match drawWalk evs q with
    | none => .done none
    | some (rest,x) => replyWalk decode lanes rest (recordSample col q x) q

def walkFrom (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    List (Coord p) → List SourceEvent × Collected p →
      HashProgram (Option (List SourceEvent × Collected p))
  | [], state => .done (some state)
  | q :: qs, state => (stepWalk decode grinding lanes state q).bind fun result =>
    match result with
    | none => .done none
    | some next => walkFrom decode grinding lanes qs next

/-- The opening walk: the native opening schedule over recorded events, from the commitment root, with every query batch authenticated by whole-hash calls. -/
def walk (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat)
    (root : Digest32) (evs : List SourceEvent) : HashProgram (Option (Collected p)) :=
  (walkFrom decode grinding lanes (WHIRHistory.schedule cfg) (evs,Collected.start root)).map
    (Option.map Prod.snd)

/-! ## Lowering is the existing Merkle row program -/

theorem program_bind_assoc {R S T : Type} (a : Program R) (f : R → Program S) (g : S → Program T) :
    WHIRModeFinal.bind (WHIRModeFinal.bind a f) g = WHIRModeFinal.bind a (fun r => WHIRModeFinal.bind (f r) g) := by
  induction a with
  | done r => rfl
  | ask q next ih => simp only [WHIRModeFinal.bind,ih]

theorem lower_map {R S : Type} (f : R → S) (h : HashProgram R) :
    (h.map f).lower = WHIRModeFinal.bind h.lower (fun r => .done (f r)) := by
  induction h with
  | done r => rfl
  | hash bytes next ih =>
    simp only [HashProgram.map,HashProgram.bind,HashProgram.lower,program_bind_assoc] at ih ⊢
    simp only [ih]

/-- The lowered query authentication is literally `WHIRPhysicalVerifier.openQuery`. -/
theorem openProgram_lower (lanes : Nat) (i : Fin (cfg).folds.size) (root : Digest32)
    (proof : MerkleTransport.PrunedMerklePaths) (x : CausalProbability.Sample (.query i)) :
    (openProgram lanes i root proof x).lower = WHIRPhysicalVerifier.openQuery p i lanes proof root x := by
  rw [openProgram,lower_map]
  rfl

theorem openProgram_eval (C : PrimitiveOracle) (lanes : Nat) (i : Fin (cfg).folds.size) (root : Digest32)
    (proof : MerkleTransport.PrunedMerklePaths) (x : CausalProbability.Sample (.query i)) :
    HashProgram.eval (PublicMerkleLog.hash C) (openProgram lanes i root proof x) =
      openQuery C lanes i root proof x := by
  rw [openProgram,HashProgram.eval_map,plan_eval]
  rfl

/-! ## The walk evaluates exactly like the native opening -/

theorem parse_bytes {A : Type} (codec : Codec A) (a : A) : codec.parse (codec.bytes a) = some (a,[]) := by
  simpa using Codec.parse_append codec a []

theorem readMessage_events (C : PrimitiveOracle) (cur next : Cursor) (m : Protocol.Message E)
    (ok : readMessage C cur = some (next,m)) :
    ∃ xs : Fin 2 → E, next.events = cur.events ++ [.prover (.vector 2) ((WireKind.vector 2).codec.bytes xs)] ∧
      m = ⟨xs 0,xs 1⟩ := by
  unfold readMessage at ok
  split at ok
  · cases ok
  next mid xs h =>
    cases ok
    exact ⟨xs,read_events _ _ _ _ _ h,rfl⟩

theorem powWalk_native (C : PrimitiveOracle) (grinding : Fin (cfg).folds.size → Fin 64)
    (cur next : Cursor) (col col' : Collected p) (q : Coord p)
    (ok : powStep C grinding cur col q = some (next,col')) :
    ∃ evs, next.events = cur.events ++ evs ∧
      ∀ suffix, powWalk grinding (evs ++ suffix) col q = some (suffix,col') := by
  cases q with
  | query i =>
    simp only [powStep] at ok
    split at ok
    next zero =>
      cases ok
      exact ⟨[],by simp,fun suffix => by simp [powWalk,zero]⟩
    next positive =>
      split at ok
      · cases ok
      next challenged bytes squeezed =>
        split at ok
        · cases ok
        next after nonce readOk =>
          cases ok
          obtain ⟨first,_⟩ := squeezeGroup_events _ _ _ _ _ squeezed
          have second := read_events _ _ _ _ _ readOk
          refine ⟨[.verifier bytes,.prover .nonce (WireKind.nonce.codec.bytes nonce)],?_,fun suffix => ?_⟩
          · rw [second,first]
            simp
          · simp [powWalk,positive,takeVerifier,takeProver,parse_bytes]
  | initial => cases ok; exact ⟨[],by simp,fun _ => rfl⟩
  | fold i j => cases ok; exact ⟨[],by simp,fun _ => rfl⟩
  | ood i j => cases ok; exact ⟨[],by simp,fun _ => rfl⟩
  | tail j => cases ok; exact ⟨[],by simp,fun _ => rfl⟩

theorem drawWalk_native (C : PrimitiveOracle) (cur next : Cursor) (q : Coord p)
    (x : PCSBCSRounds.Raw q) (ok : drawStep C cur q = some (next,x)) :
    ∃ evs, next.events = cur.events ++ evs ∧ ∀ suffix, drawWalk (evs ++ suffix) q = some (suffix,x) := by
  unfold drawStep at ok
  split at ok
  next zero =>
    cases ok
    exact ⟨[],by simp,fun suffix => by simp [drawWalk,zero]⟩
  next positive =>
    split at ok
    · cases ok
    next after bytes squeezed =>
      cases ok
      obtain ⟨events,_⟩ := squeezeGroup_events _ _ _ _ _ squeezed
      exact ⟨[.verifier bytes],events,fun suffix => by simp [drawWalk,positive,takeVerifier]⟩

theorem replyWalk_native (C : PrimitiveOracle) (decode : Decoder) (lanes : Nat)
    (cur next : Cursor) (col col' : Collected p) (q : Coord p)
    (ok : replyStep C decode lanes cur col q = some (next,col')) :
    ∃ evs, next.events = cur.events ++ evs ∧ ∀ suffix,
      HashProgram.eval (PublicMerkleLog.hash C) (replyWalk decode lanes (evs ++ suffix) col q) =
        some (suffix,col') := by
  cases q with
  | initial =>
    simp only [replyStep] at ok
    obtain ⟨⟨mid,m⟩,first,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    obtain ⟨xs,events,rfl⟩ := readMessage_events C _ _ _ first
    exact ⟨_,events,fun suffix => by simp [replyWalk,replyPure,HashProgram.eval,takeMessage,takeProver,parse_bytes]⟩
  | fold i j =>
    simp only [replyStep] at ok
    obtain ⟨⟨mid,m⟩,first,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨xs,events,rfl⟩ := readMessage_events C _ _ _ first
    split at ok
    next last =>
      split at ok
      next more =>
        obtain ⟨⟨after,root⟩,rootRead,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok
        have second := read_events _ _ _ _ _ rootRead
        refine ⟨[.prover (.vector 2) ((WireKind.vector 2).codec.bytes xs),
          .prover .root (WireKind.root.codec.bytes root)],?_,fun suffix => ?_⟩
        · rw [second,events]
          simp
        · simp [replyWalk,replyPure,HashProgram.eval,last,more,takeMessage,takeProver,parse_bytes]
      next final =>
        obtain ⟨⟨after,residual⟩,residualRead,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok
        have second := read_events _ _ _ _ _ residualRead
        refine ⟨[.prover (.vector 2) ((WireKind.vector 2).codec.bytes xs),
          .prover (.vector (2^CausalGame.remaining cfg i.val))
            ((WireKind.vector (2^CausalGame.remaining cfg i.val)).codec.bytes residual)],?_,
          fun suffix => ?_⟩
        · rw [second,events]
          simp
        · simp [replyWalk,replyPure,HashProgram.eval,last,final,takeMessage,takeProver,parse_bytes]
    next notLast =>
      cases ok
      exact ⟨_,events,fun suffix => by
        simp [replyWalk,replyPure,HashProgram.eval,notLast,takeMessage,takeProver,parse_bytes]⟩
  | ood i j =>
    simp only [replyStep] at ok
    obtain ⟨⟨mid,y⟩,first,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨⟨after,m⟩,second,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    have firstEvents := read_events _ _ _ _ _ first
    obtain ⟨xs,secondEvents,rfl⟩ := readMessage_events C _ _ _ second
    refine ⟨[.prover .scalar (WireKind.scalar.codec.bytes y),
      .prover (.vector 2) ((WireKind.vector 2).codec.bytes xs)],?_,fun suffix => ?_⟩
    · rw [secondEvents,firstEvents]
      simp
    · simp [replyWalk,replyPure,HashProgram.eval,takeMessage,takeProver,parse_bytes]
  | query i =>
    simp only [replyStep] at ok
    obtain ⟨hint,headEq,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨hinted,taken,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨proof,decoded,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨root,rootAt,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨opened,openOk,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨⟨after,m⟩,second,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    obtain ⟨bytes,head,firstEvents⟩ := takeHint_events _ _ taken
    rw [headEq] at head
    cases head
    obtain ⟨xs,secondEvents,rfl⟩ := readMessage_events C _ _ _ second
    have decoded' : decode (WHIRPhysicalVerifier.queryIndices p i
        (CausalProbability.get (.query i) col.tape)) (rowWords lanes i) hint = some proof := decoded
    refine ⟨[.hint hint,.prover (.vector 2) ((WireKind.vector 2).codec.bytes xs)],?_,fun suffix => ?_⟩
    · rw [secondEvents,firstEvents]
      simp
    · simp [replyWalk,replyQuery,takeHintBytes,decoded',rootAt,HashProgram.eval_map,openProgram_eval,openOk,
        takeMessage,takeProver,parse_bytes]
  | tail j =>
    change (if isVisibleTail j then (do
      let (next,m) ← readMessage C cur
      pure (next,{col with replies := col.replies.push (.tail m)})) else some (cur,col)) =
      some (next,col') at ok
    split at ok
    next visible =>
      obtain ⟨⟨after,m⟩,first,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok
      obtain ⟨xs,events,rfl⟩ := readMessage_events C _ _ _ first
      exact ⟨_,events,fun suffix => by
        simp [replyWalk,replyPure,HashProgram.eval,visible,takeMessage,takeProver,parse_bytes]⟩
    next hidden =>
      cases ok
      exact ⟨[],by simp,fun suffix => by simp [replyWalk,replyPure,HashProgram.eval,hidden]⟩

theorem stepWalk_native (C : PrimitiveOracle) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat)
    (state next : Cursor × Collected p) (q : Coord p)
    (ok : step C decode grinding lanes state q = some next) :
    ∃ evs, next.1.events = state.1.events ++ evs ∧ ∀ suffix,
      HashProgram.eval (PublicMerkleLog.hash C) (stepWalk decode grinding lanes (evs ++ suffix,state.2) q) =
        some (suffix,next.2) := by
  unfold step at ok
  obtain ⟨⟨powed,col⟩,powOk,ok⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨⟨drawn,x⟩,drawOk,ok⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨first,firstEvents,firstWalk⟩ := powWalk_native C grinding _ _ _ _ q powOk
  obtain ⟨second,secondEvents,secondWalk⟩ := drawWalk_native C _ _ q x drawOk
  obtain ⟨third,thirdEvents,thirdWalk⟩ := replyWalk_native C decode lanes _ next.1 _ next.2 q ok
  refine ⟨first ++ second ++ third,?_,fun suffix => ?_⟩
  · rw [thirdEvents,secondEvents,firstEvents]
    simp
  · simp only [stepWalk,List.append_assoc,firstWalk,secondWalk]
    exact thirdWalk suffix

theorem walkFrom_native (C : PrimitiveOracle) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    ∀ (qs : List (Coord p)) (state final : Cursor × Collected p),
      run C decode grinding lanes qs state = some final →
      ∃ evs, final.1.events = state.1.events ++ evs ∧ ∀ suffix,
        HashProgram.eval (PublicMerkleLog.hash C) (walkFrom decode grinding lanes qs (evs ++ suffix,state.2)) =
          some (suffix,final.2)
  | [], state, final, ok => by
    simp only [run,Option.some.injEq] at ok
    subst ok
    exact ⟨[],by simp,fun suffix => by simp [walkFrom,HashProgram.eval]⟩
  | q :: qs, state, final, ok => by
    simp only [run] at ok
    obtain ⟨mid,first,rest⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨front,frontEvents,frontWalk⟩ := stepWalk_native C decode grinding lanes state mid q first
    obtain ⟨back,backEvents,backWalk⟩ := walkFrom_native C decode grinding lanes qs mid final rest
    refine ⟨front ++ back,by rw [backEvents,frontEvents,List.append_assoc],fun suffix => ?_⟩
    simp only [walkFrom,HashProgram.eval_bind,List.append_assoc,frontWalk]
    exact backWalk suffix

/-- The native accepted opening is the pure evaluation of the walk on its own recorded events, with the ordinary Merkle hash. -/
theorem walk_native (C : PrimitiveOracle) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (cur final : Cursor) (root : Digest32)
    (col : Collected p)
    (ran : run C decode grinding lanes (WHIRHistory.schedule cfg) (cur,Collected.start root) =
      some (final,col)) :
    ∃ evs, final.events = cur.events ++ evs ∧
      HashProgram.eval (PublicMerkleLog.hash C) (walk decode grinding lanes root evs) = some col := by
  obtain ⟨evs,events,walked⟩ := walkFrom_native C decode grinding lanes _ _ _ ran
  refine ⟨evs,events,?_⟩
  have closed := walked []
  simp only [List.append_nil] at closed
  simp [walk,HashProgram.eval_map,closed]

/-! ## Every returned opening was authenticated by the walk's own hash calls -/

/-- A query opening whose proof opens at its root with the level geometry, and every hashed input of whose opened paths is among `calls`. -/
def Authenticated (H : MerkleTransport.Primitive) (o : QueryOpening p) (calls : List (List Byte)) : Prop :=
  (∃ queries width, o.proof.open H o.root (ParameterBounds.length cfg o.level.val) queries width
      (WHIRPhysicalVerifier.leafWords p o.level.val) = some o.opened.paths) ∧
  ∀ path ∈ o.opened.paths, ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing H), bytes ∈ calls

theorem Authenticated.mono {H : MerkleTransport.Primitive} {o : QueryOpening p} {a b : List (List Byte)}
    (h : Authenticated H o a) (sub : ∀ bytes ∈ a, bytes ∈ b) : Authenticated H o b :=
  ⟨h.1,fun path member bytes input => sub bytes (h.2 path member bytes input)⟩

theorem powWalk_openings (grinding : Fin (cfg).folds.size → Fin 64) (evs evs' : List SourceEvent)
    (col col' : Collected p) (q : Coord p) (ok : powWalk grinding evs col q = some (evs',col')) :
    col'.openings = col.openings := by
  cases q with
  | query i =>
    simp only [powWalk] at ok
    split at ok
    · cases ok; rfl
    · obtain ⟨⟨bytes,rest⟩,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      obtain ⟨⟨nonce,after⟩,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok; rfl
  | initial => cases ok; rfl
  | fold i j => cases ok; rfl
  | ood i j => cases ok; rfl
  | tail j => cases ok; rfl

theorem recordSample_openings (col : Collected p) (q : Coord p) (x : PCSBCSRounds.Raw q) :
    (recordSample col q x).openings = col.openings := by
  cases q <;> rfl

theorem replyPure_openings (evs evs' : List SourceEvent) (col col' : Collected p) (q : Coord p)
    (ok : replyPure evs col q = some (evs',col')) : col'.openings = col.openings := by
  cases q with
  | initial =>
    simp only [replyPure] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok; rfl
  | fold i j =>
    simp only [replyPure] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    split at ok
    · split at ok
      · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok; rfl
      · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok; rfl
    · cases ok; rfl
  | ood i j =>
    simp only [replyPure] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok; rfl
  | query i => cases ok
  | tail j =>
    simp only [replyPure] at ok
    split at ok
    · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok; rfl
    · cases ok; rfl

theorem replyQuery_openings (H : MerkleTransport.Primitive) (decode : Decoder) (lanes : Nat)
    (evs evs' : List SourceEvent) (col col' : Collected p) (i : Fin (cfg).folds.size)
    (ok : HashProgram.eval H (replyQuery decode lanes evs col i) = some (evs',col')) :
    ∀ o ∈ col'.openings, o ∈ col.openings ∨
      Authenticated H o (HashProgram.calls H (replyQuery decode lanes evs col i)) := by
  cases hh : takeHintBytes evs with
  | none => simp [replyQuery,hh,HashProgram.eval] at ok
  | some hinted =>
    obtain ⟨hint,rest⟩ := hinted
    cases hd : decode (WHIRPhysicalVerifier.queryIndices p i (CausalProbability.get (.query i) col.tape))
        (rowWords lanes i) hint with
    | none => simp [replyQuery,hh,hd,HashProgram.eval] at ok
    | some proof =>
      cases hr : col.roots[i.val]? with
      | none => simp [replyQuery,hh,hd,hr,HashProgram.eval] at ok
      | some root =>
        simp only [replyQuery,hh,hd,hr,HashProgram.eval_map] at ok ⊢
        rw [HashProgram.calls_map]
        cases ho : HashProgram.eval H (openProgram lanes i root proof (CausalProbability.get (.query i) col.tape)) with
        | none => simp [ho] at ok
        | some opened =>
          simp only [ho] at ok
          obtain ⟨read,_,ok⟩ := Option.map_eq_some_iff.mp ok
          cases ok
          intro o member
          rcases List.mem_append.mp member with old | new
          · exact .inl old
          · right
            rw [List.mem_singleton] at new
            subst new
            rw [openProgram,HashProgram.eval_map,plan_eval] at ho
            unfold WHIRPhysicalVerifier.finishRows at ho
            obtain ⟨paths,opens,decoded⟩ := Option.bind_eq_some_iff.mp ho
            obtain ⟨rows,_,same⟩ := Option.map_eq_some_iff.mp decoded
            subst same
            refine ⟨⟨_,_,opens⟩,fun path member bytes input => ?_⟩
            unfold openProgram
            rw [HashProgram.calls_map]
            exact plan_opening_inputs H proof root _ _ _ _ paths opens path member bytes input

theorem stepWalk_openings (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat)
    (state final : List SourceEvent × Collected p) (q : Coord p)
    (ok : HashProgram.eval H (stepWalk decode grinding lanes state q) = some final) :
    ∀ o ∈ final.2.openings, o ∈ state.2.openings ∨
      Authenticated H o (HashProgram.calls H (stepWalk decode grinding lanes state q)) := by
  cases hp : powWalk grinding state.1 state.2 q with
  | none => simp [stepWalk,hp,HashProgram.eval] at ok
  | some powed =>
    obtain ⟨evs,col⟩ := powed
    have powEq := powWalk_openings grinding _ _ _ _ q hp
    cases hd : drawWalk evs q with
    | none => simp [stepWalk,hp,hd,HashProgram.eval] at ok
    | some drawn =>
      obtain ⟨rest,x⟩ := drawn
      simp only [stepWalk,hp,hd] at ok ⊢
      have sampled := recordSample_openings col q x
      cases q with
      | query i =>
        intro o member
        rcases replyQuery_openings H decode lanes _ _ _ _ i ok o member with old | new
        · left
          rw [← powEq,← sampled]
          exact old
        · exact .inr new
      | initial =>
        have same := replyPure_openings _ _ _ _ _ ok
        intro o member
        left
        rw [← powEq,← sampled,← same]
        exact member
      | fold i j =>
        have same := replyPure_openings _ _ _ _ _ ok
        intro o member
        left
        rw [← powEq,← sampled,← same]
        exact member
      | ood i j =>
        have same := replyPure_openings _ _ _ _ _ ok
        intro o member
        left
        rw [← powEq,← sampled,← same]
        exact member
      | tail j =>
        have same := replyPure_openings _ _ _ _ _ ok
        intro o member
        left
        rw [← powEq,← sampled,← same]
        exact member

theorem walkFrom_openings (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    ∀ (qs : List (Coord p)) (state final : List SourceEvent × Collected p),
      HashProgram.eval H (walkFrom decode grinding lanes qs state) = some final →
      ∀ o ∈ final.2.openings, o ∈ state.2.openings ∨
        Authenticated H o (HashProgram.calls H (walkFrom decode grinding lanes qs state))
  | [], state, final, ok => by
    simp only [walkFrom,HashProgram.eval,Option.some.injEq] at ok
    subst ok
    exact fun o member => .inl member
  | q :: qs, state, final, ok => by
    simp only [walkFrom,HashProgram.eval_bind] at ok
    simp only [walkFrom,HashProgram.calls_bind]
    cases hs : HashProgram.eval H (stepWalk decode grinding lanes state q) with
    | none => simp [hs,HashProgram.eval] at ok
    | some mid =>
      simp only [hs] at ok ⊢
      intro o member
      rcases walkFrom_openings H decode grinding lanes qs mid final ok o member with old | new
      · rcases stepWalk_openings H decode grinding lanes state mid q hs o old with older | first
        · exact .inl older
        · exact .inr (first.mono fun bytes h => List.mem_append_left _ h)
      · exact .inr (new.mono fun bytes h => List.mem_append_right _ h)

/-- Every query opening returned by the walk is authenticated by the walk's own whole-hash calls. -/
theorem walk_openings (H : MerkleTransport.Primitive) (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (lanes : Nat) (root : Digest32) (evs : List SourceEvent) (col : Collected p)
    (ok : HashProgram.eval H (walk decode grinding lanes root evs) = some col) :
    ∀ o ∈ col.openings, Authenticated H o (HashProgram.calls H (walk decode grinding lanes root evs)) := by
  unfold walk at ok ⊢
  rw [HashProgram.eval_map] at ok
  rw [HashProgram.calls_map]
  obtain ⟨final,walked,same⟩ := Option.map_eq_some_iff.mp ok
  subst same
  intro o member
  rcases walkFrom_openings H decode grinding lanes _ _ final walked o member with start | done
  · cases start
  · exact done

/-! ## Uniform public Merkle budget -/

def walkBudget (p : ParameterBounds.Profile) : Nat :=
  ((WHIRHistory.schedule (ParameterBounds.config p)).map (WHIRPhysicalVerifier.sampleBudget p)).sum

theorem openProgram_certified (lanes : Nat) (i : Fin (cfg).folds.size) (root : Digest32)
    (proof : MerkleTransport.PrunedMerklePaths) (x : CausalProbability.Sample (.query i)) :
    HashProgram.Certified (WHIRPhysicalVerifier.queryBudget p i.val) (fun _ => True)
      (openProgram lanes i root proof x) := by
  have size : (WHIRPhysicalVerifier.queryIndices p i x).length = (cfg).queries[i.val]! := by
    unfold WHIRPhysicalVerifier.queryIndices
    rw [Array.length_toList]
    exact QueryBatchSoundness.queries_size _ _ _
  have uniform := plan_certified_uniform proof root (ParameterBounds.length cfg i.val)
    (WHIRPhysicalVerifier.queryIndices p i x) (rowWords lanes i) (WHIRPhysicalVerifier.leafWords p i.val)
  rw [uniformBudget,size] at uniform
  exact HashProgram.Certified.map uniform _ (fun _ _ => trivial)

theorem replyQuery_certified (decode : Decoder) (lanes : Nat) (evs : List SourceEvent)
    (col : Collected p) (i : Fin (cfg).folds.size) :
    HashProgram.Certified (WHIRPhysicalVerifier.queryBudget p i.val) (fun _ => True)
      (replyQuery decode lanes evs col i) := by
  unfold replyQuery
  split
  · trivial
  · split
    · trivial
    · split
      · trivial
      · exact HashProgram.Certified.map (openProgram_certified _ _ _ _ _) _ (fun _ _ => trivial)

theorem stepWalk_certified (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (lanes : Nat) (state : List SourceEvent × Collected p) (q : Coord p) :
    HashProgram.Certified (WHIRPhysicalVerifier.sampleBudget p q) (fun _ => True)
      (stepWalk decode grinding lanes state q) := by
  unfold stepWalk
  split
  · trivial
  · split
    · trivial
    · cases q with
      | query i => exact replyQuery_certified decode lanes _ _ i
      | initial => trivial
      | fold i j => trivial
      | ood i j => trivial
      | tail j => trivial

theorem walkFrom_certified (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    ∀ (qs : List (Coord p)) (state : List SourceEvent × Collected p),
      HashProgram.Certified ((qs.map (WHIRPhysicalVerifier.sampleBudget p)).sum) (fun _ => True)
        (walkFrom decode grinding lanes qs state)
  | [], _ => trivial
  | q :: qs, state => by
    rw [List.map_cons,List.sum_cons]
    apply HashProgram.Certified.bind (stepWalk_certified decode grinding lanes state q)
    intro result _
    cases result with
    | none => trivial
    | some next => exact walkFrom_certified decode grinding lanes qs next

/-- Every hash path of the walk, on every reply, is within the uniform budget. -/
theorem walk_certified (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat)
    (root : Digest32) (evs : List SourceEvent) :
    HashProgram.Certified (walkBudget p) (fun _ => True) (walk decode grinding lanes root evs) :=
  HashProgram.Certified.map (walkFrom_certified decode grinding lanes _ _) _ (fun _ _ => trivial)

/-! ## The full counted source program -/

abbrev FullResult (p : ParameterBounds.Profile) :=
  SpongefishCurrentSourceJoinProbability.SourceResult × Option (Collected p)

/-- Events before the first opening call: the constructor's instance event and one event per caller call (prelude, commitment header, payload, binding messages). -/
def openingOffset (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call) : Nat :=
  1 + (before ++ headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++ messages).length

/-- Position of the commitment header's raw32 root read. -/
def rootIndex (before : List Call) : Nat := 1 + before.length + 3

/-- The commitment root decoded from the header's root event. -/
def headerRoot (index : Nat) (events : List SourceEvent) : Option Digest32 :=
  match events[index]? with
  | some (.prover .root bytes) => (WireKind.root.codec.parse bytes).map Prod.fst
  | _ => none

def openingEvents (offset : Nat) (data : SpongefishCurrentMixedModeCompiler.Data) : List SourceEvent :=
  data.events.drop offset

/-- After an accepted replay, walk the opening events from the header root; otherwise return the source result unchanged. -/
def openingPhase (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64) (lanes index offset : Nat)
    (res : SpongefishCurrentSourceJoinProbability.SourceResult) : Program (FullResult p) :=
  match res with
  | some (.ok data) =>
    match headerRoot index data.events with
    | none => .done (res,none)
    | some root => WHIRModeFinal.bind (walk decode grinding lanes root (openingEvents offset data)).lower
        (fun col => .done (res,col))
  | _ => .done (res,none)

/-- The old counted source program followed by the public opening walk. -/
def fullProgram (iv : Digest32) (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) : Program (FullResult p) :=
  WHIRModeFinal.bind (SpongefishCurrentSourceJoinProbability.program iv tag instanceBytes layout before
      payloadCalls messages grinding prefixProgram)
    (openingPhase decode grinding (AnchoredSourceCaller.shape layout).lanes (rootIndex before)
      (openingOffset layout before payloadCalls messages))

def fullBudget (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (grinding : Fin (cfg).folds.size → Fin 64) (A : Nat) : Nat :=
  SpongefishCurrentSourceJoinProbability.budget tag instanceBytes layout before payloadCalls messages
    grinding A + walkBudget p

theorem openingPhase_counted (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (lanes index offset : Nat) (res : SpongefishCurrentSourceJoinProbability.SourceResult) :
    Counts (walkBudget p) (openingPhase decode grinding lanes index offset res) := by
  unfold openingPhase
  split
  · split
    · trivial
    · exact WHIRModeFinal.counts_mono (WHIRModeFinal.bind_counted _ _ (walkBudget p) 0
        (walk_certified _ _ _ _ _).counts (fun _ => trivial)) (by omega)
  · trivial

/-- All-reply count of the full program for every counted attacker prefix. -/
theorem fullProgram_counted (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram) :
    Counts (fullBudget tag instanceBytes layout before payloadCalls messages grinding A)
      (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding prefixProgram) :=
  WHIRModeFinal.bind_counted _ _ _ _
    (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram
      (SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding) A attacker)
    (fun res => openingPhase_counted decode grinding _ _ _ res)

/-- Initialized byte-source coupling of the full program, with arbitrary adaptive attacker prefix and rejection behavior. -/
theorem fullProgram_mode_bound {Coins : Type} [Fintype Coins] (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) (D : View (FullResult p) → Bool) :
    let Q := fullBudget tag instanceBytes layout before payloadCalls messages grinding A
    letI := DuplexPublicSimulator.seedFintype
    ModeAdv (DuplexPublicSimulator.simulator Q) iv
      (fun coin => fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coin))
      (fun coin => fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coin) A (attacker coin)) D ≤ min 1 ((2*(Q : ℚ)^2-(Q : ℚ))/2^256) := by
  simpa only [duplexModeLoss_eq] using
    PublicCompressionCouplingActualJoint.actual_modeAdv_le_duplexModeLoss
      (AdvCoins := Coins) (R := FullResult p) (fullBudget tag instanceBytes layout before payloadCalls messages
        grinding A) iv
      (fun coin => fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coin))
      (fun coin => fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode grinding
        (prefixProgram coin) A (attacker coin)) D

/-! ## The real run returns the native opening -/

theorem getElem?_prefix {α : Type} :
    ∀ (xs ys : List α) (n : Nat) (a : α), xs[n]? = some a → (xs ++ ys)[n]? = some a
  | [], _, _, _, h => by simp at h
  | _ :: _, _, 0, _, h => by simpa using h
  | _ :: xs, ys, n+1, a, h => by simpa using getElem?_prefix xs ys n a (by simpa using h)

theorem setup_events (c : Compression) (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (initial : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup c parameter tag instanceBytes narg hints =
      some initial) :
    initial.events = [.publicBytes instanceBytes] := by
  unfold SpongefishCurrentObservedSessionEntry.actualSetup at setup
  obtain ⟨_,_,same⟩ := Option.map_eq_some_iff.mp setup
  subst same
  rfl

/-- The commitment receive's fourth event is the raw32 root read of the record root. -/
theorem receive_root_event (c : Compression) (pre received : Cursor) (shape : AnchoredHeaderCodec.Shape)
    (r : SpongefishSessionAdapter.Record)
    (accepted : SpongefishCurrentCommitmentReceive.receive c pre shape = some (received,r)) :
    received.events[pre.events.length + 3]? = some (.prover .root (WireKind.root.codec.bytes r.root)) := by
  obtain ⟨_,_,_,header,sampled,bytes,_,readHeader,drawn,_,_,readValue⟩ :=
    SpongefishCurrentCommitmentReceive.receive_retains c pre received shape r accepted
  obtain ⟨_,_,_,_,headerEvents,_⟩ :=
    SpongefishCurrentAnchorHeader.readHeader_facts c pre header shape r.root readHeader
  have sampledEvents := (squeezeGroup_events c header sampled _ bytes drawn).1
  have valueEvents := read_events c sampled received .scalar r.value readValue
  rw [valueEvents,sampledEvents,headerEvents,List.append_assoc,List.append_assoc,
    List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
  simp [SpongefishCurrentAnchorHeader.fields,SpongefishRecordBindingParser.scalarMessages,
    SpongefishSessionAdapter.constants,SpongefishRecordBindingParser.Message.bytes]

/-- Under the witnesses of `SpongefishCurrentSourceJoinProbability.NativeAcceptedBad`, the real run of the full program returns the accepted replay and the native opening's `Collected`; every opening authenticates at its root with the level geometry, and every hashed input of every opened path is shorter than `2^56` bytes and has its complete primitive plan in the full program's primitive log. -/
theorem fullProgram_native (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram)
    (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (initial pre received payload next : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) iv tag instanceBytes
      (runReal C iv prefixProgram).view.result.narg
      (runReal C iv prefixProgram).view.result.hints = some initial)
    (preRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial before = .ok pre)
    (receivedEq : SpongefishCurrentCommitmentReceive.receive (compressionOf C) pre
      (AnchoredSourceCaller.shape layout) = some (received,r))
    (payloadRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) received payloadCalls =
      .ok payload)
    (bindingEq : SpongefishRecordBindingParser.verify (compressionOf C) payload r = some next)
    (messagesEq : messageCalls r = messages)
    (opened : Accepted C decode grinding r input next) :
    (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram)).view.result =
        (some (.ok (SpongefishCurrentMixedModeCompiler.forget opened.final)),some opened.collected) ∧
    ∀ o ∈ opened.collected.openings,
      (∃ queries width, o.proof.open (PublicMerkleLog.hash C) o.root (ParameterBounds.length cfg o.level.val)
        queries width (WHIRPhysicalVerifier.leafWords p o.level.val) = some o.opened.paths) ∧
      ∀ path ∈ o.opened.paths, ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing (PublicMerkleLog.hash C)),
        bytes.length < 2^56 ∧ ∀ e ∈ PublicMerkleLog.plan C bytes,
          e ∈ PublicCompressionProgram.primitiveLog C iv
            (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding prefixProgram)
            (fullBudget tag instanceBytes layout before payloadCalls messages grinding A)
            (fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode grinding
              prefixProgram A attacker) := by
  have shapeEq := (SpongefishCurrentCommitmentReceive.receive_retains _ pre received _ r receivedEq).1
  have tapeRun := composition_replay (compressionOf C) layout r before payloadCalls initial pre received
    payload next preRun receivedEq payloadRun bindingEq
  have sameCalls : SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding =
      (before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r) ++ openingCalls grinding := by
    rw [SpongefishCurrentSourceJoinProbability.calls,shapeEq,messagesEq]
  have whole : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial
      (SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding) =
        .ok opened.final := by
    rw [sameCalls,actualReplay_append _ _ _ initial next tapeRun]
    exact run_replay C decode grinding r.shape.lanes _ _ _ opened.ran
  have programReal : (runReal C iv (SpongefishCurrentSourceJoinProbability.program iv tag instanceBytes
      layout before payloadCalls messages grinding prefixProgram)).view.result =
        some (.ok (SpongefishCurrentMixedModeCompiler.forget opened.final)) := by
    unfold SpongefishCurrentSourceJoinProbability.program SpongefishCurrentInitializedMode.afterPrefix
    rw [WHIRModeFinal.bind_real_result,SpongefishCurrentInitializedMode.program_real]
    simp [SpongefishCurrentObservedSessionEntry.actualEntry,setup,whole,
      SpongefishCurrentMixedModeCompiler.forgetResult]
  -- event bookkeeping
  have initialEvents := setup_events _ _ _ _ _ _ initial setup
  obtain ⟨preEvs,preEvents,preLength⟩ :=
    actualReplay_events_length _ before initial pre preRun
  have rootEvent := receive_root_event _ pre received _ r receivedEq
  obtain ⟨payloadEvs,payloadEvents,_⟩ := actualReplay_events _ payloadCalls received payload payloadRun
  obtain ⟨bindingEvs,bindingEvents,_⟩ := actualReplay_events _ _ payload next
    (verifyFields_replay _ (SpongefishRecordBindingParser.messages r) payload next bindingEq)
  have ran := opened.ran
  rw [shapeEq] at ran
  obtain ⟨evs,finalEvents,walked⟩ := walk_native C decode grinding (AnchoredSourceCaller.shape layout).lanes
    next opened.final r.root opened.collected ran
  obtain ⟨tapeEvs,tapeEvents,tapeLength⟩ := actualReplay_events_length _ _ initial next tapeRun
  have rootAt : headerRoot (rootIndex before) opened.final.events = some r.root := by
    have index : rootIndex before = pre.events.length + 3 := by
      rw [rootIndex,preEvents,initialEvents,List.length_append,preLength]
      simp only [List.length_singleton]
    have located : opened.final.events[rootIndex before]? =
        some (.prover .root (WireKind.root.codec.bytes r.root)) := by
      rw [finalEvents,bindingEvents,payloadEvents,index]
      exact getElem?_prefix _ _ _ _ (getElem?_prefix _ _ _ _ (getElem?_prefix _ _ _ _ rootEvent))
    simp [headerRoot,located,parse_bytes]
  have offsetEq : openingEvents (openingOffset layout before payloadCalls messages)
      (SpongefishCurrentMixedModeCompiler.forget opened.final) = evs := by
    have length : openingOffset layout before payloadCalls messages = next.events.length := by
      rw [tapeEvents,initialEvents,List.length_append,tapeLength,openingOffset,← shapeEq,← messagesEq]
      simp only [List.length_singleton]
    change opened.final.events.drop _ = evs
    rw [length,finalEvents,List.drop_left]
  have phaseReal : (runReal C iv (openingPhase decode grinding (AnchoredSourceCaller.shape layout).lanes
      (rootIndex before) (openingOffset layout before payloadCalls messages)
      (some (.ok (SpongefishCurrentMixedModeCompiler.forget opened.final))))).view.result =
        (some (.ok (SpongefishCurrentMixedModeCompiler.forget opened.final)),some opened.collected) := by
    simp only [openingPhase]
    change (runReal C iv (match headerRoot (rootIndex before) opened.final.events with
      | none => _ | some root => _)).view.result = _
    rw [rootAt]
    dsimp only
    rw [WHIRModeFinal.bind_real_result,HashProgram.lower_real,offsetEq,walked]
    rfl
  refine ⟨?_,?_⟩
  · rw [fullProgram,WHIRModeFinal.bind_real_result,programReal]
    exact phaseReal
  · intro o member
    obtain ⟨⟨queries,width,accepted⟩,covered⟩ :=
      walk_openings (PublicMerkleLog.hash C) decode grinding _ r.root evs opened.collected walked o member
    refine ⟨⟨queries,width,accepted⟩,fun path pathMember bytes input => ⟨?_,?_⟩⟩
    · exact WHIRPhysicalVerifier.path_input_bounds_lt C o.proof o.root _ queries width
        (WHIRPhysicalVerifier.leafWords p o.level.val) (2^56) o.opened.paths accepted
        (WHIRPhysicalVerifier.production_leaf_byte_tag_zero p o.level) (by norm_num) path pathMember
        bytes input
    · intro e present
      have observed : (⟨.primitive .verification e.1,e.2⟩ : Observation) ∈
          (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
            prefixProgram)).view.observations := by
        rw [fullProgram,HashProgram.bind_real_observations,programReal]
        apply List.mem_append_right
        simp only [openingPhase]
        change _ ∈ (runReal C iv (match headerRoot (rootIndex before) opened.final.events with
          | none => _ | some root => _)).view.observations
        rw [rootAt]
        dsimp only
        rw [HashProgram.bind_real_observations,HashProgram.real_observations,offsetEq]
        apply List.mem_append_left
        exact List.mem_flatMap.mpr ⟨bytes,covered path pathMember bytes input,List.mem_map.mpr ⟨e,present,rfl⟩⟩
      have included := PCSBCSConstructionReplayTrace.observation_trace_membership C iv _ _
        (fullProgram_counted iv tag instanceBytes layout before payloadCalls messages decode grinding
          prefixProgram A attacker) _ observed
      have answer := PCSBCSConstructionReplayTrace.observation_answer C iv _ _ observed
      change e.2 = C e.1 at answer
      apply included e
      change e ∈ [(e.1,C e.1)]
      exact List.mem_singleton.mpr (Prod.ext rfl answer)

/-! ## The public original list is unchanged by the primitive-only phase -/

theorem openingPhase_primitive (C : PrimitiveOracle) (iv : Digest32) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes index offset : Nat)
    (res : SpongefishCurrentSourceJoinProbability.SourceResult) :
    ∀ o ∈ (runReal C iv (openingPhase decode grinding lanes index offset res)).view.observations,
      ∃ purpose n, o.query = .primitive purpose n := by
  unfold openingPhase
  split
  · split
    · simp [runReal]
    · rw [HashProgram.bind_real_observations,HashProgram.real_observations]
      intro o member
      rcases List.mem_append.mp member with walked | final
      · obtain ⟨_,_,mapped⟩ := List.mem_flatMap.mp walked
        obtain ⟨e,_,rfl⟩ := List.mem_map.mp mapped
        exact ⟨_,_,rfl⟩
      · simp [runReal] at final
  · simp [runReal]

theorem lookup_primitive (q : Coordinate) :
    ∀ (ys : List Observation), (∀ o ∈ ys, ∃ purpose n, o.query = .primitive purpose n) →
      SpongefishCurrentCallerGetter.lookup q ys = none
  | [], _ => rfl
  | y :: ys, primitive => by
    obtain ⟨purpose,n,hy⟩ := primitive y List.mem_cons_self
    simp only [SpongefishCurrentCallerGetter.lookup,hy]
    exact lookup_primitive q ys (fun o h => primitive o (List.mem_cons_of_mem _ h))

theorem lookup_append_primitive (q : Coordinate) (ys : List Observation)
    (primitive : ∀ o ∈ ys, ∃ purpose n, o.query = .primitive purpose n) :
    ∀ (xs : List Observation),
      SpongefishCurrentCallerGetter.lookup q (xs ++ ys) = SpongefishCurrentCallerGetter.lookup q xs
  | [] => lookup_primitive q ys primitive
  | x :: xs => by
    simp only [List.cons_append,SpongefishCurrentCallerGetter.lookup]
    split
    · split
      · rfl
      · exact lookup_append_primitive q ys primitive xs
    · exact lookup_append_primitive q ys primitive xs

theorem lookup_over_budget (q : Coordinate) (Q : Nat) (big : ¬ pathCost q ≤ Q) :
    ∀ (obs : List Observation), (∀ o ∈ obs, o.query.cost ≤ Q) →
      SpongefishCurrentCallerGetter.lookup q obs = none
  | [], _ => rfl
  | o :: os, capped => by
    simp only [SpongefishCurrentCallerGetter.lookup]
    split
    next other valid same =>
      split
      next equal =>
        have cost := capped o List.mem_cons_self
        rw [same] at cost
        subst equal
        exact absurd cost big
      next => exact lookup_over_budget q Q big os (fun o' h => capped o' (List.mem_cons_of_mem _ h))
    next => exact lookup_over_budget q Q big os (fun o' h => capped o' (List.mem_cons_of_mem _ h))

theorem answer_lift {Q Q' : Nat} (obs obs' : List Observation) (le : Q ≤ Q')
    (capped : ∀ o ∈ obs, o.query.cost ≤ Q)
    (same : ∀ q, SpongefishCurrentCallerGetter.lookup q obs' = SpongefishCurrentCallerGetter.lookup q obs) :
    SpongefishCurrentCallerGetter.answer (Q := Q') obs' = SpongefishCurrentCallerGetter.answer (Q := Q) obs := by
  funext query
  cases query with
  | primitive => rfl
  | construction q valid =>
    simp only [SpongefishCurrentCallerGetter.answer,SpongefishCurrentCallerGetter.bounded]
    by_cases small : pathCost q ≤ Q
    · simp [small,le_trans small le,same]
    · by_cases fits : pathCost q ≤ Q'
      · simp [small,fits,same,lookup_over_budget q Q small obs capped]
      · simp [small,fits]

/-- A public original at budget `Q` remains a public original at any larger budget, read from any observation list with the same construction lookups, provided every observation of the original list was within `Q`. -/
theorem original_lift {Q Q' : Nat} (layout : WHIRCallerClaims.CallerLayout) (iv : Digest32)
    (key : RawKey Q) (instanceBytes : List Byte) (obs obs' : List Observation) (le : Q ≤ Q')
    (capped : ∀ o ∈ obs, o.query.cost ≤ Q)
    (same : ∀ q, SpongefishCurrentCallerGetter.lookup q obs' = SpongefishCurrentCallerGetter.lookup q obs)
    (input : PCSBCSCallerBinding.CallerInput p)
    (member : input ∈ SpongefishCurrentSourceCallerOriginal.original p layout iv key instanceBytes obs) :
    ∃ (q : Coordinate) (work : pathCost q ≤ Q'),
      input ∈ SpongefishCurrentSourceCallerOriginal.original p layout iv (constructionKey Q' iv q work)
        instanceBytes obs' := by
  unfold SpongefishCurrentSourceCallerOriginal.original at member
  cases decoded : WHIRHeaderRoots.decodeRaw iv key with
  | none => simp [decoded] at member
  | some q =>
    simp only [decoded] at member
    obtain ⟨bound,valid,exactKey⟩ := WHIRHeaderRoots.decodeRaw_sound iv key q decoded
    refine ⟨q,le_trans bound le,?_⟩
    unfold SpongefishCurrentSourceCallerOriginal.original
    rw [WHIRHeaderRoots.decodeRaw_construction iv q valid,
      SpongefishCurrentRecordModeCapture.rawRecords_construction _ _ _ valid]
    rw [← exactKey,SpongefishCurrentRecordModeCapture.rawRecords_construction _ _ _ valid] at member
    have candidates : ∀ r, SpongefishCurrentSourceCallerOriginal.candidate (Q := Q') p layout q r
        instanceBytes obs' =
        SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout q r instanceBytes obs := by
      intro r
      unfold SpongefishCurrentSourceCallerOriginal.candidate SpongefishCurrentSourceCallerOriginal.replay
      rw [answer_lift obs obs' le capped same]
    simp only [candidates]
    exact member

/-- Real native acceptance with a property of the full program's view. -/
def NativeAcceptedBadFull (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (Bad : PCSBCSCallerBinding.CallerInput p → View (FullResult p) → Prop) : Prop :=
  ∃ (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (initial pre received payload next : Cursor),
    SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) iv tag instanceBytes
      (runReal C iv prefixProgram).view.result.narg
      (runReal C iv prefixProgram).view.result.hints = some initial ∧
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial before = .ok pre ∧
    SpongefishCurrentCommitmentReceive.receive (compressionOf C) pre
      (AnchoredSourceCaller.shape layout) = some (received,r) ∧
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) received payloadCalls =
      .ok payload ∧
    SpongefishRecordBindingParser.verify (compressionOf C) payload r = some next ∧
    messageCalls r = messages ∧
    Nonempty (Accepted C decode grinding r input next) ∧
    SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout
      (coordinate next.pending (next.pending.consumed / 32)) r instanceBytes = some input ∧
    Bad input (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode
      grinding prefixProgram)).view

/-- Public full-view event: some construction key's public original list contains an original with the property. -/
def PublicBadFull (Q : Nat) (iv : Digest32) (instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout)
    (Bad : PCSBCSCallerBinding.CallerInput p → View (FullResult p) → Prop)
    (view : View (FullResult p)) : Prop :=
  ∃ (q : Coordinate) (work : pathCost q ≤ Q) (input : PCSBCSCallerBinding.CallerInput p),
    input ∈ SpongefishCurrentSourceCallerOriginal.original p layout iv (constructionKey Q iv q work)
      instanceBytes view.observations ∧ Bad input view

/-- Pointwise join for the full program: real native acceptance places its prepared original in a public original list of the same full view, at the full budget. The appended opening phase only adds primitive observations. -/
theorem native_public_full (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (nonempty : instanceBytes ≠ []) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram)
    (Bad : PCSBCSCallerBinding.CallerInput p → View (FullResult p) → Prop)
    (native : NativeAcceptedBadFull C iv tag instanceBytes layout before payloadCalls messages decode
      grinding prefixProgram Bad) :
    PublicBadFull (fullBudget tag instanceBytes layout before payloadCalls messages grinding A) iv
      instanceBytes layout Bad (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls
        messages decode grinding prefixProgram)).view := by
  obtain ⟨r,input,initial,pre,received,payload,next,setup,preRun,receivedEq,payloadRun,bindingEq,
    messagesEq,⟨opened⟩,physical,bad⟩ := native
  have shapeEq := (SpongefishCurrentCommitmentReceive.receive_retains _ pre received _ r receivedEq).1
  have joined := accepted_opening_original C iv layout r tag instanceBytes prefixProgram A attacker
    nonempty before payloadCalls beforeEq payloadEq initial pre received payload next setup preRun
    receivedEq payloadRun bindingEq decode grinding input opened
  obtain ⟨_,_,_,work,_,_,member⟩ := joined
  have sameCalls : SpongefishCurrentSourceJoinProbability.calls layout before payloadCalls messages grinding =
      before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r ++ openingCalls grinding := by
    rw [SpongefishCurrentSourceJoinProbability.calls,shapeEq,messagesEq]
  have oldObservations : (runReal C iv (SpongefishCurrentSourceJoinProbability.program iv tag instanceBytes
      layout before payloadCalls messages grinding prefixProgram)).view.observations =
        (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram
          (before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r ++
            openingCalls grinding))).view.observations := by
    unfold SpongefishCurrentSourceJoinProbability.program
    rw [sameCalls]
  have capped := SpongefishCurrentReplayProvenance.observation_cap
    (SpongefishCurrentReplayProvenance.real_runs C iv _) _
    (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram
      (before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r ++ openingCalls grinding)
      A attacker)
  have le : A + SpongefishCurrentInitializedMode.budget tag instanceBytes
      (before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r ++ openingCalls grinding) ≤
        fullBudget tag instanceBytes layout before payloadCalls messages grinding A := by
    unfold fullBudget SpongefishCurrentSourceJoinProbability.budget
    rw [sameCalls]
    exact Nat.le_add_right _ _
  have fullObservations := HashProgram.bind_real_observations C iv
    (SpongefishCurrentSourceJoinProbability.program iv tag instanceBytes layout before payloadCalls
      messages grinding prefixProgram)
    (openingPhase decode grinding (AnchoredSourceCaller.shape layout).lanes (rootIndex before)
      (openingOffset layout before payloadCalls messages))
  rw [oldObservations] at fullObservations
  have same : ∀ q, SpongefishCurrentCallerGetter.lookup q
      (runReal C iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram)).view.observations =
      SpongefishCurrentCallerGetter.lookup q (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv
        tag instanceBytes prefixProgram (before ++ headerCalls r.shape.logN ++ payloadCalls ++
          messageCalls r ++ openingCalls grinding))).view.observations := by
    intro q
    rw [fullProgram,fullObservations]
    exact lookup_append_primitive q _ (openingPhase_primitive C iv decode grinding _ _ _ _) _
  obtain ⟨q,lifted,liftedMember⟩ := original_lift layout iv _ instanceBytes _ _ le capped same input
    (member input physical)
  exact ⟨q,lifted,input,liftedMember,bad⟩

#print axioms actualReplay_events
#print axioms replayProgram_events
#print axioms replayProgram_ideal_events
#print axioms program_events
#print axioms openProgram_lower
#print axioms walk_native
#print axioms walk_openings
#print axioms walk_certified
#print axioms fullProgram_counted
#print axioms fullProgram_mode_bound
#print axioms fullProgram_native
#print axioms native_public_full

end Whir.SpongefishCurrentOpeningProgram
