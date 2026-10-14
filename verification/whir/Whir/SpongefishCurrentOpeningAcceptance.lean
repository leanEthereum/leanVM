import Whir.SpongefishCurrentAcceptedJoin
import Whir.WHIRPhysicalVerifier
import Whir.AnchorPrefixRefinementCaller
import Whir.PCSBCSChallengeOracle

/-! Current #607 native PCS opening after expected-record binding. The verifier
walks the configured coordinate schedule over the actual byte cursor: query
proof of work, the grouped verifier draw, the decoded Merkle hint and the
prover reply. Each draw is decoded with the same grouped E codec as the
historical packets, each reply with the native wire order (fold coefficients,
raw32 root or full residual, OOD value and intro, query intro), and the
accepted opening is checked by the anchored native equation verifier on the
original family and point claims of the caller and the received record.

The Merkle hint wire codec is an explicit parameter receiving the query
positions and row width, as the native `PrunedMerklePaths::from_hint` does:
every theorem below holds for an arbitrary decoder. This module is the deterministic adapter; it is not
a probability or knowledge statement. -/
namespace Whir.SpongefishCurrentOpeningAcceptance
open Concrete Protocol CausalGame CausalProbability FiatShamirGame DuplexModeGame
open DuplexRefinement SpongefishPCSRoundFrames
set_option autoImplicit false
set_option maxRecDepth 10000

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

abbrev Coord (p : ParameterBounds.Profile) := Coordinate (ParameterBounds.config p)

/-! ## Current wire schedule of one coordinate -/

/-- Current draw group carrying a PCS coordinate. -/
def group : Coord p → Group
  | .initial => .stackFamilyAndLambda
  | .fold _ _ => .fold
  | .ood i _ => .ood (remaining cfg i.val - 1)
  | .query i => .queryAndLambda (remaining cfg i.val + (cfg).rates[i.val]!) (cfg).queries[i.val]!
  | .tail _ => .residualFold

/-- A zero-dimensional OOD point issues no verifier call. -/
def drawCalls (q : Coord p) : List Call :=
  if PCSBCSRounds.rawWidth q = 0 then [] else [.draw (group q)]

def isLastFold (i : Fin (cfg).folds.size) (j : Fin (cfg).folds[i.val]!) : Bool :=
  decide (j.val + 1 = (cfg).folds[i.val]!)

def isVisibleTail (j : Fin ((cfg).logN - (cfg).folds.toList.sum)) : Bool :=
  decide (j.val + 1 < (cfg).logN - (cfg).folds.toList.sum)

/-- Native reply order. A level-ending fold carries the next raw32 root, or the
full residual at the last level; the final tail draw has no reply. -/
def replyCalls : Coord p → List Call
  | .initial => [.read (.vector 2)]
  | .fold i j => [.read (.vector 2)] ++
      (if isLastFold i j then
        (if i.val + 1 < (cfg).folds.size then [.read .root]
          else [.read (.vector (2^remaining cfg i.val))])
      else [])
  | .ood _ _ => [.read .scalar,.read (.vector 2)]
  | .query _ => [.hint,.read (.vector 2)]
  | .tail j => if isVisibleTail j then [.read (.vector 2)] else []

/-- Query proof of work precedes its query draw; other coordinates have none. -/
def powCalls (grinding : Fin (cfg).folds.size → Fin 64) : Coord p → List Call
  | .query i => powSchedule (grinding i)
  | _ => []

def callsOf (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) : List Call :=
  powCalls grinding q ++ drawCalls q ++ replyCalls q

/-- The complete current opening call list after expected-record binding. -/
def openingCalls (grinding : Fin (cfg).folds.size → Fin 64) : List Call :=
  (WHIRHistory.schedule cfg).flatMap (callsOf grinding)

/-! ## Typed decoding -/

/-- The historical grouped decoder applied to the literal drawn bytes. -/
def decodeSample (q : Coord p) (bytes : List Byte) : PCSBCSRounds.Raw q :=
  (PCSBCSChallengeOracle.rawVector q).symm
    (fun k => ByteCodec.decodeE (fun i => bytes[24*k.val+i.val]?.getD 0))

def vectorList (n : Nat) (xs : Fin n → E) : List E := List.ofFn xs

/-- One Merkle query opening recorded for later authentication arguments. -/
structure QueryOpening (p : ParameterBounds.Profile) where
  level : Fin (ParameterBounds.config p).folds.size
  root : Digest32
  hint : List Byte
  proof : MerkleTransport.PrunedMerklePaths
  opened : WHIRPhysicalVerifier.Opened

/-- One positive query proof-of-work check, with its actual raw32 challenge. -/
structure PowCheck (p : ParameterBounds.Profile) where
  level : Fin (ParameterBounds.config p).folds.size
  bits : Fin 64
  challenge : Digest32
  nonce : UInt64

structure Collected (p : ParameterBounds.Profile) where
  tape : CausalGame.Tape (ParameterBounds.config p)
  seed : Option (RingPCSGame.Prefix × E)
  replies : Array Reply
  roots : Array Digest32
  openings : List (QueryOpening p)
  pows : List (PowCheck p)

def Collected.start (root : Digest32) : Collected p :=
  ⟨WHIRReplay.zeroTape p,none,#[],#[root],[],[]⟩

/-- Proof of work before a query draw, through the actual source operations. -/
def powStep (C : PrimitiveOracle) (grinding : Fin (cfg).folds.size → Fin 64)
    (cur : Cursor) (col : Collected p) : Coord p → Option (Cursor × Collected p)
  | .query i =>
    if (grinding i).val = 0 then some (cur,col) else
      match squeezeGroup (compressionOf C) cur .positivePow with
      | .error _ => none
      | .ok (challenged,bytes) =>
        match read (compressionOf C) challenged .nonce with
        | none => none
        | some (next,nonce) =>
          some (next,{col with pows := col.pows ++
            [⟨i,grinding i,fun k => bytes[k.val]?.getD 0,nonce⟩]})
  | _ => some (cur,col)

def drawStep (C : PrimitiveOracle) (cur : Cursor) (q : Coord p) :
    Option (Cursor × PCSBCSRounds.Raw q) :=
  if PCSBCSRounds.rawWidth q = 0 then some (cur,decodeSample q []) else
    match squeezeGroup (compressionOf C) cur (group q) with
    | .error _ => none
    | .ok (next,bytes) => some (next,decodeSample q bytes)

def recordSample (col : Collected p) (q : Coord p) (x : PCSBCSRounds.Raw q) : Collected p :=
  let sampled := {col with tape := CausalProbability.set q col.tape (StackWHIRReplay.projectSample q x)}
  match q, x with
  | .initial, x => {sampled with seed := some x}
  | _, _ => sampled

def readMessage (C : PrimitiveOracle) (cur : Cursor) : Option (Cursor × Message E) :=
  match read (compressionOf C) cur (.vector 2) with
  | none => none
  | some (next,xs) => some (next,⟨xs 0,xs 1⟩)

/-- Merkle authentication of one query batch on the decoded hint. -/
def openQuery (C : PrimitiveOracle) (lanes : Nat) (i : Fin (cfg).folds.size) (root : Digest32)
    (proof : MerkleTransport.PrunedMerklePaths) (x : CausalProbability.Sample (Coordinate.query i)) :
    Option WHIRPhysicalVerifier.Opened :=
  WHIRPhysicalVerifier.finishRows (i.val == 0)
    (if i.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p i.val)
    (WHIRPhysicalVerifier.leafWords p i.val)
    (proof.open (PublicMerkleLog.hash C) root (ParameterBounds.length cfg i.val)
      (WHIRPhysicalVerifier.queryIndices p i x)
      (if i.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p i.val)
      (WHIRPhysicalVerifier.leafWords p i.val))

/-- The prover reply at a coordinate, in native wire order. -/
def replyStep (C : PrimitiveOracle) (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (lanes : Nat) (cur : Cursor) (col : Collected p) : Coord p → Option (Cursor × Collected p)
  | .initial => do
    let (next,m) ← readMessage C cur
    pure (next,{col with replies := col.replies.push (.initial m)})
  | .fold i j => do
    let (next,m) ← readMessage C cur
    if isLastFold i j then
      if i.val + 1 < (cfg).folds.size then do
        let (after,root) ← read (compressionOf C) next .root
        let replies := col.replies.push (.fold m (some #[]) #[])
        pure (after,{col with replies := replies, roots := col.roots.push root})
      else do
        let (after,residual) ← read (compressionOf C) next (.vector (2^remaining cfg i.val))
        pure (after,{col with replies := col.replies.push (.fold m none (Array.ofFn residual))})
    else pure (next,{col with replies := col.replies.push (.fold m none #[])})
  | .ood _ _ => do
    let (next,y) ← read (compressionOf C) cur .scalar
    let (after,m) ← readMessage C next
    pure (after,{col with replies := col.replies.push (.ood ⟨y,m⟩)})
  | .query i => do
    let hint ← cur.hints.head?
    let hinted ← takeHint cur
    let proof ← decode (WHIRPhysicalVerifier.queryIndices p i (CausalProbability.get (.query i) col.tape))
      (if i.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p i.val) hint
    let root ← col.roots[i.val]?
    let opened ← openQuery C lanes i root proof (CausalProbability.get (.query i) col.tape)
    let (next,m) ← readMessage C hinted
    let replies := col.replies.push (.query opened.rows m)
    pure (next,{col with replies := replies, openings := col.openings ++ [⟨i,root,hint,proof,opened⟩]})
  | .tail j =>
    if isVisibleTail j then do
      let (next,m) ← readMessage C cur
      pure (next,{col with replies := col.replies.push (.tail m)})
    else some (cur,col)

def step (C : PrimitiveOracle) (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat)
    (state : Cursor × Collected p) (q : Coord p) : Option (Cursor × Collected p) := do
  let (powed,col) ← powStep C grinding state.1 state.2 q
  let (drawn,x) ← drawStep C powed q
  replyStep C decode lanes drawn (recordSample col q x) q

def run (C : PrimitiveOracle) (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    List (Coord p) → Cursor × Collected p → Option (Cursor × Collected p)
  | [], state => some state
  | q :: qs, state => do
    let next ← step C decode grinding lanes state q
    run C decode grinding lanes qs next

/-! ## Anchored native equations -/

/-- The anchored native equation verifier of `AnchoredPhysicalAnchor`, stated on
the current record's shape, point and value. -/
def anchoredVerify {m : Nat} (r : SpongefishSessionAdapter.Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (lambda : E) (c : Config) (ch : Challenges) (proof : Opening) :
    Except String Unit :=
  WHIRNativeArithmetic.nativeVerify c ch r.shape.lanes
    (WHIRNativeArithmetic.initialClaim family points seed lambda + lambda^(points.size+1)*r.value)
    (fun x => SuccinctRingGroups.sourceStackWeightAt family points seed lambda x +
      lambda^(points.size+1)*AnchoredPhysicalAnchor.anchorAt r.shape r.point.toArray x) proof

/-- The current check is literally the historical anchored native verifier on
any historical record with the same shape, point and value. -/
theorem anchoredVerify_historical {m : Nat} (r : SpongefishSessionAdapter.Record)
    (context : AnchoredHeaderCodec.Context) (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (c : Config) (ch : Challenges) (proof : Opening) :
    anchoredVerify r family points seed lambda c ch proof =
      AnchoredPhysicalAnchor.sourceVerify ⟨r.shape,r.root,context,r.point,r.value⟩
        family points seed lambda c ch proof := rfl

/-- Accepted native opening: every proof of work clears, the replies parse at
the configured shape, and the anchored native equations hold for the original
caller claims. Merkle hints authenticated inside `run`. -/
structure Accepted (C : PrimitiveOracle) (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (r : SpongefishSessionAdapter.Record)
    (input : PCSBCSCallerBinding.CallerInput p) (cur : Cursor) where
  final : Cursor
  collected : Collected p
  ran : run C decode grinding r.shape.lanes (WHIRHistory.schedule cfg)
    (cur,Collected.start r.root) = some (final,collected)
  pow : ∀ check ∈ collected.pows,
    SpongefishPowAdapter.clears check.bits (SpongefishPowAdapter.trial C check.challenge check.nonce) = true
  seed : RingPCSGame.Prefix × E
  seeded : collected.seed = some seed
  proof : Opening
  parsed : CausalGame.opening cfg (challenges cfg collected.tape) collected.replies = .ok proof
  equations : anchoredVerify r input.family input.points seed.1 seed.2 cfg
    (challenges cfg collected.tape) proof = .ok ()

/-- Executable acceptance decision with exactly the fields of `Accepted`. -/
def verify (C : PrimitiveOracle) (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (r : SpongefishSessionAdapter.Record)
    (input : PCSBCSCallerBinding.CallerInput p) (cur : Cursor) : Bool :=
  match run C decode grinding r.shape.lanes (WHIRHistory.schedule cfg) (cur,Collected.start r.root) with
  | none => false
  | some (_,collected) =>
    collected.pows.all (fun check =>
      SpongefishPowAdapter.clears check.bits (SpongefishPowAdapter.trial C check.challenge check.nonce)) &&
    match collected.seed with
    | none => false
    | some seed =>
      match CausalGame.opening cfg (challenges cfg collected.tape) collected.replies with
      | .error _ => false
      | .ok proof =>
        match anchoredVerify r input.family input.points seed.1 seed.2 cfg
            (challenges cfg collected.tape) proof with
        | .error _ => false
        | .ok () => true

theorem verify_accepted (C : PrimitiveOracle)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (r : SpongefishSessionAdapter.Record)
    (input : PCSBCSCallerBinding.CallerInput p) (cur : Cursor)
    (accepted : verify C decode grinding r input cur = true) :
    Nonempty (Accepted C decode grinding r input cur) := by
  unfold verify at accepted
  split at accepted
  · cases accepted
  next final collected ran =>
    rw [Bool.and_eq_true] at accepted
    obtain ⟨pows,rest⟩ := accepted
    split at rest
    · cases rest
    next seed seeded =>
      split at rest
      · cases rest
      next proof parsed =>
        split at rest
        · cases rest
        next equations =>
          exact ⟨⟨final,collected,ran,
            fun check member => List.all_eq_true.mp pows check member,
            seed,seeded,proof,parsed,equations⟩⟩

/-! ## Byte-level replay of the accepted opening -/

theorem squeezeGroup_call (c : Compression) (cur next : Cursor) (g : Group) (bytes : List Byte)
    (ok : squeezeGroup c cur g = .ok (next,bytes)) :
    SpongefishCurrentPrimitiveEventCompiler.actualCall c cur (.draw g) = .ok next := by
  simp [SpongefishCurrentPrimitiveEventCompiler.actualCall,ok]

theorem read_call (c : Compression) (cur next : Cursor) (kind : WireKind) (value : kind.Value)
    (ok : read c cur kind = some (next,value)) :
    SpongefishCurrentPrimitiveEventCompiler.actualCall c cur (.read kind) = .ok next := by
  simp [SpongefishCurrentPrimitiveEventCompiler.actualCall,ok]

theorem hint_call (c : Compression) (cur next : Cursor) (ok : takeHint cur = some next) :
    SpongefishCurrentPrimitiveEventCompiler.actualCall c cur .hint = .ok next := by
  simp [SpongefishCurrentPrimitiveEventCompiler.actualCall,ok]

theorem replay_cons (c : Compression) (cur mid next : Cursor) (call : Call) (calls : List Call)
    (first : SpongefishCurrentPrimitiveEventCompiler.actualCall c cur call = .ok mid)
    (rest : SpongefishCurrentPrimitiveEventCompiler.actualReplay c mid calls = .ok next) :
    SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur (call :: calls) = .ok next := by
  simp only [SpongefishCurrentPrimitiveEventCompiler.actualReplay,first]
  exact rest

theorem replay_nil (c : Compression) (cur : Cursor) :
    SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur [] = .ok cur := rfl

theorem readMessage_call (C : PrimitiveOracle) (cur next : Cursor) (m : Message E)
    (ok : readMessage C cur = some (next,m)) :
    SpongefishCurrentPrimitiveEventCompiler.actualCall (compressionOf C) cur (.read (.vector 2)) =
      .ok next := by
  unfold readMessage at ok
  split at ok
  · cases ok
  next mid xs h =>
    cases ok
    exact read_call _ _ _ _ xs h

theorem powStep_replay (C : PrimitiveOracle) (grinding : Fin (cfg).folds.size → Fin 64)
    (cur next : Cursor) (col col' : Collected p) (q : Coord p)
    (ok : powStep C grinding cur col q = some (next,col')) :
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) cur
      (powCalls grinding q) = .ok next := by
  cases q with
  | query i =>
    simp only [powStep] at ok
    simp only [powCalls,powSchedule]
    split at ok
    next zero =>
      simp only [zero,↓reduceIte]
      cases ok
      rfl
    next positive =>
      simp only [positive,↓reduceIte]
      split at ok
      · cases ok
      next challenged bytes squeezed =>
        split at ok
        · cases ok
        next after nonce readOk =>
          cases ok
          exact replay_cons _ _ _ _ _ _ (squeezeGroup_call _ _ _ _ _ squeezed)
            (replay_cons _ _ _ _ _ _ (read_call _ _ _ _ _ readOk) (replay_nil _ _))
  | initial => cases ok; rfl
  | fold i j => cases ok; rfl
  | ood i j => cases ok; rfl
  | tail j => cases ok; rfl

theorem drawStep_replay (C : PrimitiveOracle) (cur next : Cursor) (q : Coord p)
    (x : PCSBCSRounds.Raw q) (ok : drawStep C cur q = some (next,x)) :
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) cur (drawCalls q) =
      .ok next := by
  unfold drawStep at ok
  unfold drawCalls
  split at ok
  next zero =>
    simp only [zero,↓reduceIte]
    cases ok
    rfl
  next positive =>
    simp only [positive,↓reduceIte]
    split at ok
    · cases ok
    next after bytes squeezed =>
      cases ok
      exact replay_cons _ _ _ _ _ _ (squeezeGroup_call _ _ _ _ _ squeezed) (replay_nil _ _)

theorem replyStep_replay (C : PrimitiveOracle)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths) (lanes : Nat)
    (cur next : Cursor) (col col' : Collected p) (q : Coord p)
    (ok : replyStep C decode lanes cur col q = some (next,col')) :
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) cur (replyCalls q) =
      .ok next := by
  cases q with
  | initial =>
    simp only [replyStep] at ok
    obtain ⟨⟨mid,m⟩,first,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    exact replay_cons _ _ _ _ _ _ (readMessage_call C _ _ _ first) (replay_nil _ _)
  | fold i j =>
    simp only [replyStep] at ok
    obtain ⟨⟨mid,m⟩,first,ok⟩ := Option.bind_eq_some_iff.mp ok
    have head := readMessage_call C _ _ _ first
    simp only [replyCalls]
    split at ok
    next last =>
      simp only [last,↓reduceIte]
      split at ok
      next more =>
        simp only [more,↓reduceIte]
        obtain ⟨⟨after,root⟩,rootRead,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok
        exact replay_cons _ _ _ _ _ _ head
          (replay_cons _ _ _ _ _ _ (read_call _ _ _ _ _ rootRead) (replay_nil _ _))
      next final =>
        simp only [final,↓reduceIte]
        obtain ⟨⟨after,residual⟩,residualRead,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok
        exact replay_cons _ _ _ _ _ _ head
          (replay_cons _ _ _ _ _ _ (read_call _ _ _ _ _ residualRead) (replay_nil _ _))
    next notLast =>
      simp only [notLast,Bool.false_eq_true,↓reduceIte,List.append_nil]
      cases ok
      exact replay_cons _ _ _ _ _ _ head (replay_nil _ _)
  | ood i j =>
    simp only [replyStep] at ok
    obtain ⟨⟨mid,y⟩,first,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨⟨after,m⟩,second,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    exact replay_cons _ _ _ _ _ _ (read_call _ _ _ _ _ first)
      (replay_cons _ _ _ _ _ _ (readMessage_call C _ _ _ second) (replay_nil _ _))
  | query i =>
    simp only [replyStep] at ok
    obtain ⟨hint,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨hinted,taken,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨proof,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨root,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨opened,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨⟨after,m⟩,second,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    exact replay_cons _ _ _ _ _ _ (hint_call _ _ _ taken)
      (replay_cons _ _ _ _ _ _ (readMessage_call C _ _ _ second) (replay_nil _ _))
  | tail j =>
    change (if isVisibleTail j then (do
      let (next,m) ← readMessage C cur
      pure (next,{col with replies := col.replies.push (.tail m)})) else some (cur,col)) =
      some (next,col') at ok
    simp only [replyCalls]
    split at ok
    next visible =>
      simp only [visible,↓reduceIte]
      obtain ⟨⟨after,m⟩,first,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok
      exact replay_cons _ _ _ _ _ _ (readMessage_call C _ _ _ first) (replay_nil _ _)
    next hidden =>
      simp only [hidden,Bool.false_eq_true,↓reduceIte]
      cases ok
      rfl

theorem step_replay (C : PrimitiveOracle)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat)
    (state next : Cursor × Collected p) (q : Coord p)
    (ok : step C decode grinding lanes state q = some next) :
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) state.1
      (callsOf grinding q) = .ok next.1 := by
  unfold step at ok
  obtain ⟨⟨powed,col⟩,powOk,ok⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨⟨drawn,x⟩,drawOk,ok⟩ := Option.bind_eq_some_iff.mp ok
  have first := powStep_replay C grinding _ _ _ _ q powOk
  have second := drawStep_replay C _ _ q x drawOk
  have third := replyStep_replay C decode lanes _ next.1 _ next.2 q ok
  unfold callsOf
  rw [SpongefishCurrentAcceptedJoin.actualReplay_append _ _ _ _ _
    (by rw [SpongefishCurrentAcceptedJoin.actualReplay_append _ _ _ _ _ first]; exact second)]
  exact third

/-- The accepted native opening is one accepted actual replay of the literal
opening call list. -/
theorem run_replay (C : PrimitiveOracle)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    ∀ (qs : List (Coord p)) (state final : Cursor × Collected p),
      run C decode grinding lanes qs state = some final →
      SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) state.1
        (qs.flatMap (callsOf grinding)) = .ok final.1
  | [], state, final, ok => by
    simp only [run,Option.some.injEq] at ok
    subst ok
    rfl
  | q :: qs, state, final, ok => by
    simp only [run] at ok
    obtain ⟨mid,first,rest⟩ := Option.bind_eq_some_iff.mp ok
    rw [List.flatMap_cons,SpongefishCurrentAcceptedJoin.actualReplay_append _ _ _ _ _
      (step_replay C decode grinding lanes state mid q first)]
    exact run_replay C decode grinding lanes qs mid final rest

#print axioms run_replay

/-! ## Composition with the accepted caller path -/

theorem schedule_head : ∃ qs, WHIRHistory.schedule cfg = Coordinate.initial :: qs := by
  exact ⟨(visibleCoordinates cfg).tail ++ WHIRHistory.hiddenTail cfg,
    by simp [WHIRHistory.schedule,visibleCoordinates]⟩

theorem openingCalls_head (grinding : Fin (cfg).folds.size → Fin 64) :
    ∃ rest, openingCalls grinding = .draw .stackFamilyAndLambda :: rest := by
  obtain ⟨qs,head⟩ := schedule_head (p := p)
  refine ⟨replyCalls (p := p) .initial ++ qs.flatMap (callsOf grinding),?_⟩
  simp only [openingCalls,head,List.flatMap_cons,callsOf,powCalls,drawCalls,group,
    List.nil_append]
  rfl

/-! ## Proof of work at every ground query level -/

theorem powStep_pows (C : PrimitiveOracle) (grinding : Fin (cfg).folds.size → Fin 64)
    (cur next : Cursor) (col col' : Collected p) (q : Coord p)
    (ok : powStep C grinding cur col q = some (next,col')) :
    ∃ extra, col'.pows = col.pows ++ extra := by
  cases q with
  | query i =>
    simp only [powStep] at ok
    split at ok
    · cases ok; exact ⟨[],by simp⟩
    · split at ok
      · cases ok
      · split at ok
        · cases ok
        · cases ok; exact ⟨_,rfl⟩
  | initial => cases ok; exact ⟨[],by simp⟩
  | fold i j => cases ok; exact ⟨[],by simp⟩
  | ood i j => cases ok; exact ⟨[],by simp⟩
  | tail j => cases ok; exact ⟨[],by simp⟩

theorem powStep_query (C : PrimitiveOracle) (grinding : Fin (cfg).folds.size → Fin 64)
    (cur next : Cursor) (col col' : Collected p) (i : Fin (cfg).folds.size)
    (positive : (grinding i).val ≠ 0)
    (ok : powStep C grinding cur col (.query i) = some (next,col')) :
    ∃ check ∈ col'.pows, check.level = i ∧ check.bits = grinding i := by
  simp only [powStep,positive,↓reduceIte] at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · cases ok
      exact ⟨_,List.mem_append_right _ (List.mem_singleton_self _),rfl,rfl⟩

theorem recordSample_pows (col : Collected p) (q : Coord p) (x : PCSBCSRounds.Raw q) :
    (recordSample col q x).pows = col.pows := by
  cases q <;> rfl

theorem replyStep_pows (C : PrimitiveOracle)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths) (lanes : Nat)
    (cur next : Cursor) (col col' : Collected p) (q : Coord p)
    (ok : replyStep C decode lanes cur col q = some (next,col')) : col'.pows = col.pows := by
  cases q with
  | initial =>
    simp only [replyStep] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok; rfl
  | fold i j =>
    simp only [replyStep] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    split at ok
    · split at ok
      · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok; rfl
      · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok; rfl
    · cases ok; rfl
  | ood i j =>
    simp only [replyStep] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok; rfl
  | query i =>
    simp only [replyStep] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok; rfl
  | tail j =>
    change (if isVisibleTail j then (do
      let (next,m) ← readMessage C cur
      pure (next,{col with replies := col.replies.push (.tail m)})) else some (cur,col)) =
      some (next,col') at ok
    split at ok
    · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok; rfl
    · cases ok; rfl

theorem step_pows (C : PrimitiveOracle)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat)
    (state next : Cursor × Collected p) (q : Coord p)
    (ok : step C decode grinding lanes state q = some next) :
    ∃ extra, next.2.pows = state.2.pows ++ extra := by
  unfold step at ok
  obtain ⟨⟨powed,col⟩,powOk,ok⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨⟨drawn,x⟩,_,ok⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨extra,grown⟩ := powStep_pows C grinding _ _ _ _ q powOk
  refine ⟨extra,?_⟩
  rw [replyStep_pows C decode lanes _ next.1 _ next.2 q ok,recordSample_pows,grown]

theorem run_pows (C : PrimitiveOracle)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    ∀ (qs : List (Coord p)) (state final : Cursor × Collected p),
      run C decode grinding lanes qs state = some final →
      ∃ extra, final.2.pows = state.2.pows ++ extra
  | [], state, final, ok => by
    simp only [run,Option.some.injEq] at ok
    subst ok
    exact ⟨[],by simp⟩
  | q :: qs, state, final, ok => by
    simp only [run] at ok
    obtain ⟨mid,first,rest⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨a,ha⟩ := step_pows C decode grinding lanes state mid q first
    obtain ⟨b,hb⟩ := run_pows C decode grinding lanes qs mid final rest
    exact ⟨a ++ b,by rw [hb,ha,List.append_assoc]⟩

theorem run_query_pow (C : PrimitiveOracle)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (i : Fin (cfg).folds.size)
    (positive : (grinding i).val ≠ 0) :
    ∀ (qs : List (Coord p)) (state final : Cursor × Collected p), .query i ∈ qs →
      run C decode grinding lanes qs state = some final →
      ∃ check ∈ final.2.pows, check.level = i ∧ check.bits = grinding i
  | [], _, _, member, _ => by cases member
  | q :: qs, state, final, member, ok => by
    simp only [run] at ok
    obtain ⟨mid,first,rest⟩ := Option.bind_eq_some_iff.mp ok
    rcases List.mem_cons.mp member with same | later
    · subst same
      unfold step at first
      obtain ⟨⟨powed,col⟩,powOk,first⟩ := Option.bind_eq_some_iff.mp first
      obtain ⟨⟨drawn,x⟩,_,first⟩ := Option.bind_eq_some_iff.mp first
      obtain ⟨check,checkMember,level,bits⟩ := powStep_query C grinding _ _ _ _ i positive powOk
      have midPows : mid.2.pows = col.pows := by
        rw [replyStep_pows C decode lanes _ mid.1 _ mid.2 _ first,recordSample_pows]
      obtain ⟨extra,grown⟩ := run_pows C decode grinding lanes qs mid final rest
      refine ⟨check,?_,level,bits⟩
      rw [grown,midPows]
      exact List.mem_append_left _ checkMember
    · exact run_query_pow C decode grinding lanes i positive qs mid final later rest

/-- Every ground query level of an accepted opening executed its proof of work
on the actual raw32 challenge, and that work cleared the configured difficulty. -/
theorem accepted_pow {C : PrimitiveOracle}
    {decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths}
    {grinding : Fin (cfg).folds.size → Fin 64} {r : SpongefishSessionAdapter.Record}
    {input : PCSBCSCallerBinding.CallerInput p} {cur : Cursor}
    (a : Accepted C decode grinding r input cur) (i : Fin (cfg).folds.size)
    (positive : (grinding i).val ≠ 0) :
    ∃ check ∈ a.collected.pows, check.level = i ∧ check.bits = grinding i ∧
      SpongefishPowAdapter.clears (grinding i)
        (SpongefishPowAdapter.trial C check.challenge check.nonce) = true := by
  obtain ⟨check,member,level,bits⟩ := run_query_pow C decode grinding r.shape.lanes i positive
    (WHIRHistory.schedule cfg) _ _ (WHIRHistory.coordinate_mem_schedule _) a.ran
  refine ⟨check,member,level,bits,?_⟩
  rw [← bits]
  exact a.pow check member

/-! ## Accepted caller path followed by the accepted opening -/

/-- The first opening draw passes the source cursor guard. -/
theorem first_draw_guard (C : PrimitiveOracle) (iv : Digest32)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (r : SpongefishSessionAdapter.Record)
    (input : PCSBCSCallerBinding.CallerInput p) (cur : Cursor)
    (represented : RepresentsCurrent (compressionOf C) iv cur.pending cur.state)
    (a : Accepted C decode grinding r input cur) :
    cur.pending.consumed + Group.stackFamilyAndLambda.bytes ≤ maxCursor := by
  obtain ⟨qs,head⟩ := schedule_head (p := p)
  have ran := a.ran
  rw [head] at ran
  simp only [run] at ran
  obtain ⟨mid,first,_⟩ := Option.bind_eq_some_iff.mp ran
  unfold step at first
  obtain ⟨⟨powed,col⟩,powOk,first⟩ := Option.bind_eq_some_iff.mp first
  obtain ⟨⟨drawn,x⟩,drawOk,_⟩ := Option.bind_eq_some_iff.mp first
  simp only [powStep,Option.some.injEq,Prod.mk.injEq] at powOk
  obtain ⟨rfl,rfl⟩ := powOk
  unfold drawStep at drawOk
  have width : PCSBCSRounds.rawWidth (Coordinate.initial : Coord p) ≠ 0 := by
    simp [PCSBCSRounds.rawWidth,WHIRHistory.stackScalarCount]
  simp only [width,↓reduceIte] at drawOk
  split at drawOk
  · cases drawOk
  next next bytes squeezed =>
    unfold squeezeGroup at squeezed
    cases sq : squeeze (compressionOf C) cur.state (group (p := p) .initial).bytes with
    | error e => simp [sq] at squeezed
    | ok pair =>
      have bound : cur.state.consumed + (group (p := p) .initial).bytes ≤ maxCursor := by
        unfold squeeze at sq
        split at sq
        next zero => simp [group,Group.bytes,Group.elements] at zero
        next =>
          split at sq
          next fits => exact fits
          next => cases sq
      rw [SpongefishCurrentMixedModeCompiler.cursor_eq (compressionOf C) iv cur represented] at bound
      exact bound

open SpongefishCurrentAcceptedJoin DuplexFraming SpongefishCurrentModeQueries in
/-- An accepted #607 caller path (setup, prelude, commitment receive, payload and
expected-record binding) followed by an accepted native opening: the received
record is among the raw-decoded candidates of the post-binding construction key,
the public parser's prepared original equals the physical one, every prepared
original is in the public original list, the whole tape and opening are one
accepted actual replay, every ground query level's proof of work cleared, and
the anchored native equations hold for the prepared original claims. -/
theorem accepted_opening_original (C : PrimitiveOracle) (iv : Digest32)
    (layout : WHIRCallerClaims.CallerLayout)
    (r : SpongefishSessionAdapter.Record) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (A : Nat) (attacker : Counts A prefixProgram) (nonempty : instanceBytes ≠ [])
    (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (initial pre received payload next : Cursor)
    (setup : SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) iv tag instanceBytes
      (runReal C iv prefixProgram).view.result.narg
      (runReal C iv prefixProgram).view.result.hints = some initial)
    (preRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial before =
      .ok pre)
    (receivedEq : SpongefishCurrentCommitmentReceive.receive (compressionOf C) pre
      (AnchoredSourceCaller.shape layout) = some (received, r))
    (payloadRun : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) received
      payloadCalls = .ok payload)
    (bindingEq : SpongefishRecordBindingParser.verify (compressionOf C) payload r = some next)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (input : PCSBCSCallerBinding.CallerInput p)
    (opened : Accepted C decode grinding r input next) :
    let tape := before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes (tape ++ openingCalls grinding)
    let q := coordinate next.pending (next.pending.consumed / 32)
    let observations := (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv tag
      instanceBytes prefixProgram (tape ++ openingCalls grinding))).view.observations
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial
        (tape ++ openingCalls grinding) = .ok opened.final ∧
    (∀ i : Fin (cfg).folds.size, (grinding i).val ≠ 0 →
      ∃ check ∈ opened.collected.pows, check.level = i ∧ check.bits = grinding i ∧
        SpongefishPowAdapter.clears (grinding i)
          (SpongefishPowAdapter.trial C check.challenge check.nonce) = true) ∧
    anchoredVerify r input.family input.points opened.seed.1 opened.seed.2 cfg
      (challenges cfg opened.collected.tape) opened.proof = .ok () ∧
    ∃ work : pathCost q ≤ Q,
      r ∈ SpongefishCurrentRecordModeCapture.rawRecords (AnchoredSourceCaller.shape layout) iv
        (constructionKey Q iv q work) ∧
      SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout q r instanceBytes observations =
        SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r instanceBytes ∧
      ∀ prepared, SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r
          instanceBytes = some prepared →
        prepared ∈ SpongefishCurrentSourceCallerOriginal.original p layout iv
          (constructionKey Q iv q work) instanceBytes observations := by
  intro tape Q q observations
  have tapeRun := composition_replay (compressionOf C) layout r before payloadCalls initial pre
    received payload next preRun receivedEq payloadRun bindingEq
  have openRun := run_replay C decode grinding r.shape.lanes (WHIRHistory.schedule cfg) _ _ opened.ran
  have whole : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial
      (tape ++ openingCalls grinding) = .ok opened.final := by
    rw [actualReplay_append (compressionOf C) _ _ initial next tapeRun]
    exact openRun
  have initialRep : RepresentsCurrent (compressionOf C) iv initial.pending initial.state := by
    have initialEq : SpongefishCurrentObservedSessionEntry.cursor
        (SpongefishSessionAdapter.derive (compressionOf C) iv tag) instanceBytes
        (runReal C iv prefixProgram).view.result.narg (runReal C iv prefixProgram).view.result.hints
        (absorb (compressionOf C) (SpongefishSessionAdapter.init (compressionOf C) iv
          (SpongefishSessionAdapter.derive (compressionOf C) iv tag)) instanceBytes) = initial := by
      simpa [SpongefishCurrentObservedSessionEntry.actualSetup, SpongefishSessionAdapter.newSession,
        nonempty] using setup
    rw [← initialEq]
    simpa [SpongefishCurrentObservedSessionEntry.cursor,nonempty] using
      session_bridge (compressionOf C) iv (SpongefishSessionAdapter.derive (compressionOf C) iv tag)
        instanceBytes
  have nextRep : RepresentsCurrent (compressionOf C) iv next.pending next.state := by
    have erased := SpongefishCurrentPrimitiveEventCompiler.actualReplay_erases (compressionOf C)
      initial tape
    rw [tapeRun] at erased
    exact all_round_replay_bridge (compressionOf C) iv initial next tape initialRep erased.symm
  have guard := first_draw_guard C iv decode grinding r input next nextRep opened
  obtain ⟨rest,head⟩ := openingCalls_head (p := p) grinding
  have joined := accepted_original_next C iv p layout r tag instanceBytes prefixProgram
    .stackFamilyAndLambda rest A attacker nonempty before payloadCalls beforeEq payloadEq
    initial pre received payload next setup preRun receivedEq payloadRun bindingEq
    (by decide) guard
  rw [← head] at joined
  exact ⟨whole,accepted_pow opened,opened.equations,joined⟩

#print axioms accepted_pow
#print axioms accepted_opening_original

end Whir.SpongefishCurrentOpeningAcceptance
