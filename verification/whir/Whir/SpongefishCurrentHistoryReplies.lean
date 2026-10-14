import Whir.SpongefishCurrentOpeningPackets
import Whir.SpongefishCurrentOpeningProgram
import Whir.SpongefishCurrentOpeningExperiment
import Whir.SpongefishCurrentRootPolicy
import Whir.SpongefishCurrentGoodEvent

/-! Current #607 opening replies parsed from a packet's key history.

The opening replays one source event per call of `openingCalls`: reads bind their canonical bytes into the pending prover run, every opening draw is positive and closes that run into a frame, and hints absorb nothing. On the ideal tables of `SpongefishCurrentOpeningPackets.opening_packets`, the history of the `j`-th opening draw therefore holds, from frame index `boundary + 1` on, exactly the prover runs after the first `j` opening draws (`opening_frames`). The opening adds no byte before its first draw, and the first history is the post-binding coordinate's history.

`historyReplies` walks the opening schedule over these frames. It decodes every read with the codec of `replyPure`/`replyQuery` and stops when the frames run out. Query rows are the rows of the supplied level oracle at the tape's query indices, and a level-ending fold carries the oracle of the next level. On the key history of the draw of coordinate `q`, these replies agree before position `q` with the walk's restored replies (`replies_exact`, `replies_exact_local`). The same per-coordinate analysis of the walk gives the reply-position invariant (`reply_positions`, `query_reply`), the tape and seed at every draw (`tape_draw`, `tape_zero`, `seed_draw`), and the level roots (`root_start`, `level_root`, `level_roots_of_frames`). -/
namespace Whir.SpongefishCurrentHistoryReplies
open Concrete Protocol CausalGame CausalProbability FiatShamirGame
open SpongefishPCSRoundFrames SpongefishCurrentOpeningAcceptance SpongefishCurrentOpeningProgram
open SpongefishCurrentOpeningPackets PrunedMerkleProgram
set_option autoImplicit false

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

/-! ## Prover runs between verifier draws -/

/-- Prover bytes of an event list before its first verifier event. -/
def leadBytes : List SourceEvent → List Byte
  | [] => []
  | .prover _ bytes :: rest => bytes ++ leadBytes rest
  | .verifier _ :: _ => []
  | .hint _ :: rest => leadBytes rest
  | .publicBytes _ :: rest => leadBytes rest

/-- For every verifier event, the concatenated prover bytes up to the next verifier event. -/
def drawRuns : List SourceEvent → List (List Byte)
  | [] => []
  | .prover _ _ :: rest => drawRuns rest
  | .verifier _ :: rest => leadBytes rest :: drawRuns rest
  | .hint _ :: rest => drawRuns rest
  | .publicBytes _ :: rest => drawRuns rest

/-! ## The history parser -/

/-- Parser state: unread bytes of the current frame and the later frames. -/
abbrev Reader := List Byte × List (List Byte)

def readKind (kind : WireKind) (s : Reader) : Option (kind.Value × Reader) :=
  (kind.codec.parse s.1).map fun parsed => (parsed.1,(parsed.2,s.2))

/-- A positive verifier draw closes the current frame; the next frame holds the following prover bytes. -/
def nextFrame (s : Reader) : Option Reader :=
  match s.2 with
  | [] => none
  | bytes :: more => some (bytes,more)

def readPair (s : Reader) : Option (Message E × Reader) :=
  (readKind (.vector 2) s).map fun parsed => (⟨parsed.1 0,parsed.1 1⟩,parsed.2)

def powRead (grinding : Fin (cfg).folds.size → Fin 64) (s : Reader) : Coord p → Option Reader
  | .query i =>
    if (grinding i).val = 0 then some s else do
      let s ← nextFrame s
      let (_,s) ← readKind .nonce s
      pure s
  | .initial => some s
  | .fold _ _ => some s
  | .ood _ _ => some s
  | .tail _ => some s

def drawRead (s : Reader) (q : Coord p) : Option Reader :=
  if PCSBCSRounds.rawWidth q = 0 then some s else nextFrame s

/-- Replies decoded with the codecs of `replyPure`; query rows and next oracles are left empty here. -/
def replyRead (s : Reader) (replies : Array Reply) : Coord p → Option (Reader × Array Reply)
  | .initial => do
    let (m,s) ← readPair s
    pure (s,replies.push (.initial m))
  | .fold i j => do
    let (m,s) ← readPair s
    if isLastFold i j then
      if i.val + 1 < (cfg).folds.size then do
        let (_,s) ← readKind .root s
        pure (s,replies.push (.fold m (some #[]) #[]))
      else do
        let (residual,s) ← readKind (.vector (2^CausalGame.remaining cfg i.val)) s
        pure (s,replies.push (.fold m none (Array.ofFn residual)))
    else pure (s,replies.push (.fold m none #[]))
  | .ood _ _ => do
    let (y,s) ← readKind .scalar s
    let (m,s) ← readPair s
    pure (s,replies.push (.ood ⟨y,m⟩))
  | .query _ => do
    let (m,s) ← readPair s
    pure (s,replies.push (.query #[] m))
  | .tail j =>
    if isVisibleTail j then do
      let (m,s) ← readPair s
      pure (s,replies.push (.tail m))
    else some (s,replies)

def stepRead (grinding : Fin (cfg).folds.size → Fin 64) (state : Reader × Array Reply) (q : Coord p) :
    Option (Reader × Array Reply) := do
  let s ← powRead grinding state.1 q
  let s ← drawRead s q
  replyRead s state.2 q

/-- Parse coordinates in order until the frames run out; the replies parsed so far are kept. -/
def walkRead (grinding : Fin (cfg).folds.size → Fin 64) :
    List (Coord p) → Reader × Array Reply → Array Reply
  | [], state => state.2
  | q :: qs, state =>
    match stepRead grinding state q with
    | none => state.2
    | some next => walkRead grinding qs next

def frameBytes : Frame → List Byte
  | .absorb _ bytes => bytes
  | .nonce _ _ _ => []

/-- Byte runs of the frames after the opening boundary frame. -/
def openingFrames (boundary : Nat) (h : FramedHistory) : List (List Byte) :=
  (h.frames.drop (boundary+1)).map frameBytes

/-- Replies parsed from the opening frames of a history, without query rows or next oracles. -/
def frameReplies (grinding : Fin (cfg).folds.size → Fin 64) (boundary : Nat) (h : FramedHistory) :
    Array Reply :=
  walkRead grinding (WHIRHistory.schedule cfg) (([],openingFrames boundary h),#[])

/-- Ideal completion of the parsed reply at reply position `n`: query rows are the oracle rows at the tape's query indices, a present next oracle is the oracle of the following level. -/
def idealReply (t : Tape cfg) (oracle : Nat → Oracle) (n : Nat) : Reply → Reply
  | .fold m o residual =>
    .fold m (o.map fun _ => oracle (SpongefishCurrentOpeningExperiment.replyLevel cfg n + 1)) residual
  | .query rows m =>
    match (visibleCoordinates cfg)[n]? with
    | some (.query i) =>
      .query (WHIRPhysicalVerifier.atQueries (oracle i.val)
        (WHIRPhysicalVerifier.queryIndices p i (get (.query i) t))) m
    | _ => .query rows m
  | r => r

/-- Every reply whose bytes lie in the opening frames of `h`, in schedule order, decoded as the opening walk decodes it, with query rows read from `oracle` at the indices of `t` and level-end fold replies carrying `oracle (i+1)`. -/
def historyReplies (grinding : Fin (cfg).folds.size → Fin 64) (boundary : Nat) (h : FramedHistory)
    (t : Tape cfg) (oracle : Nat → Oracle) : Array Reply :=
  (frameReplies grinding boundary h).mapIdx fun n r => idealReply t oracle n r

/-! ## Reader states agreeing with an event suffix -/

/-- The reader holds the prover bytes before the next draw and the first `n` later runs. -/
def Rel (n : Nat) (evs : List SourceEvent) (s : Reader) : Prop :=
  s.1 = leadBytes evs ∧ s.2 = (drawRuns evs).take n

theorem rel_read (n : Nat) (kind : WireKind) (v : kind.Value) (rest : List SourceEvent) (s : Reader)
    (rel : Rel n (.prover kind (kind.codec.bytes v) :: rest) s) :
    readKind kind s = some (v,(leadBytes rest,s.2)) ∧ Rel n rest (leadBytes rest,s.2) := by
  obtain ⟨bytes,frames⟩ := rel
  refine ⟨?_,rfl,?_⟩
  · simp [readKind,bytes,leadBytes,Codec.parse_append]
  · simpa [drawRuns] using frames

theorem rel_pair (n : Nat) (xs : Fin 2 → E) (rest : List SourceEvent) (s : Reader)
    (rel : Rel n (.prover (.vector 2) ((WireKind.vector 2).codec.bytes xs) :: rest) s) :
    readPair s = some (⟨xs 0,xs 1⟩,(leadBytes rest,s.2)) ∧ Rel n rest (leadBytes rest,s.2) := by
  obtain ⟨read,next⟩ := rel_read n (.vector 2) xs rest s rel
  exact ⟨by simp [readPair,read],next⟩

theorem rel_draw (n : Nat) (bytes : List Byte) (rest : List SourceEvent) (s : Reader)
    (rel : Rel (n+1) (.verifier bytes :: rest) s) :
    nextFrame s = some (leadBytes rest,(drawRuns rest).take n) ∧
      Rel n rest (leadBytes rest,(drawRuns rest).take n) := by
  obtain ⟨_,frames⟩ := rel
  refine ⟨?_,rfl,rfl⟩
  simp [nextFrame,frames,drawRuns]

theorem rel_hint (n : Nat) (bytes : List Byte) (rest : List SourceEvent) (s : Reader)
    (rel : Rel n (.hint bytes :: rest) s) : Rel n rest s := by
  obtain ⟨lead,frames⟩ := rel
  exact ⟨by simpa [leadBytes] using lead,by simpa [drawRuns] using frames⟩

/-! ## One coordinate of the walk on its own call events -/

def powDraws (grinding : Fin (cfg).folds.size → Fin 64) : Coord p → List (Option (Coord p))
  | .query i => if (grinding i).val = 0 then [] else [none]
  | _ => []

def pcsDraws (q : Coord p) : List (Option (Coord p)) :=
  if PCSBCSRounds.rawWidth q = 0 then [] else [some q]

/-- The opening draws of one coordinate. -/
def drawList (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) : List (Option (Coord p)) :=
  powDraws grinding q ++ pcsDraws q

theorem openingDraws_eq (grinding : Fin (cfg).folds.size → Fin 64) :
    SpongefishCurrentRoundPackets.openingDraws grinding =
      (WHIRHistory.schedule cfg).flatMap (drawList grinding) := by
  rfl

def visibleQ : Coord p → Bool
  | .tail j => isVisibleTail j
  | _ => true

/-- Level-ending folds that carry the next commitment root. -/
def rootFold : Coord p → Bool
  | .fold i j => isLastFold i j && decide (i.val + 1 < (cfg).folds.size)
  | _ => false

def isQuery : Coord p → Bool
  | .query _ => true
  | _ => false

/-- The reply constructor of a coordinate; a fold carries the empty next-oracle placeholder exactly at a root-carrying level end. -/
def Fits : Coord p → Reply → Prop
  | .initial, .initial _ => True
  | .fold i j, .fold _ next _ => next = if rootFold (.fold i j) then some #[] else none
  | .ood _ _, .ood _ => True
  | .query _, .query _ _ => True
  | .tail _, .tail _ => True
  | _, _ => False

def blankRows : Reply → Reply
  | .query _ m => .query #[] m
  | r => r

/-- The authenticated query reply of level `i`: hint, decoded proof, the current level root and the opened rows. -/
def QueryFacts (H : MerkleTransport.Primitive) (decode : Decoder) (lanes : Nat) (i : Fin (cfg).folds.size)
    (col col' : Collected p) : Prop :=
  ∃ (hint : List Byte) (proof : MerkleTransport.PrunedMerklePaths) (root : Digest32)
    (opened : WHIRPhysicalVerifier.Opened) (m : Message E),
    col'.replies = col.replies.push (.query opened.rows m) ∧
    col'.openings = col.openings ++ [⟨i,root,hint,proof,opened⟩] ∧
    col.roots[i.val]? = some root ∧
    decode (WHIRPhysicalVerifier.queryIndices p i (get (.query i) col.tape)) (rowWords lanes i) hint =
      some proof ∧
    HashProgram.eval H (openProgram lanes i root proof (get (.query i) col.tape)) = some opened

theorem pow_block (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) (Ep X : List SourceEvent)
    (col : Collected p) (shape : List.Forall₂ CallEvent (powCalls grinding q) Ep) :
    (∃ pows, powWalk grinding (Ep ++ X) col q = some (X,{col with pows := pows})) ∧
    (verifierBytes Ep).length = (powDraws grinding q).length ∧
    ∀ n s, Rel n (Ep ++ X) s → (powDraws grinding q).length ≤ n →
      ∃ s', powRead grinding s q = some s' ∧ Rel (n - (powDraws grinding q).length) X s' := by
  cases q with
  | query i =>
    by_cases zero : (grinding i).val = 0
    · simp only [powCalls,powSchedule,zero,↓reduceIte] at shape
      cases shape
      refine ⟨⟨col.pows,by simp [powWalk,zero]⟩,by simp [powDraws,zero,verifierBytes],?_⟩
      intro n s rel _
      exact ⟨s,by simp [powRead,zero],by simpa [powDraws,zero] using rel⟩
    · simp only [powCalls,powSchedule,zero,↓reduceIte] at shape
      rcases shape with _ | ⟨⟨bytes,_,rfl⟩,_ | ⟨⟨nonce,rfl⟩,⟨⟩⟩⟩
      refine ⟨⟨_,by simp [powWalk,zero,takeVerifier,takeProver,parse_bytes]; rfl⟩,
        by simp [powDraws,zero,verifierBytes],?_⟩
      intro n s rel enough
      simp only [powDraws,zero,↓reduceIte,List.length_singleton] at enough ⊢
      obtain ⟨m,rfl⟩ : ∃ m, n = m + 1 := ⟨n-1,by omega⟩
      simp only [List.cons_append,List.nil_append] at rel
      obtain ⟨drawn,rel₁⟩ := rel_draw m bytes _ s rel
      obtain ⟨read,rel₂⟩ := rel_read m .nonce nonce X _ rel₁
      simp only [drawRuns] at drawn read rel₂
      exact ⟨(leadBytes X,(drawRuns X).take m),by simp [powRead,zero,drawn,read],by simpa using rel₂⟩
  | initial =>
    cases shape
    exact ⟨⟨col.pows,rfl⟩,rfl,fun n s rel _ => ⟨s,rfl,by simpa [powDraws] using rel⟩⟩
  | fold i j =>
    cases shape
    exact ⟨⟨col.pows,rfl⟩,rfl,fun n s rel _ => ⟨s,rfl,by simpa [powDraws] using rel⟩⟩
  | ood i j =>
    cases shape
    exact ⟨⟨col.pows,rfl⟩,rfl,fun n s rel _ => ⟨s,rfl,by simpa [powDraws] using rel⟩⟩
  | tail j =>
    cases shape
    exact ⟨⟨col.pows,rfl⟩,rfl,fun n s rel _ => ⟨s,rfl,by simpa [powDraws] using rel⟩⟩

theorem draw_block (q : Coord p) (Ed X : List SourceEvent)
    (shape : List.Forall₂ CallEvent (drawCalls q) Ed) :
    drawWalk (Ed ++ X) q = some (X,decodeSample q ((verifierBytes Ed).headD [])) ∧
    (verifierBytes Ed).length = (pcsDraws q).length ∧
    ∀ n s, Rel n (Ed ++ X) s → (pcsDraws q).length ≤ n →
      ∃ s', drawRead s q = some s' ∧ Rel (n - (pcsDraws q).length) X s' := by
  by_cases zero : PCSBCSRounds.rawWidth q = 0
  · simp only [drawCalls,zero,↓reduceIte] at shape
    cases shape
    refine ⟨by simp [drawWalk,zero,verifierBytes],by simp [pcsDraws,zero,verifierBytes],?_⟩
    intro n s rel _
    exact ⟨s,by simp [drawRead,zero],by simpa [pcsDraws,zero] using rel⟩
  · simp only [drawCalls,zero,↓reduceIte] at shape
    rcases shape with _ | ⟨⟨bytes,_,rfl⟩,⟨⟩⟩
    refine ⟨by simp [drawWalk,zero,takeVerifier,verifierBytes],by simp [pcsDraws,zero,verifierBytes],?_⟩
    intro n s rel enough
    simp only [pcsDraws,zero,↓reduceIte,List.length_singleton] at enough ⊢
    obtain ⟨m,rfl⟩ : ∃ m, n = m + 1 := ⟨n-1,by omega⟩
    simp only [List.cons_append,List.nil_append] at rel
    obtain ⟨drawn,rel₁⟩ := rel_draw m bytes X s rel
    exact ⟨(leadBytes X,(drawRuns X).take m),by simp [drawRead,zero,drawn],by simpa using rel₁⟩

/-- Facts about one reply segment of the walk on its call events. -/
def ReplyOutcome (H : MerkleTransport.Primitive) (decode : Decoder) (lanes : Nat) (q : Coord p)
    (Er X : List SourceEvent) (col : Collected p) (st : List SourceEvent × Collected p) : Prop :=
  st.1 = X ∧ verifierBytes Er = [] ∧ st.2.tape = col.tape ∧ st.2.seed = col.seed ∧
  (∀ n s, Rel n (Er ++ X) s →
    ∃ s', replyRead s (col.replies.map blankRows) q = some (s',st.2.replies.map blankRows) ∧
      Rel n X s') ∧
  (visibleQ q = true → ∃ r, st.2.replies = col.replies.push r ∧ Fits q r) ∧
  (visibleQ q = false → st.2.replies = col.replies) ∧
  (rootFold q = false → st.2.roots = col.roots) ∧
  (rootFold q = true → ∃ (xs : Fin 2 → E) (r : Digest32),
    Er = [.prover (.vector 2) ((WireKind.vector 2).codec.bytes xs),.prover .root (WireKind.root.codec.bytes r)] ∧
    st.2.roots = col.roots.push r) ∧
  (isQuery q = false → st.2.openings = col.openings) ∧
  (∀ i, q = .query i → QueryFacts H decode lanes i col st.2)

theorem reply_block (H : MerkleTransport.Primitive) (decode : Decoder) (lanes : Nat) (q : Coord p)
    (Er X : List SourceEvent) (col : Collected p) (st : List SourceEvent × Collected p)
    (shape : List.Forall₂ CallEvent (replyCalls q) Er)
    (ok : HashProgram.eval H (replyWalk decode lanes (Er ++ X) col q) = some st) :
    ReplyOutcome H decode lanes q Er X col st := by
  cases q with
  | initial =>
    simp only [replyCalls] at shape
    rcases shape with _ | ⟨⟨xs,rfl⟩,⟨⟩⟩
    simp only [List.cons_append,List.nil_append] at ok ⊢
    simp [replyWalk,replyPure,HashProgram.eval,takeMessage,takeProver,parse_bytes] at ok
    subst ok
    refine ⟨rfl,by simp [verifierBytes],rfl,rfl,?_,fun _ => ⟨_,rfl,by simp [Fits]⟩,
      fun h => by simp [visibleQ] at h,fun _ => rfl,fun h => by simp [rootFold] at h,fun _ => rfl,
      fun i h => by cases h⟩
    intro n s rel
    obtain ⟨b,f⟩ := s
    obtain ⟨lead,frames⟩ := rel
    simp only at lead frames
    subst lead frames
    refine ⟨(leadBytes X,(drawRuns X).take n),?_,rfl,rfl⟩
    simp [replyRead,readPair,readKind,leadBytes,drawRuns,Codec.parse_append,blankRows]
  | fold i j =>
    by_cases last : isLastFold i j = true
    · by_cases more : i.val + 1 < (cfg).folds.size
      · have root : rootFold (.fold i j) = true := by simp [rootFold,last,more]
        simp only [replyCalls,last,more,↓reduceIte] at shape
        rcases shape with _ | ⟨⟨xs,rfl⟩,_ | ⟨⟨r,rfl⟩,⟨⟩⟩⟩
        simp only [List.cons_append,List.nil_append] at ok ⊢
        simp [replyWalk,replyPure,HashProgram.eval,last,more,takeMessage,takeProver,parse_bytes] at ok
        subst ok
        refine ⟨rfl,by simp [verifierBytes],rfl,rfl,?_,fun _ => ⟨_,rfl,by simp [Fits,root]⟩,
          fun h => by simp [visibleQ] at h,fun h => by simp [root] at h,fun _ => ⟨xs,r,rfl,rfl⟩,
          fun _ => rfl,fun i h => by cases h⟩
        intro n s rel
        obtain ⟨b,f⟩ := s
        obtain ⟨lead,frames⟩ := rel
        simp only at lead frames
        subst lead frames
        refine ⟨(leadBytes X,(drawRuns X).take n),?_,rfl,rfl⟩
        simp [replyRead,readPair,readKind,leadBytes,drawRuns,Codec.parse_append,blankRows,last,more]
      · have root : rootFold (.fold i j) = false := by simp [rootFold,more]
        simp only [replyCalls,last,more,↓reduceIte] at shape
        rcases shape with _ | ⟨⟨xs,rfl⟩,_ | ⟨⟨res,rfl⟩,⟨⟩⟩⟩
        simp only [List.cons_append,List.nil_append] at ok ⊢
        simp [replyWalk,replyPure,HashProgram.eval,last,more,takeMessage,takeProver,parse_bytes] at ok
        subst ok
        refine ⟨rfl,by simp [verifierBytes],rfl,rfl,?_,fun _ => ⟨_,rfl,by simp [Fits,root]⟩,
          fun h => by simp [visibleQ] at h,fun _ => rfl,fun h => by simp [root] at h,
          fun _ => rfl,fun i h => by cases h⟩
        intro n s rel
        obtain ⟨b,f⟩ := s
        obtain ⟨lead,frames⟩ := rel
        simp only at lead frames
        subst lead frames
        refine ⟨(leadBytes X,(drawRuns X).take n),?_,rfl,rfl⟩
        simp [replyRead,readPair,readKind,leadBytes,drawRuns,Codec.parse_append,blankRows,last,more]
    · have root : rootFold (.fold i j) = false := by simp [rootFold,last]
      simp only [replyCalls,last] at shape
      rcases shape with _ | ⟨⟨xs,rfl⟩,⟨⟩⟩
      simp only [List.cons_append,List.nil_append] at ok ⊢
      simp [replyWalk,replyPure,HashProgram.eval,last,takeMessage,takeProver,parse_bytes] at ok
      subst ok
      refine ⟨rfl,by simp [verifierBytes],rfl,rfl,?_,fun _ => ⟨_,rfl,by simp [Fits,root]⟩,
        fun h => by simp [visibleQ] at h,fun _ => rfl,fun h => by simp [root] at h,
        fun _ => rfl,fun i h => by cases h⟩
      intro n s rel
      obtain ⟨b,f⟩ := s
      obtain ⟨lead,frames⟩ := rel
      simp only at lead frames
      subst lead frames
      refine ⟨(leadBytes X,(drawRuns X).take n),?_,rfl,rfl⟩
      simp [replyRead,readPair,readKind,leadBytes,drawRuns,Codec.parse_append,blankRows,last]
  | ood i j =>
    simp only [replyCalls] at shape
    rcases shape with _ | ⟨⟨y,rfl⟩,_ | ⟨⟨xs,rfl⟩,⟨⟩⟩⟩
    simp only [List.cons_append,List.nil_append] at ok ⊢
    simp [replyWalk,replyPure,HashProgram.eval,takeMessage,takeProver,parse_bytes] at ok
    subst ok
    refine ⟨rfl,by simp [verifierBytes],rfl,rfl,?_,fun _ => ⟨_,rfl,by simp [Fits]⟩,
      fun h => by simp [visibleQ] at h,fun _ => rfl,fun h => by simp [rootFold] at h,fun _ => rfl,
      fun i h => by cases h⟩
    intro n s rel
    obtain ⟨b,f⟩ := s
    obtain ⟨lead,frames⟩ := rel
    simp only at lead frames
    subst lead frames
    refine ⟨(leadBytes X,(drawRuns X).take n),?_,rfl,rfl⟩
    simp [replyRead,readPair,readKind,leadBytes,drawRuns,Codec.parse_append,blankRows]
  | query i =>
    simp only [replyCalls] at shape
    rcases shape with _ | ⟨⟨hint,rfl⟩,_ | ⟨⟨xs,rfl⟩,⟨⟩⟩⟩
    simp only [List.cons_append,List.nil_append,replyWalk] at ok ⊢
    cases hd : decode (WHIRPhysicalVerifier.queryIndices p i (get (.query i) col.tape))
        (rowWords lanes i) hint with
    | none => simp [replyQuery,takeHintBytes,hd,HashProgram.eval] at ok
    | some proof =>
      cases hr : col.roots[i.val]? with
      | none => simp [replyQuery,takeHintBytes,hd,hr,HashProgram.eval] at ok
      | some root =>
        simp only [replyQuery,takeHintBytes,hd,hr,HashProgram.eval_map] at ok
        cases ho : HashProgram.eval H (openProgram lanes i root proof (get (.query i) col.tape)) with
        | none => simp [ho] at ok
        | some opened =>
          simp [ho,takeMessage,takeProver,parse_bytes] at ok
          subst ok
          refine ⟨rfl,by simp [verifierBytes],rfl,rfl,?_,fun _ => ⟨_,rfl,by simp [Fits]⟩,
            fun h => by simp [visibleQ] at h,fun _ => rfl,fun h => by simp [rootFold] at h,
            fun h => by simp [isQuery] at h,?_⟩
          · intro n s rel
            obtain ⟨b,f⟩ := s
            obtain ⟨lead,frames⟩ := rel
            simp only at lead frames
            subst lead frames
            refine ⟨(leadBytes X,(drawRuns X).take n),?_,rfl,rfl⟩
            simp [replyRead,readPair,readKind,leadBytes,drawRuns,Codec.parse_append,blankRows]
          · intro i' same
            cases same
            exact ⟨hint,proof,root,opened,_,rfl,rfl,hr,hd,ho⟩
  | tail j =>
    by_cases vis : isVisibleTail j = true
    · simp only [replyCalls,vis,↓reduceIte] at shape
      rcases shape with _ | ⟨⟨xs,rfl⟩,⟨⟩⟩
      simp only [List.cons_append,List.nil_append] at ok ⊢
      simp [replyWalk,replyPure,HashProgram.eval,vis,takeMessage,takeProver,parse_bytes] at ok
      subst ok
      refine ⟨rfl,by simp [verifierBytes],rfl,rfl,?_,fun _ => ⟨_,rfl,by simp [Fits]⟩,
        fun h => by simp [visibleQ,vis] at h,fun _ => rfl,fun h => by simp [rootFold] at h,fun _ => rfl,
        fun i h => by cases h⟩
      intro n s rel
      obtain ⟨b,f⟩ := s
      obtain ⟨lead,frames⟩ := rel
      simp only at lead frames
      subst lead frames
      refine ⟨(leadBytes X,(drawRuns X).take n),?_,rfl,rfl⟩
      simp [replyRead,readPair,readKind,leadBytes,drawRuns,Codec.parse_append,blankRows,vis]
    · simp only [replyCalls,vis] at shape
      cases shape
      simp only [List.nil_append] at ok ⊢
      simp [replyWalk,replyPure,HashProgram.eval,vis] at ok
      subst ok
      refine ⟨rfl,rfl,rfl,rfl,?_,fun h => by simp [visibleQ,vis] at h,fun _ => rfl,fun _ => rfl,
        fun h => by simp [rootFold] at h,fun _ => rfl,fun i h => by cases h⟩
      intro n s rel
      exact ⟨s,by simp [replyRead,vis],rel⟩

theorem forall₂_split {A B : Type} {R : A → B → Prop} :
    ∀ {xs ys : List A} {es : List B}, List.Forall₂ R (xs ++ ys) es →
      ∃ e₁ e₂, es = e₁ ++ e₂ ∧ List.Forall₂ R xs e₁ ∧ List.Forall₂ R ys e₂
  | [], _, es, h => ⟨[],es,rfl,.nil,h⟩
  | _ :: xs, ys, _, .cons head rest => by
    obtain ⟨e₁,e₂,rfl,left,right⟩ := forall₂_split (xs := xs) (ys := ys) rest
    exact ⟨_ :: e₁,e₂,rfl,.cons head left,right⟩

theorem verifierBytes_append (xs ys : List SourceEvent) :
    verifierBytes (xs ++ ys) = verifierBytes xs ++ verifierBytes ys := by
  simp [verifierBytes,List.filterMap_append]

theorem recordSample_tape (col : Collected p) (q : Coord p) (x : PCSBCSRounds.Raw q) :
    (recordSample col q x).tape = set q col.tape (StackWHIRReplay.projectSample q x) := by
  cases q <;> rfl

theorem recordSample_fields (col : Collected p) (q : Coord p) (x : PCSBCSRounds.Raw q) :
    (recordSample col q x).replies = col.replies ∧ (recordSample col q x).roots = col.roots ∧
      (recordSample col q x).openings = col.openings := by
  cases q <;> exact ⟨rfl,rfl,rfl⟩

theorem recordSample_seed (col : Collected p) (pows : List (PowCheck p)) (q : Coord p)
    (x : PCSBCSRounds.Raw q) :
    (recordSample {col with pows := pows} q x).seed = (recordSample col q x).seed := by
  cases q <;> rfl

/-- Bytes of the PCS draw of a coordinate block (empty for a zero-width coordinate). -/
def sampleBytes (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) (evs : List SourceEvent) :
    List Byte :=
  ((verifierBytes evs).drop (powDraws grinding q).length).headD []

/-- Everything one step of the opening walk does on the events of its coordinate. -/
def StepOutcome (H : MerkleTransport.Primitive) (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (lanes : Nat) (q : Coord p) (Eq R : List SourceEvent) (col : Collected p)
    (st : List SourceEvent × Collected p) : Prop :=
  st.1 = R ∧ (verifierBytes Eq).length = (drawList grinding q).length ∧
  (∀ n s, Rel n (Eq ++ R) s → (drawList grinding q).length ≤ n →
    ∃ s', stepRead grinding (s,col.replies.map blankRows) q = some (s',st.2.replies.map blankRows) ∧
      Rel (n - (drawList grinding q).length) R s') ∧
  st.2.tape = set q col.tape (StackWHIRReplay.projectSample q (decodeSample q (sampleBytes grinding q Eq))) ∧
  st.2.seed = (recordSample col q (decodeSample q (sampleBytes grinding q Eq))).seed ∧
  (visibleQ q = true → ∃ r, st.2.replies = col.replies.push r ∧ Fits q r) ∧
  (visibleQ q = false → st.2.replies = col.replies) ∧
  (rootFold q = false → st.2.roots = col.roots) ∧
  (rootFold q = true → ∃ (b : List Byte) (xs : Fin 2 → E) (r : Digest32),
    Eq = [.verifier b,.prover (.vector 2) ((WireKind.vector 2).codec.bytes xs),
      .prover .root (WireKind.root.codec.bytes r)] ∧
    st.2.roots = col.roots.push r) ∧
  (isQuery q = false → st.2.openings = col.openings) ∧
  (∀ i, q = .query i → QueryFacts H decode lanes i {col with tape := st.2.tape} st.2)

theorem step_block (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (q : Coord p) (Eq R : List SourceEvent)
    (col : Collected p) (st : List SourceEvent × Collected p)
    (shape : List.Forall₂ CallEvent (callsOf grinding q) Eq)
    (ok : HashProgram.eval H (stepWalk decode grinding lanes (Eq ++ R,col) q) = some st) :
    StepOutcome H decode grinding lanes q Eq R col st := by
  obtain ⟨Epd,Er,rfl,shapePD,shapeR⟩ := forall₂_split shape
  obtain ⟨Ep,Ed,rfl,shapeP,shapeD⟩ := forall₂_split shapePD
  obtain ⟨⟨pows,powOk⟩,powLen,powRel⟩ := pow_block grinding q Ep (Ed ++ (Er ++ R)) col shapeP
  obtain ⟨drawOk,drawLen,drawRel⟩ := draw_block q Ed (Er ++ R) shapeD
  simp only [List.append_assoc] at ok ⊢
  simp only [stepWalk,powOk,drawOk] at ok
  obtain ⟨rest,vEr,tape,seed,parse,vis,hid,rootsSame,rootsPush,opens,queries⟩ :=
    reply_block H decode lanes q Er R _ st shapeR ok
  obtain ⟨midReplies,midRoots,midOpenings⟩ := recordSample_fields {col with pows := pows} q
    (decodeSample q ((verifierBytes Ed).headD []))
  have sample : sampleBytes grinding q (Ep ++ (Ed ++ Er)) = (verifierBytes Ed).headD [] := by
    simp [sampleBytes,verifierBytes_append,vEr,← powLen]
  have drawLength : (drawList grinding q).length = (powDraws grinding q).length + (pcsDraws q).length := by
    simp [drawList]
  unfold StepOutcome
  rw [sample]
  refine ⟨rest,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [verifierBytes_append,vEr,powLen,drawLen,drawList]
  · intro n s rel enough
    simp only [List.append_assoc] at rel
    obtain ⟨s₁,read₁,rel₁⟩ := powRel n s rel (by omega)
    obtain ⟨s₂,read₂,rel₂⟩ := drawRel _ s₁ rel₁ (by omega)
    obtain ⟨s₃,read₃,rel₃⟩ := parse _ s₂ rel₂
    rw [midReplies] at read₃
    refine ⟨s₃,by simp [stepRead,read₁,read₂,read₃],?_⟩
    rw [drawLength,← Nat.sub_sub]
    exact rel₃
  · rw [tape,recordSample_tape]
  · rw [seed,recordSample_seed]
  · intro visible
    obtain ⟨r,same,fits⟩ := vis visible
    exact ⟨r,by rw [same,midReplies],fits⟩
  · intro hidden
    rw [hid hidden,midReplies]
  · intro plain
    rw [rootsSame plain,midRoots]
  · intro root
    obtain ⟨xs,r,rfl,pushed⟩ := rootsPush root
    cases q with
    | fold i j =>
      simp only [powCalls] at shapeP
      cases shapeP
      have width : PCSBCSRounds.rawWidth (CausalProbability.Coordinate.fold (c := cfg) i j) = 1 := rfl
      simp only [drawCalls,width,one_ne_zero,↓reduceIte] at shapeD
      rcases shapeD with _ | ⟨⟨b,_,rfl⟩,⟨⟩⟩
      exact ⟨b,xs,r,rfl,by rw [pushed,midRoots]⟩
    | initial => simp [rootFold] at root
    | ood i j => simp [rootFold] at root
    | query i => simp [rootFold] at root
    | tail j => simp [rootFold] at root
  · intro plain
    rw [opens plain,midOpenings]
  · intro i same
    subst same
    obtain ⟨hint,proof,root,opened,m,r₁,r₂,r₃,r₄,r₅⟩ := queries i rfl
    rw [midReplies] at r₁
    rw [midOpenings] at r₂
    rw [midRoots] at r₃
    rw [recordSample_tape] at r₄ r₅
    rw [tape,recordSample_tape]
    exact ⟨hint,proof,root,opened,m,r₁,r₂,r₃,r₄,r₅⟩

/-! ## The walk over consecutive coordinate blocks -/

/-- One event block per coordinate, each of the coordinate's call shape. -/
def Blocks (grinding : Fin (cfg).folds.size → Fin 64) (xs : List (Coord p))
    (bx : List (List SourceEvent)) : Prop :=
  List.Forall₂ (fun q b => List.Forall₂ CallEvent (callsOf grinding q) b) xs bx

theorem blocks_of (grinding : Fin (cfg).folds.size → Fin 64) :
    ∀ (xs : List (Coord p)) (E : List SourceEvent),
      List.Forall₂ CallEvent (xs.flatMap (callsOf grinding)) E →
      ∃ bx, E = bx.flatten ∧ Blocks grinding xs bx
  | [], E, h => by
    rw [List.flatMap_nil] at h
    cases h
    exact ⟨[],rfl,.nil⟩
  | q :: xs, E, h => by
    rw [List.flatMap_cons] at h
    obtain ⟨e₁,e₂,rfl,first,rest⟩ := forall₂_split h
    obtain ⟨bx,rfl,blocks⟩ := blocks_of grinding xs e₂ rest
    exact ⟨e₁ :: bx,by simp,.cons first blocks⟩

theorem walk_cons_eval (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (q : Coord p) (qs : List (Coord p))
    (st : List SourceEvent × Collected p) :
    HashProgram.eval H (walkFrom decode grinding lanes (q :: qs) st) =
      (HashProgram.eval H (stepWalk decode grinding lanes st q)).bind
        (fun next => HashProgram.eval H (walkFrom decode grinding lanes qs next)) := by
  rw [walkFrom,HashProgram.eval_bind]
  cases HashProgram.eval H (stepWalk decode grinding lanes st q) <;> rfl

theorem push_append_toArray {A : Type} (a : Array A) (r : A) (l : List A) :
    a.push r ++ l.toArray = a ++ (r :: l).toArray := by
  apply Array.ext'
  simp

theorem recordSample_seed_ne (col : Collected p) (q : Coord p) (x : PCSBCSRounds.Raw q)
    (other : q ≠ .initial) : (recordSample col q x).seed = col.seed := by
  cases q with
  | initial => exact (other rfl).elim
  | fold i j => rfl
  | ood i j => rfl
  | query i => rfl
  | tail j => rfl

/-- What the walk over a run of coordinate blocks preserves and produces. -/
def WalkOutcome (grinding : Fin (cfg).folds.size → Fin 64) (xs : List (Coord p))
    (bx : List (List SourceEvent)) (R : List SourceEvent) (col : Collected p)
    (final : List SourceEvent × Collected p) : Prop :=
  final.1 = R ∧
  (verifierBytes bx.flatten).length = (xs.flatMap (drawList grinding)).length ∧
  (∀ ys n s, Rel n (bx.flatten ++ R) s → (xs.flatMap (drawList grinding)).length ≤ n →
    ∃ s', walkRead grinding (xs ++ ys) (s,col.replies.map blankRows) =
        walkRead grinding ys (s',final.2.replies.map blankRows) ∧
      Rel (n - (xs.flatMap (drawList grinding)).length) R s') ∧
  (∃ rs : List Reply, final.2.replies = col.replies ++ rs.toArray ∧
    List.Forall₂ Fits (xs.filter visibleQ) rs) ∧
  (∃ rts : List Digest32, final.2.roots = col.roots ++ rts.toArray ∧
    rts.length = (xs.filter rootFold).length) ∧
  (∀ r, r ∉ xs → get r final.2.tape = get r col.tape) ∧
  ((.initial : Coord p) ∉ xs → final.2.seed = col.seed) ∧
  (∀ o ∈ col.openings, o ∈ final.2.openings)

theorem walk_run (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    ∀ (xs : List (Coord p)) (bx : List (List SourceEvent)) (R : List SourceEvent) (col : Collected p)
      (final : List SourceEvent × Collected p), Blocks grinding xs bx →
      HashProgram.eval H (walkFrom decode grinding lanes xs (bx.flatten ++ R,col)) = some final →
      WalkOutcome grinding xs bx R col final
  | [], bx, R, col, final, blocks, ok => by
    cases blocks
    simp only [walkFrom,HashProgram.eval,Option.some.injEq,List.flatten_nil,List.nil_append] at ok
    subst ok
    refine ⟨rfl,rfl,?_,⟨[],by simp,.nil⟩,⟨[],by simp,rfl⟩,fun _ _ => rfl,fun _ => rfl,fun _ h => h⟩
    intro ys n s rel _
    exact ⟨s,rfl,by simpa using rel⟩
  | q :: xs, _, R, col, final, blocks, ok => by
    rcases blocks with _ | @⟨_,b,_,bx,shape,blocks⟩
    simp only [List.flatten_cons,List.append_assoc] at ok
    rw [walk_cons_eval] at ok
    obtain ⟨next,stepOk,restOk⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨rest,vLen,parse,tape,seed,vis,hid,rootsSame,rootsPush,opens,queries⟩ :=
      step_block H decode grinding lanes q b (bx.flatten ++ R) col next shape stepOk
    obtain ⟨n₁,n₂⟩ := next
    simp only at rest
    subst rest
    obtain ⟨fin,vRest,parseRest,⟨rs,repl,fits⟩,⟨rts,rootsEq,rtsLen⟩,tapeRest,seedRest,opensRest⟩ :=
      walk_run H decode grinding lanes xs bx R n₂ final blocks restOk
    refine ⟨fin,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [verifierBytes_append,vLen,vRest]
    · intro ys n s rel enough
      simp only [List.flatten_cons,List.append_assoc] at rel
      simp only [List.flatMap_cons,List.length_append] at enough ⊢
      obtain ⟨s₁,read₁,rel₁⟩ := parse n s rel (by omega)
      obtain ⟨s₂,eq₂,rel₂⟩ := parseRest ys _ s₁ rel₁ (by omega)
      refine ⟨s₂,?_,by rw [Nat.sub_add_eq]; exact rel₂⟩
      simp only [List.cons_append,walkRead,read₁]
      exact eq₂
    · by_cases v : visibleQ q = true
      · obtain ⟨r,push,fit⟩ := vis v
        refine ⟨r :: rs,by rw [repl,push,push_append_toArray],?_⟩
        rw [List.filter_cons_of_pos v]
        exact .cons fit fits
      · refine ⟨rs,by rw [repl,hid (by simpa using v)],?_⟩
        rw [List.filter_cons_of_neg v]
        exact fits
    · by_cases v : rootFold q = true
      · obtain ⟨_,_,r,_,push⟩ := rootsPush v
        refine ⟨r :: rts,by rw [rootsEq,push,push_append_toArray],?_⟩
        rw [List.filter_cons_of_pos v]
        simp [rtsLen]
      · refine ⟨rts,by rw [rootsEq,rootsSame (by simpa using v)],?_⟩
        rw [List.filter_cons_of_neg v]
        exact rtsLen
    · intro r notin
      simp only [List.mem_cons,not_or] at notin
      rw [tapeRest r notin.2,tape,get_set_ne _ _ _ _ notin.1]
    · intro notin
      simp only [List.mem_cons,not_or] at notin
      rw [seedRest notin.2,seed,recordSample_seed_ne _ _ _ (Ne.symm notin.1)]
    · intro o member
      apply opensRest
      cases hq : isQuery q with
      | false => rw [opens hq]; exact member
      | true =>
        cases q with
        | query i =>
          obtain ⟨_,_,_,_,_,_,pushed,_⟩ := queries i rfl
          rw [pushed]
          exact List.mem_append_left _ member
        | initial => simp [isQuery] at hq
        | fold i j => simp [isQuery] at hq
        | ood i j => simp [isQuery] at hq
        | tail j => simp [isQuery] at hq

theorem walk_split (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    ∀ (xs ys : List (Coord p)) (bx : List (List SourceEvent)) (R : List SourceEvent) (col : Collected p)
      (final : List SourceEvent × Collected p), Blocks grinding xs bx →
      HashProgram.eval H (walkFrom decode grinding lanes (xs ++ ys) (bx.flatten ++ R,col)) = some final →
      ∃ mid, HashProgram.eval H (walkFrom decode grinding lanes xs (bx.flatten ++ R,col)) = some (R,mid) ∧
        HashProgram.eval H (walkFrom decode grinding lanes ys (R,mid)) = some final
  | [], ys, bx, R, col, final, blocks, ok => by
    cases blocks
    exact ⟨col,by simp [walkFrom,HashProgram.eval],by simpa using ok⟩
  | q :: xs, ys, _, R, col, final, blocks, ok => by
    rcases blocks with _ | @⟨_,b,_,bx,shape,blocks⟩
    simp only [List.flatten_cons,List.append_assoc,List.cons_append] at ok ⊢
    rw [walk_cons_eval] at ok
    obtain ⟨next,stepOk,restOk⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨rest,_⟩ := step_block H decode grinding lanes q b (bx.flatten ++ R) col next shape stepOk
    obtain ⟨n₁,n₂⟩ := next
    simp only at rest
    subst rest
    obtain ⟨mid,first,second⟩ := walk_split H decode grinding lanes xs ys bx R n₂ final blocks restOk
    refine ⟨mid,?_,second⟩
    rw [walk_cons_eval,stepOk]
    exact first

/-! ## Schedule positions of opening draws -/

theorem powDraws_none (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) (x : Option (Coord p))
    (member : x ∈ powDraws grinding q) : x = none := by
  cases q with
  | query i =>
    simp only [powDraws] at member
    split_ifs at member <;> simp_all
  | initial => simp [powDraws] at member
  | fold i j => simp [powDraws] at member
  | ood i j => simp [powDraws] at member
  | tail j => simp [powDraws] at member

/-- The coordinate of an opening draw, its schedule split and its draw index. -/
theorem flatMap_index (grinding : Fin (cfg).folds.size → Fin 64) :
    ∀ (xs : List (Coord p)), xs.Nodup → ∀ (j : Nat) (q : Coord p),
      (xs.flatMap (drawList grinding))[j]? = some (some q) →
      ∃ pre post, xs = pre ++ q :: post ∧ q ∉ pre ∧
        j = (pre.flatMap (drawList grinding)).length + (powDraws grinding q).length
  | [], _, j, q, found => by simp at found
  | x :: xs, nd, j, q, found => by
    rw [List.flatMap_cons] at found
    by_cases within : j < (drawList grinding x).length
    · rw [List.getElem?_append_left within] at found
      unfold drawList at found within
      by_cases inPow : j < (powDraws grinding x).length
      · rw [List.getElem?_append_left inPow] at found
        have := powDraws_none grinding x _ (List.mem_of_getElem? found)
        simp at this
      · rw [List.getElem?_append_right (by omega)] at found
        unfold pcsDraws at found
        split_ifs at found with zero
        · simp at found
        · have idx : j - (powDraws grinding x).length = 0 := by
            have := (List.getElem?_eq_some_iff.mp found).1
            simp only [List.length_singleton] at this
            omega
          rw [idx] at found
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst found
          exact ⟨[],xs,rfl,by simp,by simp; omega⟩
    · rw [List.getElem?_append_right (by omega)] at found
      obtain ⟨pre,post,split,notin,index⟩ :=
        flatMap_index grinding xs (List.nodup_cons.mp nd).2 _ q found
      have ne : x ≠ q := by
        intro same
        subst same
        exact (List.nodup_cons.mp nd).1 (by rw [split]; simp)
      refine ⟨x :: pre,post,by rw [split]; rfl,by simp [Ne.symm ne,notin],?_⟩
      simp only [List.flatMap_cons,List.length_append]
      omega

theorem split_position (q : Coord p) (pre post : List (Coord p))
    (split : WHIRHistory.schedule cfg = pre ++ q :: post) (notin : q ∉ pre) :
    position q = pre.length := by
  rw [← WHIRHistory.schedule_idxOf,split,List.idxOf_append_of_notMem notin]
  simp

theorem split_visible (q : Coord p) (pre post : List (Coord p))
    (split : WHIRHistory.schedule cfg = pre ++ q :: post) :
    ∀ r ∈ pre, r ∈ visibleCoordinates cfg := by
  intro r member
  have hidden : (WHIRHistory.hiddenTail cfg).length ≤ 1 := by
    unfold WHIRHistory.hiddenTail
    split <;> simp
  have total := congrArg List.length split
  simp only [WHIRHistory.schedule,List.length_append,List.length_cons] at total
  have taken := congrArg (List.take pre.length) split
  rw [WHIRHistory.schedule,List.take_append_of_le_length (by omega),List.take_left] at taken
  rw [← taken] at member
  exact List.mem_of_mem_take member

theorem visibleQ_of_mem (r : Coord p) (member : r ∈ visibleCoordinates cfg) : visibleQ r = true := by
  cases r with
  | tail j =>
    simp only [visibleQ,isVisibleTail,decide_eq_true_eq]
    simp only [CausalProbability.visibleCoordinates,List.mem_append,List.mem_cons,
      List.mem_flatMap,List.mem_ofFn,List.not_mem_nil] at member
    rcases member with ((same | none) | ⟨i,_,inLevel⟩) | ⟨k,same⟩
    · cases same
    · exact none.elim
    · unfold CausalProbability.levelCoordinates at inLevel
      split at inLevel
      · simp [List.mem_ofFn] at inLevel
      · cases inLevel
    · cases same
      have := k.isLt
      simp only
      omega
  | initial => rfl
  | fold i j => rfl
  | ood i j => rfl
  | query i => rfl

theorem schedule_filter : (WHIRHistory.schedule cfg).filter visibleQ = visibleCoordinates cfg := by
  rw [WHIRHistory.schedule,List.filter_append,List.filter_eq_self.mpr (fun r m => visibleQ_of_mem r m)]
  unfold WHIRHistory.hiddenTail
  split
  · rename_i pos
    have stop : ¬ ((cfg).logN - (cfg).folds.toList.sum - 1 + 1 < (cfg).logN - (cfg).folds.toList.sum) := by
      omega
    simp only [List.filter_cons,List.filter_nil,visibleQ,isVisibleTail,decide_eq_false stop,
      Bool.false_eq_true,↓reduceIte,List.append_nil]
  · simp

theorem push_eq_append {A : Type} (a : Array A) (r : A) : a.push r = a ++ #[r] := by
  apply Array.ext'
  simp

theorem replyRead_prefix (s : Reader) (rs : Array Reply) (q : Coord p) (next : Reader × Array Reply)
    (ok : replyRead s rs q = some next) : ∃ extra : Array Reply, next.2 = rs ++ extra := by
  cases q with
  | initial =>
    simp only [replyRead] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    exact ⟨_,push_eq_append _ _⟩
  | fold i j =>
    simp only [replyRead] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    split_ifs at ok
    · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok
      exact ⟨_,push_eq_append _ _⟩
    · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok
      exact ⟨_,push_eq_append _ _⟩
    · cases ok
      exact ⟨_,push_eq_append _ _⟩
  | ood i j =>
    simp only [replyRead] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    exact ⟨_,push_eq_append _ _⟩
  | query i =>
    simp only [replyRead] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    exact ⟨_,push_eq_append _ _⟩
  | tail j =>
    simp only [replyRead] at ok
    split_ifs at ok
    · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok
      exact ⟨_,push_eq_append _ _⟩
    · cases ok
      exact ⟨#[],by simp⟩

theorem walkRead_prefix (grinding : Fin (cfg).folds.size → Fin 64) :
    ∀ (qs : List (Coord p)) (s : Reader) (rs : Array Reply),
      ∃ extra : Array Reply, walkRead grinding qs (s,rs) = rs ++ extra
  | [], s, rs => ⟨#[],by simp [walkRead]⟩
  | q :: qs, s, rs => by
    simp only [walkRead]
    cases ok : stepRead grinding (s,rs) q with
    | none => exact ⟨#[],by simp⟩
    | some next =>
      simp only
      unfold stepRead at ok
      obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      obtain ⟨extra,same⟩ := replyRead_prefix _ _ q next ok
      obtain ⟨more,rest⟩ := walkRead_prefix grinding qs next.1 next.2
      refine ⟨extra ++ more,?_⟩
      rw [rest,same,Array.append_assoc]

/-! ## Reply positions and exactness -/

theorem leadBytes_opening (grinding : Fin (cfg).folds.size → Fin 64) (E : List SourceEvent)
    (calls : List.Forall₂ CallEvent (openingCalls grinding) E) : leadBytes E = [] := by
  obtain ⟨rest,head⟩ := openingCalls_head grinding (p := p)
  rw [head] at calls
  rcases calls with _ | ⟨⟨bytes,_,rfl⟩,_⟩
  rfl

/-- A successful walk on the opening call events is a walk over one block per scheduled coordinate. -/
theorem walk_whole (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col) :
    ∃ bx fin, E = bx.flatten ∧ Blocks grinding (WHIRHistory.schedule cfg) bx ∧
      HashProgram.eval H (walkFrom decode grinding lanes (WHIRHistory.schedule cfg)
        (bx.flatten ++ [],Collected.start root0)) = some (fin,col) := by
  obtain ⟨bx,rfl,blocks⟩ := blocks_of grinding (WHIRHistory.schedule cfg) E calls
  unfold walk at walked
  rw [HashProgram.eval_map] at walked
  obtain ⟨⟨fin,col'⟩,ev,same⟩ := Option.map_eq_some_iff.mp walked
  cases same
  exact ⟨bx,fin,rfl,blocks,by simpa using ev⟩

/-- Reply-position invariant: the walk pushes exactly one reply per visible coordinate, in schedule order, of the coordinate's constructor. -/
theorem reply_positions (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col) :
    List.Forall₂ Fits (visibleCoordinates cfg) col.replies.toList := by
  obtain ⟨bx,fin,rfl,blocks,ev⟩ := walk_whole H decode grinding lanes root0 E col calls walked
  obtain ⟨_,_,_,⟨rs,repl,fits⟩,_⟩ := walk_run H decode grinding lanes _ bx [] _ _ blocks ev
  rw [schedule_filter] at fits
  simp only at repl
  rw [repl]
  simpa [Collected.start] using fits

theorem reply_at (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (r : Coord p) (visible : r ∈ visibleCoordinates cfg) :
    ∃ reply, col.replies[position r]? = some reply ∧ Fits r reply := by
  have fits := reply_positions H decode grinding lanes root0 E col calls walked
  obtain ⟨reply,found,fit⟩ := forall₂_getElem? fits (position r) r (List.getElem?_idxOf visible)
  exact ⟨reply,by simpa using found,fit⟩

theorem forall₂_getElem?_right {B C : Type} {R : B → C → Prop} {xs : List B} {ys : List C}
    (h : List.Forall₂ R xs ys) (k : Nat) (b : C) (found : ys[k]? = some b) :
    ∃ a, xs[k]? = some a ∧ R a b := by
  have flipped : List.Forall₂ (flip R) ys xs := h.flip
  obtain ⟨a,at',rel⟩ := forall₂_getElem? flipped k b found
  exact ⟨a,at',rel⟩

theorem bang_of {A : Type} [Inhabited A] (xs : Array A) (n : Nat) (a : A) (found : xs[n]? = some a) :
    xs[n]! = a := by
  rw [getElem!_def,found]

theorem position_at (n : Nat) (c : Coord p) (atN : (visibleCoordinates cfg)[n]? = some c) :
    position c = n := by
  have within := List.getElem?_eq_some_iff.mp atN
  unfold position
  rw [← within.2]
  exact (WHIRHistory.visibleCoordinates_nodup cfg).idxOf_getElem n within.1

theorem idealReply_restore (t : Tape cfg) (root : BaseOracle) (next next' : Nat → Oracle) (col : Collected p)
    (n : Nat) (r : Reply) (c : Coord p) (atN : (visibleCoordinates cfg)[n]? = some c) (fits : Fits c r)
    (stored : col.replies[n]? = some r)
    (rows : SpongefishCurrentOpeningExperiment.RowsAuthenticated col.tape col.replies root next)
    (agree : ∀ i : Fin (cfg).folds.size, position (.query i : Coord p) = n →
      get (.query i) t = get (.query i) col.tape)
    (levels : ∀ i : Nat, ((∃ (i' : Fin (cfg).folds.size) (k : Fin (cfg).folds[i'.val]!),
        isLastFold i' k = true ∧ i'.val + 1 < (cfg).folds.size ∧ i = i'.val + 1 ∧ c = .fold i' k) ∨
      (∃ i' : Fin (cfg).folds.size, 0 < i'.val ∧ i = i'.val ∧ c = .query i')) → next' i = next i) :
    idealReply t (SpongefishCurrentOpeningExperiment.levelOracle root next') n (blankRows r) =
      SpongefishCurrentOpeningExperiment.restoreReply cfg next n r := by
  cases r with
  | initial m => rfl
  | fold m o residual =>
    cases o with
    | none => rfl
    | some x =>
      cases c with
      | fold i' k =>
        have root : rootFold (.fold i' k : Coord p) = true := by
          by_contra hr
          simp [Fits,hr] at fits
        simp only [rootFold,Bool.and_eq_true,decide_eq_true_eq] at root
        have level : SpongefishCurrentOpeningExperiment.replyLevel cfg n = i'.val := by
          simp [SpongefishCurrentOpeningExperiment.replyLevel,atN]
        have same := levels (i'.val + 1) (.inl ⟨i',k,root.1,root.2,rfl,rfl⟩)
        simp [blankRows,idealReply,SpongefishCurrentOpeningExperiment.restoreReply,
          SpongefishCurrentOpeningExperiment.levelOracle,level,same]
      | initial => simp [Fits] at fits
      | ood i j => simp [Fits] at fits
      | query i => simp [Fits] at fits
      | tail j => simp [Fits] at fits
  | ood claim => rfl
  | tail m => rfl
  | query rowsR m =>
    cases c with
    | query i =>
      have place : position (.query i : Coord p) = n := position_at n _ atN
      have authenticated := rows i
      rw [place,bang_of _ _ _ stored] at authenticated
      simp only [rowsField] at authenticated
      have oracleEq : SpongefishCurrentOpeningExperiment.levelOracle root next' i.val =
          SpongefishCurrentOpeningExperiment.levelOracle root next i.val := by
        unfold SpongefishCurrentOpeningExperiment.levelOracle
        split_ifs with zero
        · rfl
        · exact levels i.val (.inr ⟨i,by omega,rfl,rfl⟩)
      simp only [blankRows,idealReply,atN,SpongefishCurrentOpeningExperiment.restoreReply,oracleEq,
        authenticated,agree i place]
    | initial => simp [Fits] at fits
    | fold i j => simp [Fits] at fits
    | ood i j => simp [Fits] at fits
    | tail j => simp [Fits] at fits

/-- Exactness of the history parser with per-level oracles: on the key history of the `j`-th opening draw (coordinate `q`), the replies parsed from the opening frames and completed with `levelOracle root next'` agree, before position `q`, with the walk's replies restored with `next`, as soon as `next'` and `next` agree on every level used by a reply before `q` (the level after a root-carrying fold, and the level of a query with positive level). -/
theorem replies_exact_local (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (j : Nat) (q : Coord p)
    (found : (SpongefishCurrentRoundPackets.openingDraws grinding)[j]? = some (some q))
    (boundary : Nat) (h : FramedHistory) (frames : openingFrames boundary h = (drawRuns E).take j)
    (root : BaseOracle) (next : Nat → Oracle)
    (rows : SpongefishCurrentOpeningExperiment.RowsAuthenticated col.tape col.replies root next)
    (t : Tape cfg) (agree : ∀ r : Coord p, position r < position q → get r t = get r col.tape)
    (next' : Nat → Oracle)
    (levels : ∀ i : Nat, ((∃ (i' : Fin (cfg).folds.size) (k : Fin (cfg).folds[i'.val]!),
        SpongefishCurrentOpeningAcceptance.isLastFold i' k = true ∧ i'.val + 1 < (cfg).folds.size ∧
          i = i'.val + 1 ∧ position (.fold i' k : Coord p) < position q) ∨
      (∃ i' : Fin (cfg).folds.size, 0 < i'.val ∧ i = i'.val ∧ position (.query i' : Coord p) < position q)) →
      next' i = next i) :
    PCSRoundByRoundTranscriptState.priorAnswers
        (historyReplies grinding boundary h t (SpongefishCurrentOpeningExperiment.levelOracle root next'))
        (position q) =
      PCSRoundByRoundTranscriptState.priorAnswers
        (SpongefishCurrentOpeningExperiment.restoredReplies col next) (position q) := by
  have lead := leadBytes_opening grinding E calls
  have fitsAll := reply_positions H decode grinding lanes root0 E col calls walked
  obtain ⟨bx,fin,rfl,blocks,ev⟩ := walk_whole H decode grinding lanes root0 E col calls walked
  obtain ⟨pre,post,split,notin,index⟩ := flatMap_index grinding (WHIRHistory.schedule cfg)
    (WHIRHistory.schedule_nodup cfg) j q (by rw [← openingDraws_eq]; exact found)
  have place := split_position q pre post split notin
  rw [split] at blocks ev
  obtain ⟨bpre,brest,rfl,bp,br⟩ := forall₂_split blocks
  rw [List.flatten_append,List.append_nil] at ev
  obtain ⟨mid,first,second⟩ := walk_split H decode grinding lanes pre (q :: post) bpre brest.flatten
    (Collected.start root0) (fin,col) bp (by simpa using ev)
  obtain ⟨_,_,parse,⟨rs,repl,fits⟩,_⟩ := walk_run H decode grinding lanes pre bpre brest.flatten
    (Collected.start root0) (brest.flatten,mid) bp first
  obtain ⟨_,_,_,⟨rs₂,repl₂,_⟩,_⟩ := walk_run H decode grinding lanes (q :: post) brest [] mid (fin,col) br
    (by simpa using second)
  simp only at repl repl₂
  have allVisible : pre.filter visibleQ = pre :=
    List.filter_eq_self.mpr (fun r m => visibleQ_of_mem r (split_visible q pre post split r m))
  rw [allVisible] at fits
  have midSize : mid.replies.size = position q := by
    rw [repl,place,fits.length_eq]
    simp [Collected.start]
  obtain ⟨s',reads,_⟩ := parse (q :: post) j ([],openingFrames boundary h)
    ⟨by rw [List.flatten_append] at lead; exact lead.symm,by rw [frames,List.flatten_append]⟩
    (by omega)
  have start : (Collected.start (p := p) root0).replies.map blankRows = #[] := by simp [Collected.start]
  rw [start,← split] at reads
  obtain ⟨extra,tail⟩ := walkRead_prefix grinding (q :: post) s' (mid.replies.map blankRows)
  have parsed : frameReplies grinding boundary h = mid.replies.map blankRows ++ extra := by
    rw [frameReplies,reads,tail]
  unfold PCSRoundByRoundTranscriptState.priorAnswers
  congr 1
  funext n
  have small : n.val < mid.replies.size := by omega
  have stored : col.replies[n.val]? = mid.replies[n.val]? := by
    rw [repl₂,Array.getElem?_append_left small]
  obtain ⟨r,midAt⟩ : ∃ r, mid.replies[n.val]? = some r := ⟨_,getElem?_pos mid.replies n.val small⟩
  rw [midAt] at stored
  obtain ⟨c,atN,fit⟩ := forall₂_getElem?_right fitsAll n.val r (by simpa using stored)
  rw [getElem!_def,getElem!_def,historyReplies,Array.getElem?_mapIdx,parsed,
    Array.getElem?_append_left (by simpa using small),Array.getElem?_map,midAt,
    SpongefishCurrentOpeningExperiment.restoredReplies_getElem?,stored]
  simp only [Option.map_some]
  have placeC := position_at n.val c atN
  exact idealReply_restore t root next next' col n.val r c atN fit stored rows
    (fun i same => agree _ (by rw [same]; omega))
    (fun i used => levels i (by
      rcases used with ⟨i',k,last,more,rfl,rfl⟩ | ⟨i',pos,rfl,rfl⟩
      · exact .inl ⟨i',k,last,more,rfl,by omega⟩
      · exact .inr ⟨i',pos,rfl,by omega⟩))

/-- Exactness of the history parser: on the key history of the `j`-th opening draw (coordinate `q`), the replies parsed from the opening frames and completed with the ideal oracles agree, before position `q`, with the walk's replies with restored next oracles. -/
theorem replies_exact (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (j : Nat) (q : Coord p)
    (found : (SpongefishCurrentRoundPackets.openingDraws grinding)[j]? = some (some q))
    (boundary : Nat) (h : FramedHistory) (frames : openingFrames boundary h = (drawRuns E).take j)
    (root : BaseOracle) (next : Nat → Oracle)
    (rows : SpongefishCurrentOpeningExperiment.RowsAuthenticated col.tape col.replies root next)
    (t : Tape cfg) (agree : ∀ r : Coord p, position r < position q → get r t = get r col.tape) :
    PCSRoundByRoundTranscriptState.priorAnswers
        (historyReplies grinding boundary h t (SpongefishCurrentOpeningExperiment.levelOracle root next))
        (position q) =
      PCSRoundByRoundTranscriptState.priorAnswers
        (SpongefishCurrentOpeningExperiment.restoredReplies col next) (position q) :=
  replies_exact_local H decode grinding lanes root0 E col calls walked j q found boundary h frames root next
    rows t agree next (fun _ _ => rfl)

/-! ## Frames of the replayed opening -/

/-- The pending absorb state after a list of events: reads bind, positive draws close the run, hints absorb nothing. -/
def applyEvents : Pending → List SourceEvent → Pending
  | m, [] => m
  | m, .prover _ bytes :: rest => applyEvents (SpongefishPCSRoundFrames.bind m bytes) rest
  | m, .verifier bytes :: rest => applyEvents (SpongefishPCSRoundFrames.draw m bytes.length) rest
  | m, .hint _ :: rest => applyEvents m rest
  | m, .publicBytes _ :: rest => applyEvents m rest

/-- Runs closed by the draws of an event list, starting from the pending run `run`. -/
def chunks (run : List Byte) : List SourceEvent → List (List Byte)
  | [] => []
  | .prover _ bytes :: rest => chunks (run ++ bytes) rest
  | .verifier bytes :: rest =>
    if bytes.length = 0 then chunks run rest else if run = [] then chunks [] rest else run :: chunks [] rest
  | .hint _ :: rest => chunks run rest
  | .publicBytes _ :: rest => chunks run rest

def byteRun : ByteFrame → List Byte
  | .absorb _ bytes => bytes

theorem applyEvents_domain : ∀ (m : Pending) (E : List SourceEvent), (applyEvents m E).domain = m.domain
  | m, [] => rfl
  | m, .prover _ bytes :: rest => by rw [applyEvents,applyEvents_domain,bind_domain]
  | m, .verifier bytes :: rest => by
    rw [applyEvents,applyEvents_domain]
    by_cases zero : bytes.length = 0
    · simp [SpongefishPCSRoundFrames.draw,zero]
    · exact (draw_facts m _ zero).2.2
  | m, .hint _ :: rest => by rw [applyEvents,applyEvents_domain]
  | m, .publicBytes _ :: rest => by rw [applyEvents,applyEvents_domain]

theorem bind_run (m : Pending) (bytes : List Byte) :
    (SpongefishPCSRoundFrames.bind m bytes).run = m.run ++ bytes := by
  by_cases empty : bytes = [] <;> simp [SpongefishPCSRoundFrames.bind,empty]

theorem apply_frames : ∀ (m : Pending) (E : List SourceEvent),
    (applyEvents m E).frames.map byteRun = m.frames.map byteRun ++ chunks m.run E
  | m, [] => by simp [applyEvents,chunks]
  | m, .prover _ bytes :: rest => by
    rw [applyEvents,apply_frames,bind_frames,bind_run]
    rfl
  | m, .verifier bytes :: rest => by
    rw [applyEvents,apply_frames]
    by_cases zero : bytes.length = 0
    · simp [SpongefishPCSRoundFrames.draw,zero,chunks]
    · by_cases empty : m.run = []
      · simp [SpongefishPCSRoundFrames.draw,zero,chunks,close,empty]
      · simp [SpongefishPCSRoundFrames.draw,zero,chunks,close,empty,byteRun]
  | m, .hint _ :: rest => by
    rw [applyEvents,apply_frames]
    rfl
  | m, .publicBytes _ :: rest => by
    rw [applyEvents,apply_frames]
    rfl

theorem chunks_length_le : ∀ (r : List Byte) (E : List SourceEvent),
    (chunks r E).length ≤ (drawRuns E).length
  | r, [] => by simp [chunks]
  | r, .prover _ bytes :: rest => by
    simpa [chunks,drawRuns] using chunks_length_le (r ++ bytes) rest
  | r, .verifier bytes :: rest => by
    have one := chunks_length_le r rest
    have two := chunks_length_le [] rest
    simp only [chunks,drawRuns,List.length_cons]
    split_ifs <;> simp <;> omega
  | r, .hint _ :: rest => by
    simpa [chunks,drawRuns] using chunks_length_le r rest
  | r, .publicBytes _ :: rest => by
    simpa [chunks,drawRuns] using chunks_length_le r rest

/-- When every draw closes a nonempty run, the closed runs are the starting run with the lead bytes, then every run after a draw but the last. -/
theorem chunks_full : ∀ (r : List Byte) (E : List SourceEvent),
    (drawRuns E).length ≤ (chunks r E).length →
      chunks r E = ((r ++ leadBytes E) :: drawRuns E).dropLast
  | r, [], _ => by simp [chunks,drawRuns]
  | r, .prover _ bytes :: rest, full => by
    simp only [chunks,drawRuns,leadBytes] at full ⊢
    rw [chunks_full (r ++ bytes) rest full,List.append_assoc]
  | r, .verifier bytes :: rest, full => by
    have bound := chunks_length_le [] rest
    have bound' := chunks_length_le r rest
    simp only [chunks,drawRuns,leadBytes,List.length_cons] at full ⊢
    split_ifs at full ⊢ with zero empty
    · omega
    · omega
    · simp only [List.length_cons] at full
      rw [chunks_full [] rest (by omega)]
      simp
  | r, .hint _ :: rest, full => by
    simp only [chunks,drawRuns,leadBytes] at full ⊢
    exact chunks_full r rest full
  | r, .publicBytes _ :: rest, full => by
    simp only [chunks,drawRuns,leadBytes] at full ⊢
    exact chunks_full r rest full

theorem drawRuns_length : ∀ E : List SourceEvent, (drawRuns E).length = (verifierBytes E).length
  | [] => rfl
  | .prover _ _ :: rest => by simpa [drawRuns,verifierBytes] using drawRuns_length rest
  | .verifier _ :: rest => by simpa [drawRuns,verifierBytes] using drawRuns_length rest
  | .hint _ :: rest => by simpa [drawRuns,verifierBytes] using drawRuns_length rest
  | .publicBytes _ :: rest => by simpa [drawRuns,verifierBytes] using drawRuns_length rest

theorem frames_window (pre runs : List (List Byte)) (x : List Byte) (j : Nat) (hj : j < runs.length) :
    ((pre ++ (x :: runs).dropLast).take (pre.length + j + 1)).drop (pre.length + 1) = runs.take j := by
  have ne : runs ≠ [] := by
    rintro rfl
    simp at hj
  have hmin : min j (runs.length - 1) = j := by omega
  rw [List.dropLast_cons_of_ne_nil ne,List.dropLast_eq_take,List.take_append,List.drop_append,
    List.take_of_length_le (by omega : pre.length ≤ pre.length + j + 1)]
  simp [show pre.length + j + 1 - pre.length = j + 1 by omega,List.take_take,hmin]

/-- A history whose opening frames are the first `j` draw runs has the `k`-th run as its absorb frame `boundary + k + 1`. -/
theorem frame_of_openingFrames (boundary j : Nat) (h : FramedHistory) (runs : List (List Byte))
    (frames : openingFrames boundary h = runs.take j)
    (absorbs : ∀ f ∈ h.frames, ∃ previous bytes, f = .absorb previous bytes)
    (k : Nat) (bytes : List Byte) (before : k < j) (run : runs[k]? = some bytes) :
    ∃ previous, h.frames[boundary + k + 1]? = some (.absorb previous bytes) := by
  have at' := congrArg (fun l => l[k]?) frames
  simp only [openingFrames,List.getElem?_map,List.getElem?_drop,List.getElem?_take,before,↓reduceIte,run]
    at at'
  obtain ⟨f,found,same⟩ := Option.map_eq_some_iff.mp at'
  obtain ⟨previous,run',rfl⟩ := absorbs f (List.mem_of_getElem? found)
  simp only [frameBytes] at same
  subst same
  exact ⟨previous,by rw [← found]; congr 1; omega⟩

open SpongefishCurrentMixedModeCompiler in
/-- The semantic replay under fixed answers appends one call event per call and applies exactly those events to the pending absorb state. -/
theorem replay_apply (ans : Coordinate → Digest32) (cur : SemanticCursor) (calls : List Call)
    (good : CacheOK ans cur.cache) (fin : SemanticCursor)
    (ok : (runWith ans (replayProgram cur calls)).result = .ok fin) :
    ∃ evs, fin.data.events = cur.data.events ++ evs ∧ List.Forall₂ CallEvent calls evs ∧
      fin.data.pending = applyEvents cur.data.pending evs := by
  induction calls generalizing cur with
  | nil =>
    simp only [replayProgram,runWith,Except.ok.injEq] at ok
    subst ok
    exact ⟨[],by simp,.nil,rfl⟩
  | cons call calls ih =>
    cases call with
    | read kind =>
      cases parsed : kind.codec.parse cur.data.narg with
      | none => simp [replayProgram,parsed,runWith] at ok
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        simp only [replayProgram,parsed] at ok
        obtain ⟨evs,events,shapes,pending⟩ := ih (readNext cur kind value rest) good ok
        refine ⟨.prover kind (kind.codec.bytes value) :: evs,?_,.cons ⟨value,rfl⟩ shapes,?_⟩
        · rw [events]
          simp [readNext,boundData]
        · rw [pending]
          rfl
    | hint =>
      cases hints : cur.data.hints with
      | nil => simp [replayProgram,hints,runWith] at ok
      | cons bytes rest =>
        simp only [replayProgram,hints] at ok
        obtain ⟨evs,events,shapes,pending⟩ := ih (hintNext cur bytes rest) good ok
        refine ⟨.hint bytes :: evs,?_,.cons ⟨bytes,rfl⟩ shapes,?_⟩
        · rw [events]
          simp [hintNext]
        · rw [pending]
          rfl
    | draw g =>
      have positive := group_bytes_pos g
      by_cases guard : cur.data.pending.consumed + g.bytes ≤ DuplexRefinement.maxCursor
      · simp only [replayProgram,positive,guard,↓reduceDIte,seq,runWith_bind] at ok
        obtain ⟨good₁,answer₁,_,_,_⟩ := collect_with ans cur.data.pending
          (positions cur.data.pending g.bytes) (positions_valid _ cur.framed _ guard) cur.cache good
        generalize (runWith ans (collect cur.data.pending (positions cur.data.pending g.bytes)
          (positions_valid _ cur.framed _ guard) cur.cache)) = first at *
        obtain ⟨obs₁,cache,bytes⟩ := first
        dsimp only at good₁ answer₁ ok
        obtain ⟨evs,events,shapes,pending⟩ := ih (drawn cur g.bytes guard cache bytes) good₁ ok
        have length : bytes.length = g.bytes := by
          rw [answer₁]
          simp [positions]
        refine ⟨.verifier bytes :: evs,?_,.cons ⟨bytes,length,rfl⟩ shapes,?_⟩
        · rw [events]
          simp [drawn]
        · rw [pending]
          simp [applyEvents,length,drawn]
      · simp [replayProgram,positive,guard,runWith] at ok

theorem frameBytes_core (f : ByteFrame) : frameBytes f.historicalCore = byteRun f := by
  cases f
  rfl

section Packets
open DuplexRefinement DuplexFraming DuplexModeGame RawOracleCoupling TypedOracleCompiler SpongefishCurrentModeQueries
open SpongefishCurrentMixedModeCompiler SpongefishCurrentRoundPackets

/-- `SpongefishCurrentOpeningPackets.opening_packets` with the frame content of its histories: the opening events have the call shapes of the opening, and the opening frames (index `boundary + 1` on) of the `j`-th draw history are the first `j` prover runs after the opening draws. Frame `boundary + k + 1` of every later history is the absorb frame of the prover bytes between the `k`-th and `(k+1)`-th verifier events, and the opening adds no byte before its first draw. -/
theorem opening_frames {S : Type} (Q : Nat) (iv : Digest32)
    (grinding : Fin (cfg).folds.size → Fin 64) (boundary : Nat)
    (tag instanceBytes : List Byte) (pre : List Call)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (k : Option SpongefishCurrentInitializedMode.Result → Program S)
    (counted : Counts Q (WHIRModeFinal.bind (SpongefishCurrentInitializedMode.afterPrefix iv tag
      instanceBytes prefixProgram (pre ++ openingCalls grinding)) k))
    (shape : openingShape instanceBytes pre = (boundary,true))
    (table : (key : Key p Q iv grinding boundary) → Answer p Q iv grinding boundary key)
    (data : Data)
    (success : (Sampling.eval table (SpongefishCurrentBCSKnowledge.source
      (partition p Q iv grinding boundary) iv
      (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram
        (pre ++ openingCalls grinding))
      (WHIRModeFinal.bind_prefix_counted _ k Q counted))).result = some (.ok data)) :
    ∃ histories : List FramedHistory,
      histories.length = (openingDraws grinding).length ∧
      (∀ (j : Nat) (h : FramedHistory), histories[j]? = some h → h.frames.length = boundary + j + 1) ∧
      (∀ (i j : Nat) (hi hj : FramedHistory), i ≤ j → histories[i]? = some hi →
        histories[j]? = some hj → hi = {hj with frames := hj.frames.take (boundary + i + 1)}) ∧
      (verifierBytes (SpongefishCurrentOpeningPackets.openingEvents grinding data.events)).length =
        (openingDraws grinding).length ∧
      (∀ (j : Nat) (h : FramedHistory) (bytes : List Byte), histories[j]? = some h →
        (verifierBytes (SpongefishCurrentOpeningPackets.openingEvents grinding data.events))[j]? = some bytes →
        ∃ g, (drawGroups (openingCalls grinding))[j]? = some g ∧
          bytes = (List.range g.bytes).map (fun i => idealAnswer Q iv
            (roOf (partition p Q iv grinding boundary) table) ⟨h,.output (i/32)⟩
              ⟨i%32,Nat.mod_lt _ (by decide)⟩)) ∧
      (∀ (j : Nat) (q : Coord p), (openingDraws grinding)[j]? = some (some q) →
        ∃ (packet : Packet p Q grinding boundary) (bytes : List Byte),
          packet.coord = q ∧ histories[j]? = some packet.history ∧
          (verifierBytes (SpongefishCurrentOpeningPackets.openingEvents grinding data.events))[j]? =
            some bytes ∧
          decodeSample packet.coord bytes =
            PCSBCSChallengeOracle.grouped packet.coord (table (.inl packet)) ∧
          (⟨.inl packet,table (.inl packet)⟩ : Sigma (Answer p Q iv grinding boundary)) ∈
            (Sampling.execute table (SpongefishCurrentBCSKnowledge.source
              (partition p Q iv grinding boundary) iv
              (WHIRModeFinal.bind (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes
                prefixProgram (pre ++ openingCalls grinding)) k) counted)).2) ∧
      List.Forall₂ CallEvent (openingCalls grinding)
        (SpongefishCurrentOpeningPackets.openingEvents grinding data.events) ∧
      leadBytes (SpongefishCurrentOpeningPackets.openingEvents grinding data.events) = [] ∧
      (∀ (j : Nat) (h : FramedHistory), histories[j]? = some h →
        openingFrames boundary h =
          (drawRuns (SpongefishCurrentOpeningPackets.openingEvents grinding data.events)).take j ∧
        ∀ f ∈ h.frames, ∃ previous bytes, f = .absorb previous bytes) ∧
      (∀ (j : Nat) (h : FramedHistory) (k : Nat) (bytes : List Byte), histories[j]? = some h → k < j →
        (drawRuns (SpongefishCurrentOpeningPackets.openingEvents grinding data.events))[k]? = some bytes →
        ∃ previous, h.frames[boundary + k + 1]? = some (.absorb previous bytes)) ∧
      (∀ h : FramedHistory, histories[0]? = some h →
        SpongefishCurrentGoodEvent.postBinding boundary data = ⟨h,.output 0⟩) := by
  let part := partition p Q iv grinding boundary
  let ro := roOf part table
  let ans := idealAnswer Q iv ro
  rw [eval_source] at success
  obtain ⟨session,narg,hints,fin,replayOk,finData,replayInside⟩ := afterPrefix_replay
    (DuplexPublicSimulator.simulator Q) ro iv tag instanceBytes prefixProgram
    (pre ++ openingCalls grinding) _ Q (Nat.le_refl Q) _ data success
  obtain ⟨oldInside,_⟩ := ideal_bind_parts (DuplexPublicSimulator.simulator Q) ro iv _ k
    ⟨seedOf part table,[]⟩ Q (Nat.le_refl Q) counted
  have inFinal : ∀ o ∈ (runWith ans (replayProgram
      (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints)
        (pre ++ openingCalls grinding))).observations,
      o ∈ (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv _ counted)).observations := by
    rw [eval_source]
    exact fun o h => oldInside o (replayInside o h)
  obtain ⟨mid,preOk,openOk,obsSplit⟩ := replay_append ans _ pre (openingCalls grinding) fin replayOk
  obtain ⟨midShaped,midGood,midKnown⟩ := replay_shape ans _ pre _
    (initial_shaped session instanceBytes narg hints) (fun _ _ h => by cases h) mid preOk
  rw [show frameShape (0,decide (instanceBytes ≠ [])) pre = (boundary,true) from shape] at midShaped
  obtain ⟨midFrames,midReady,midZeroed⟩ := midShaped
  have midRun : mid.data.pending.run ≠ [] := midReady.mp rfl
  obtain ⟨evs,ms,events,evLength,_,msLength,bytesLength,facts⟩ := replay_draws ans mid
    (openingCalls grinding) false (by simpa using midRun) midZeroed (scan_opening_calls grinding)
    midGood fin openOk
  obtain ⟨evs',events',calls',pending'⟩ := replay_apply ans mid (openingCalls grinding) midGood fin openOk
  have sameEvs : evs' = evs := by
    rw [events] at events'
    exact (List.append_cancel_left events').symm
  subst sameEvs
  have openEvents : SpongefishCurrentOpeningPackets.openingEvents grinding data.events = evs' := by
    rw [← finData,events]
    unfold SpongefishCurrentOpeningPackets.openingEvents
    rw [List.length_append,evLength,Nat.add_sub_cancel]
    exact List.drop_left
  have matched := opening_matches grinding (p := p)
  have drawLength : (drawGroups (openingCalls grinding)).length = (openingDraws grinding).length :=
    matched.length_eq.symm
  have factAt : ∀ j m, ms[j]? = some m → ∃ g bytes, (drawGroups (openingCalls grinding))[j]? = some g ∧
      (verifierBytes evs')[j]? = some bytes ∧
      DrawFact ans mid.data.pending.domain mid.data.pending.frames.length mid.cache
        fin.data.pending.frames (runWith ans (replayProgram mid (openingCalls grinding))).observations
        j g m bytes := by
    intro j m found
    have within : j < ms.length := (List.getElem?_eq_some_iff.mp found).1
    obtain ⟨g,hg⟩ : ∃ g, (drawGroups (openingCalls grinding))[j]? = some g :=
      ⟨_,List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨bytes,hb⟩ : ∃ bytes, (verifierBytes evs')[j]? = some bytes :=
      ⟨_,List.getElem?_eq_getElem (by omega)⟩
    exact ⟨g,bytes,hg,hb,facts j g m bytes hg found hb⟩
  have historyLength : ∀ j m, ms[j]? = some m →
      ((close m).core.history.frames).length = boundary + j + 1 := by
    intro j m found
    obtain ⟨g,bytes,_,_,fact⟩ := factAt j m found
    simp only [Pending.core,List.length_map,close_frames m fact.run_ne,List.length_append,
      List.length_singleton,fact.frames_eq,midFrames]
  have closedTake : ∀ j m, ms[j]? = some m →
      (close m).frames = fin.data.pending.frames.take (boundary + j + 1) := by
    intro j m found
    obtain ⟨_,_,_,_,fact⟩ := factAt j m found
    have length := historyLength j m found
    simp only [Pending.core,List.length_map] at length
    rw [List.prefix_iff_eq_take.mp fact.closed,length]
  -- every draw closes a nonempty run, so the closed runs are the lead run then the draw runs
  have lead := leadBytes_opening grinding evs' calls'
  obtain ⟨restCalls,head⟩ := openingCalls_head grinding (p := p)
  have positiveDraws : 0 < (openingDraws grinding).length := by
    rw [← drawLength,head]
    simp [drawGroups]
  have runsLength : (drawRuns evs').length = (openingDraws grinding).length := by
    rw [drawRuns_length,bytesLength,drawLength]
  have applied := apply_frames mid.data.pending evs'
  rw [← pending'] at applied
  have full : chunks mid.data.pending.run evs' = ((mid.data.pending.run ++ leadBytes evs') ::
      drawRuns evs').dropLast := by
    apply chunks_full
    obtain ⟨m,lastAt⟩ : ∃ m, ms[(openingDraws grinding).length - 1]? = some m :=
      ⟨_,List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨_,_,_,_,fact⟩ := factAt _ m lastAt
    have length := historyLength _ m lastAt
    simp only [Pending.core,List.length_map] at length
    have bigger := fact.closed.length_le
    have total := congrArg List.length applied
    simp only [List.length_map,List.length_append,midFrames] at total
    omega
  have windowAt : ∀ j m, ms[j]? = some m →
      openingFrames boundary (close m).core.history = (drawRuns evs').take j := by
    intro j m found
    have within : j < (drawRuns evs').length := by
      have := (List.getElem?_eq_some_iff.mp found).1
      omega
    have bytesOf : (fin.data.pending.frames.map byteRun) =
        (mid.data.pending.frames.map byteRun) ++ ((mid.data.pending.run ++ leadBytes evs') ::
          drawRuns evs').dropLast := by
      rw [applied,full]
    have preLength : (mid.data.pending.frames.map byteRun).length = boundary := by
      simp [midFrames]
    unfold openingFrames
    simp only [Pending.core,closedTake j m found,List.map_drop,List.map_take,List.map_map]
    rw [show (frameBytes ∘ ByteFrame.historicalCore) = byteRun from funext frameBytes_core,bytesOf,
      ← preLength]
    exact frames_window _ _ _ j within
  have absorbsAt : ∀ m : Pending, ∀ f ∈ (close m).core.history.frames,
      ∃ previous bytes, f = .absorb previous bytes := by
    intro m f member
    simp only [Pending.core,List.mem_map] at member
    obtain ⟨g,_,rfl⟩ := member
    cases g with
    | absorb previous bytes => exact ⟨previous,bytes,rfl⟩
  have domainEq : fin.data.pending.domain = mid.data.pending.domain := by
    rw [pending']
    exact applyEvents_domain _ _
  have postEq : ∀ m, ms[0]? = some m →
      SpongefishCurrentGoodEvent.postBinding boundary data = ⟨(close m).core.history,.output 0⟩ := by
    intro m found
    obtain ⟨_,_,_,_,fact⟩ := factAt 0 m found
    have takeEq := closedTake 0 m found
    have length := historyLength 0 m found
    simp only [Pending.core,List.length_map] at length
    have long : boundary + 0 + 1 ≤ fin.data.pending.frames.length := by
      have := fact.closed.length_le
      omega
    obtain ⟨extra,closeEq⟩ := close_prefix fin.data.pending
    unfold SpongefishCurrentGoodEvent.postBinding
    rw [← finData]
    simp only [Pending.core,close_domain,fact.domain_eq,domainEq,← List.map_take,← closeEq,
      List.take_append_of_le_length long,← takeEq]
  refine ⟨ms.map (fun m => (close m).core.history),by simp [msLength,drawLength],?_,?_,
    by rw [openEvents,bytesLength,drawLength],?_,?_,by rw [openEvents]; exact calls',
    by rw [openEvents]; exact lead,?_,?_,?_⟩
  · intro j h found
    rw [List.getElem?_map] at found
    obtain ⟨m,member,rfl⟩ := Option.map_eq_some_iff.mp found
    exact historyLength j m member
  · intro i j hi hj order foundI foundJ
    rw [List.getElem?_map] at foundI foundJ
    obtain ⟨mi,memberI,rfl⟩ := Option.map_eq_some_iff.mp foundI
    obtain ⟨mj,memberJ,rfl⟩ := Option.map_eq_some_iff.mp foundJ
    obtain ⟨_,_,_,_,factI⟩ := factAt i mi memberI
    obtain ⟨_,_,_,_,factJ⟩ := factAt j mj memberJ
    have lengthI := historyLength i mi memberI
    have lengthJ := historyLength j mj memberJ
    simp only [Pending.core,List.length_map] at lengthI lengthJ
    have nested : (close mi).frames <+: (close mj).frames :=
      List.prefix_of_prefix_length_le factI.closed factJ.closed (by omega)
    have taken := List.prefix_iff_eq_take.mp nested
    rw [lengthI] at taken
    simp only [Pending.core,close_domain,factI.domain_eq,factJ.domain_eq,← List.map_take,← taken]
  · intro j h bytes found bytesAt
    rw [List.getElem?_map] at found
    obtain ⟨m,member,rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨g,bytes',groupAt,bytesAt',fact⟩ := factAt j m member
    rw [openEvents,bytesAt'] at bytesAt
    cases bytesAt
    refine ⟨g,groupAt,?_⟩
    rw [fact.bytes_eq]
    simp only [positions,fact.consumed_eq,Nat.zero_add,List.map_map]
    rfl
  · intro j q found
    obtain ⟨g,groupAt,groupEq⟩ := forall₂_getElem? matched j (some q) found
    change g = group q at groupEq
    have within : j < ms.length := by
      have := (List.getElem?_eq_some_iff.mp groupAt).1
      omega
    obtain ⟨m,member⟩ : ∃ m, ms[j]? = some m := ⟨_,List.getElem?_eq_getElem within⟩
    obtain ⟨g',bytes,groupAt',bytesAt,fact⟩ := factAt j m member
    rw [groupAt] at groupAt'
    cases groupAt'
    subst groupEq
    have width := openingDraws_width grinding q (List.mem_of_getElem? found)
    have groupBytes := group_bytes q width
    have seen : Observed ans (runWith ans (replayProgram
        (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints)
          (pre ++ openingCalls grinding))).observations (coordinate m 0) := by
      rw [obsSplit]
      rcases fact.first with cached | observed
      · rcases midKnown _ cached with impossible | observed
        · exact (impossible rfl).elim
        · exact observed_mono ans _ _ _ (fun o h => List.mem_append_left _ h) observed
      · exact observed_mono ans _ _ _ (fun o h => List.mem_append_right _ h) observed
    obtain ⟨valid0,seenAt⟩ := seen
    have bound0 : pathCost (coordinate m 0) ≤ Q := by
      have final := inFinal _ seenAt
      rw [eval_source] at final
      exact ideal_cost _ _ _ _ _ _ _ _ _ final
    have bound : ∀ b, pathCost (coordinate m b) ≤ Q := fun b => (coordinate_cost m b).le.trans bound0
    have small : ∀ b : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth q)), b.val < 2^44 := by
      intro b
      have := b.isLt
      have guard := fact.guard
      simp only [PCSBCSChallengeOracle.blocks,maxCursor] at this guard
      omega
    let packet : Packet p Q grinding boundary :=
      { history := (close m).core.history
        coord := q
        classified := by
          unfold classify
          rw [historyLength j m member]
          simp [show boundary < boundary + j + 1 by omega,
            show boundary + j + 1 - boundary - 1 = j by omega,found]
        admissible := fun b => coordinate_admissible m fact.framed b.val (small b)
        bounded := fun b => bound b.val }
    have blockAnswer : ∀ b : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth q)),
        ans (coordinate m b.val) = table (.inl packet) b := by
      intro b
      have encoded : part.encode ⟨packet,b⟩ = .inr (constructionKey Q iv (coordinate m b.val) (bound b.val)) :=
        rfl
      simp only [ans,idealAnswer,bound b.val,↓reduceDIte,ro,roOf]
      rw [← encoded]
      exact join_encode part table ⟨packet,b⟩
    refine ⟨packet,bytes,rfl,by simp [member,packet],by rw [openEvents]; exact bytesAt,?_,?_⟩
    · apply decode_grouped
      intro i within
      rw [fact.bytes_eq]
      change i < 24 * PCSBCSRounds.rawWidth q at within
      have inGroup : i < (group q).bytes := by omega
      simp only [positions,fact.consumed_eq,Nat.zero_add,List.map_map,List.getElem?_map,
        List.getElem?_range inGroup,Option.map_some,Function.comp_apply]
      exact congrArg some (congrFun (blockAnswer ⟨i/32,by unfold PCSBCSChallengeOracle.blocks; omega⟩) _)
    · apply observed_recorded part iv _ counted table (coordinate m 0) valid0 (ans (coordinate m 0))
        (inFinal _ seenAt) ⟨packet,firstBlock packet⟩
      intro bound'
      have encoded : part.encode ⟨packet,firstBlock packet⟩ = .inr (constructionKey Q iv (coordinate m 0) bound') :=
        rfl
      rw [← encoded]
      exact part.recognize_encode _
  · intro j h found
    rw [List.getElem?_map] at found
    obtain ⟨m,member,rfl⟩ := Option.map_eq_some_iff.mp found
    rw [openEvents]
    exact ⟨windowAt j m member,absorbsAt m⟩
  · intro j h k bytes found before run
    rw [List.getElem?_map] at found
    obtain ⟨m,member,rfl⟩ := Option.map_eq_some_iff.mp found
    rw [openEvents] at run
    exact frame_of_openingFrames boundary j _ (drawRuns evs') (windowAt j m member) (absorbsAt m) k bytes
      before run
  · intro h found
    rw [List.getElem?_map] at found
    obtain ⟨m,member,rfl⟩ := Option.map_eq_some_iff.mp found
    exact postEq m member

end Packets

/-! ## Tape, seed, roots and query replies of the walk -/

theorem split_post (q : Coord p) (pre post : List (Coord p))
    (split : WHIRHistory.schedule cfg = pre ++ q :: post) : q ∉ post := by
  have nd := WHIRHistory.schedule_nodup cfg
  rw [split,List.nodup_append,List.nodup_cons] at nd
  exact nd.2.1.1

theorem split_of_mem (q : Coord p) :
    ∃ pre post, WHIRHistory.schedule cfg = pre ++ q :: post ∧ q ∉ pre ∧ q ∉ post := by
  obtain ⟨pre,post,split⟩ := List.append_of_mem (WHIRHistory.coordinate_mem_schedule q)
  have nd := WHIRHistory.schedule_nodup cfg
  rw [split,List.nodup_append,List.nodup_cons] at nd
  exact ⟨pre,post,split,fun member => nd.2.2 q member q List.mem_cons_self rfl,nd.2.1.1⟩

/-- The walk on the opening call events, split at a scheduled coordinate: the blocks before it, its own block and step, and the blocks after it. -/
theorem walk_at (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (q : Coord p) (pre post : List (Coord p)) (split : WHIRHistory.schedule cfg = pre ++ q :: post) :
    ∃ (bpre : List (List SourceEvent)) (bq : List SourceEvent) (bpost : List (List SourceEvent))
      (mid : Collected p) (st : List SourceEvent × Collected p) (fin : List SourceEvent),
      E = bpre.flatten ++ (bq ++ bpost.flatten) ∧ Blocks grinding pre bpre ∧
      List.Forall₂ CallEvent (callsOf grinding q) bq ∧ Blocks grinding post bpost ∧
      WalkOutcome grinding pre bpre (bq ++ bpost.flatten) (Collected.start root0)
        (bq ++ bpost.flatten,mid) ∧
      StepOutcome H decode grinding lanes q bq bpost.flatten mid st ∧
      WalkOutcome grinding post bpost [] st.2 (fin,col) := by
  obtain ⟨bx,fin,rfl,blocks,ev⟩ := walk_whole H decode grinding lanes root0 E col calls walked
  rw [split] at blocks ev
  obtain ⟨bpre,brest,rfl,bp,br⟩ := forall₂_split blocks
  rcases br with _ | @⟨_,bq,_,bpost,shape,bpo⟩
  simp only [List.flatten_append,List.flatten_cons,List.append_nil] at ev ⊢
  obtain ⟨mid,first,second⟩ := walk_split H decode grinding lanes pre (q :: post) bpre
    (bq ++ bpost.flatten) (Collected.start root0) (fin,col) bp ev
  have before := walk_run H decode grinding lanes pre bpre _ _ _ bp first
  rw [walk_cons_eval] at second
  obtain ⟨st,stepOk,restOk⟩ := Option.bind_eq_some_iff.mp second
  have step := step_block H decode grinding lanes q bq bpost.flatten mid st shape stepOk
  obtain ⟨st₁,st₂⟩ := st
  have rest : st₁ = bpost.flatten := step.1
  subst rest
  have after := walk_run H decode grinding lanes post bpost [] st₂ (fin,col) bpo (by simpa using restOk)
  exact ⟨bpre,bq,bpost,mid,(bpost.flatten,st₂),fin,rfl,bp,shape,bpo,before,step,after⟩

theorem mid_size (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) (pre post : List (Coord p))
    (split : WHIRHistory.schedule cfg = pre ++ q :: post) (notin : q ∉ pre)
    (bpre : List (List SourceEvent)) (R : List SourceEvent) (root0 : Digest32) (mid : Collected p)
    (out : WalkOutcome grinding pre bpre R (Collected.start root0) (R,mid)) :
    mid.replies.size = position q := by
  obtain ⟨_,_,_,⟨rs,repl,fits⟩,_⟩ := out
  have allVisible : pre.filter visibleQ = pre :=
    List.filter_eq_self.mpr (fun r m => visibleQ_of_mem r (split_visible q pre post split r m))
  rw [allVisible] at fits
  simp only at repl
  rw [repl,split_position q pre post split notin,fits.length_eq]
  simp [Collected.start]

theorem headD_drop (l : List (List Byte)) (n : Nat) (b : List Byte) (h : l[n]? = some b) :
    (l.drop n).headD [] = b := by
  rw [List.headD_eq_head?_getD,List.head?_drop,h]
  rfl

/-- The PCS draw bytes of a coordinate block are the verifier bytes of the whole opening at the coordinate's draw index. -/
theorem sample_eq (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) (bpre : List (List SourceEvent))
    (bq rest : List SourceEvent) (j : Nat) (bytes : List Byte)
    (index : j = (verifierBytes bpre.flatten).length + (powDraws grinding q).length)
    (vq : (verifierBytes bq).length = (drawList grinding q).length) (width : PCSBCSRounds.rawWidth q ≠ 0)
    (drawn : (verifierBytes (bpre.flatten ++ (bq ++ rest)))[j]? = some bytes) :
    sampleBytes grinding q bq = bytes := by
  have lengthQ : (verifierBytes bq).length = (powDraws grinding q).length + 1 := by
    rw [vq]
    simp [drawList,pcsDraws,width]
  rw [verifierBytes_append,verifierBytes_append,index,
    List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega)] at drawn
  exact headD_drop _ _ _ drawn

/-- Tape of the walk at a PCS draw: the coordinate's sample is the decoded verifier bytes of its opening draw. -/
theorem tape_draw (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (j : Nat) (q : Coord p) (bytes : List Byte)
    (found : (SpongefishCurrentRoundPackets.openingDraws grinding)[j]? = some (some q))
    (drawn : (verifierBytes E)[j]? = some bytes) :
    get q col.tape = StackWHIRReplay.projectSample q (decodeSample q bytes) := by
  obtain ⟨pre,post,split,_,index⟩ := flatMap_index grinding _ (WHIRHistory.schedule_nodup cfg) j q
    (by rw [← openingDraws_eq]; exact found)
  obtain ⟨bpre,bq,bpost,mid,st,fin,rfl,_,_,_,before,step,after⟩ :=
    walk_at H decode grinding lanes root0 E col calls walked q pre post split
  have width := SpongefishCurrentRoundPackets.openingDraws_width grinding q (List.mem_of_getElem? found)
  obtain ⟨_,vPre,_⟩ := before
  obtain ⟨_,vq,_,tape,_⟩ := step
  obtain ⟨_,_,_,_,_,tapeRest,_⟩ := after
  rw [tapeRest q (split_post q pre post split),tape,get_set,
    sample_eq grinding q bpre bq bpost.flatten j bytes (by rw [vPre]; exact index) vq width drawn]

/-- Tape of the walk at a zero-width coordinate. -/
theorem tape_zero (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (q : Coord p) (zero : PCSBCSRounds.rawWidth q = 0) :
    get q col.tape = StackWHIRReplay.projectSample q (decodeSample q []) := by
  obtain ⟨pre,post,split,_,later⟩ := split_of_mem q
  obtain ⟨bpre,bq,bpost,mid,st,fin,rfl,_,_,_,_,step,after⟩ :=
    walk_at H decode grinding lanes root0 E col calls walked q pre post split
  obtain ⟨_,vq,_,tape,_⟩ := step
  obtain ⟨_,_,_,_,_,tapeRest,_⟩ := after
  have empty : sampleBytes grinding q bq = [] := by
    have : (verifierBytes bq).length ≤ (powDraws grinding q).length := by
      rw [vq]
      simp [drawList,pcsDraws,zero]
    simp [sampleBytes,List.drop_eq_nil_of_le this]
  rw [tapeRest q later,tape,get_set,empty]

/-- Seed of the walk: the decoded verifier bytes of the initial draw. -/
theorem seed_draw (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (j : Nat) (bytes : List Byte)
    (found : (SpongefishCurrentRoundPackets.openingDraws grinding)[j]? = some (some .initial))
    (drawn : (verifierBytes E)[j]? = some bytes) :
    col.seed = some (decodeSample (.initial : Coord p) bytes) := by
  obtain ⟨pre,post,split,_,index⟩ := flatMap_index grinding _ (WHIRHistory.schedule_nodup cfg) j _
    (by rw [← openingDraws_eq]; exact found)
  obtain ⟨bpre,bq,bpost,mid,st,fin,rfl,_,_,_,before,step,after⟩ :=
    walk_at H decode grinding lanes root0 E col calls walked _ pre post split
  have width := SpongefishCurrentRoundPackets.openingDraws_width grinding _ (List.mem_of_getElem? found)
  obtain ⟨_,vPre,_⟩ := before
  obtain ⟨_,vq,_,_,seed,_⟩ := step
  obtain ⟨_,_,_,_,_,_,seedRest,_⟩ := after
  rw [seedRest (split_post _ pre post split),seed,
    sample_eq grinding _ bpre bq bpost.flatten j bytes (by rw [vPre]; exact index) vq width drawn]
  rfl

/-- The first walk root is the commitment root the walk starts from. -/
theorem root_start (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col) :
    col.roots[0]? = some root0 := by
  obtain ⟨bx,fin,rfl,blocks,ev⟩ := walk_whole H decode grinding lanes root0 E col calls walked
  obtain ⟨_,_,_,_,⟨rts,roots,_⟩,_⟩ := walk_run H decode grinding lanes _ bx [] _ _ blocks ev
  simp only at roots
  rw [roots]
  simp [Collected.start]

/-- The authenticated query reply of level `i` sits at reply position `position (.query i)`; its opening is recorded, its root is the walk's level root `i`, and its proof and rows come from the decoder and the whole-hash Merkle program at the final tape. -/
theorem query_reply (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (i : Fin (cfg).folds.size) :
    ∃ (hint : List Byte) (proof : MerkleTransport.PrunedMerklePaths) (root : Digest32)
      (opened : WHIRPhysicalVerifier.Opened) (m : Message Concrete.E),
      col.replies[position (.query i : Coord p)]? = some (.query opened.rows m) ∧
      (⟨i,root,hint,proof,opened⟩ : QueryOpening p) ∈ col.openings ∧
      col.roots[i.val]? = some root ∧
      decode (WHIRPhysicalVerifier.queryIndices p i (get (.query i) col.tape)) (rowWords lanes i) hint =
        some proof ∧
      HashProgram.eval H (openProgram lanes i root proof (get (.query i) col.tape)) = some opened := by
  obtain ⟨pre,post,split,notin,later⟩ := split_of_mem (.query i : Coord p)
  obtain ⟨bpre,bq,bpost,mid,st,fin,rfl,_,_,_,before,step,after⟩ :=
    walk_at H decode grinding lanes root0 E col calls walked _ pre post split
  have size := mid_size grinding _ pre post split notin bpre _ root0 mid before
  obtain ⟨_,_,_,_,_,_,_,rootsSame,_,_,queries⟩ := step
  obtain ⟨hint,proof,root,opened,m,r₁,r₂,r₃,r₄,r₅⟩ := queries i rfl
  obtain ⟨_,_,_,⟨rs,repl,_⟩,⟨rts,roots,_⟩,tapeRest,_,opens⟩ := after
  simp only at repl roots tapeRest opens r₁ r₂ r₃ r₄ r₅
  have rootsEq : st.2.roots = mid.roots := rootsSame rfl
  have tapeEq := tapeRest _ later
  refine ⟨hint,proof,root,opened,m,?_,?_,?_,?_,?_⟩
  · rw [repl,r₁,← size,Array.getElem?_append_left (by simp)]
    simp
  · apply opens
    rw [r₂]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · have within : i.val < mid.roots.size := (Array.getElem?_eq_some_iff.mp r₃).1
    rw [roots,rootsEq,Array.getElem?_append_left within]
    exact r₃
  · rw [tapeEq]
    exact r₄
  · rw [tapeEq]
    exact r₅

/-! ## Level roots -/

theorem mem_level (n : Fin (cfg).folds.size) (x : Coord p) (member : x ∈ levelCoordinates cfg n.val) :
    (∃ k, x = .fold n k) ∨ (∃ k, x = .ood n k) ∨ x = .query n := by
  unfold levelCoordinates at member
  rw [dite_eq_left n.isLt] at member
  simp only [List.mem_append,List.mem_ofFn,List.mem_singleton] at member
  rcases member with (⟨k,rfl⟩ | ⟨k,rfl⟩) | rfl
  · exact .inl ⟨k,rfl⟩
  · exact .inr (.inl ⟨k,rfl⟩)
  · exact .inr (.inr rfl)

theorem fold_mem_level (n : Fin (cfg).folds.size) (k : Fin (cfg).folds[n.val]!) :
    (.fold n k : Coord p) ∈ levelCoordinates cfg n.val := by
  unfold levelCoordinates
  rw [dite_eq_left n.isLt]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨k,rfl⟩))

theorem rootFold_level (n : Fin (cfg).folds.size) (x : Coord p) (member : x ∈ levelCoordinates cfg n.val)
    (root : rootFold x = true) : ∃ k, x = .fold n k ∧ isLastFold n k = true := by
  rcases mem_level n x member with ⟨k,rfl⟩ | ⟨k,rfl⟩ | rfl
  · simp only [rootFold,Bool.and_eq_true] at root
    exact ⟨k,rfl,root.1⟩
  · simp [rootFold] at root
  · simp [rootFold] at root

theorem level_count (n : Fin (cfg).folds.size) (more : n.val + 1 < (cfg).folds.size) :
    ((levelCoordinates cfg n.val).filter rootFold).length = 1 := by
  have pos := WHIRQueryOracleRecurrence.production_folds_positive p n
  have mem := fold_mem_level n ⟨(cfg).folds[n.val]! - 1,by omega⟩
  have same : (levelCoordinates cfg n.val).filter rootFold = (levelCoordinates cfg n.val).filter
      (· == (.fold n ⟨(cfg).folds[n.val]! - 1,by omega⟩ : Coord p)) := by
    apply List.filter_congr
    intro x member
    rcases mem_level n x member with ⟨k,rfl⟩ | ⟨k,rfl⟩ | rfl
    · have := k.isLt
      rw [Bool.eq_iff_iff]
      simp only [rootFold,isLastFold,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,
        CausalProbability.Coordinate.fold.injEq,heq_eq_eq,true_and,Fin.ext_iff]
      constructor
      · intro h
        omega
      · intro h
        exact ⟨by omega,more⟩
    · simp [rootFold]
    · simp [rootFold]
  rw [same,← List.count_eq_length_filter]
  exact (WHIRHistory.levelCoordinates_nodup cfg n.val).count_of_mem mem

theorem levels_count : ∀ (i : Nat), i + 1 < (cfg).folds.size →
    (((List.range i).flatMap (levelCoordinates cfg)).filter (rootFold (p := p))).length = i
  | 0, _ => by simp
  | m + 1, bound => by
    rw [List.range_succ,List.flatMap_append,List.filter_append,List.length_append,
      levels_count m (by omega)]
    have one := level_count (p := p) ⟨m,by omega⟩ (by simp only; omega)
    simp only at one
    simp [one]

theorem split_unique {A : Type} [DecidableEq A] (l a b a' b' : List A) (x : A)
    (h : l = a ++ x :: b) (h' : l = a' ++ x :: b') (n : x ∉ a) (n' : x ∉ a') : a = a' := by
  have e₁ : l.idxOf x = a.length := by
    rw [h,List.idxOf_append_of_notMem n]
    simp
  have e₂ : l.idxOf x = a'.length := by
    rw [h',List.idxOf_append_of_notMem n']
    simp
  calc a = l.take a.length := by rw [h]; exact List.take_left.symm
    _ = l.take a'.length := by rw [← e₁,← e₂]
    _ = a' := by rw [h']; exact List.take_left

/-- Before the last fold of level `i`, the schedule has exactly `i` root-carrying folds. -/
theorem fold_prefix_count (i : Fin (cfg).folds.size) (k : Fin (cfg).folds[i.val]!)
    (last : isLastFold i k = true) (more : i.val + 1 < (cfg).folds.size) (pre post : List (Coord p))
    (split : WHIRHistory.schedule cfg = pre ++ .fold i k :: post) (notin : (.fold i k : Coord p) ∉ pre) :
    (pre.filter rootFold).length = i.val := by
  have hr : List.range (cfg).folds.size = List.range i.val ++ [i.val] ++
      (List.range ((cfg).folds.size-(i.val+1))).map (fun x => i.val+1+x) := by
    calc
      List.range (cfg).folds.size =
          List.range ((i.val+1)+((cfg).folds.size-(i.val+1))) := congrArg List.range (by omega)
      _ = _ := by rw [List.range_add,List.range_succ]
  obtain ⟨X,Y,levelSplit⟩ := List.append_of_mem (fold_mem_level i k)
  have decomposed : WHIRHistory.schedule cfg =
      ([.initial] ++ (List.range i.val).flatMap (levelCoordinates cfg) ++ X) ++ .fold i k ::
        (Y ++ ((List.range ((cfg).folds.size-(i.val+1))).map (fun x => i.val+1+x)).flatMap
          (levelCoordinates cfg) ++
        List.ofFn (fun j : Fin ((cfg).logN - (cfg).folds.toList.sum - 1) =>
          (Coordinate.tail ⟨j.val,by omega⟩ : Coord p)) ++ WHIRHistory.hiddenTail cfg) := by
    unfold WHIRHistory.schedule visibleCoordinates
    rw [hr]
    simp only [List.flatMap_append,List.flatMap_cons,levelSplit,
      List.append_assoc,List.cons_append,List.nil_append]
  have nd := WHIRHistory.schedule_nodup cfg
  rw [decomposed,List.nodup_append] at nd
  have notin' : (.fold i k : Coord p) ∉ [.initial] ++ (List.range i.val).flatMap (levelCoordinates cfg) ++ X :=
    fun member => nd.2.2 _ member _ List.mem_cons_self rfl
  rw [split_unique _ _ _ _ _ _ split decomposed notin notin',List.filter_append,List.filter_append,
    List.length_append,List.length_append,levels_count i.val more]
  have ndLevel := WHIRHistory.levelCoordinates_nodup cfg i.val
  rw [levelSplit,List.nodup_append] at ndLevel
  have empty : X.filter rootFold = [] := by
    rw [List.filter_eq_nil_iff]
    intro x member root
    obtain ⟨k',rfl,last'⟩ := rootFold_level i x (by rw [levelSplit]; exact List.mem_append_left _ member)
      root
    have same : k' = k := by
      simp only [isLastFold,decide_eq_true_eq] at last last'
      exact Fin.ext (by omega)
    subst same
    exact ndLevel.2.2 _ member _ List.mem_cons_self rfl
  simp [empty,rootFold]

theorem drawRuns_at : ∀ (A C : List SourceEvent) (b : List Byte),
    (drawRuns (A ++ .verifier b :: C))[(verifierBytes A).length]? = some (leadBytes C)
  | [], C, b => by simp [drawRuns,verifierBytes]
  | .prover _ _ :: A, C, b => by simpa [drawRuns,verifierBytes] using drawRuns_at A C b
  | .verifier _ :: A, C, b => by simpa [drawRuns,verifierBytes] using drawRuns_at A C b
  | .hint _ :: A, C, b => by simpa [drawRuns,verifierBytes] using drawRuns_at A C b
  | .publicBytes _ :: A, C, b => by simpa [drawRuns,verifierBytes] using drawRuns_at A C b

/-- Level root of the walk: at the draw of the last fold of level `i` (with a next level), the prover run after the draw starts with the fold message and the next root, that root is the walk's level root `i+1`, and a later opening draw closes this run into a frame. -/
theorem level_root (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (j : Nat) (i : Fin (cfg).folds.size) (k : Fin (cfg).folds[i.val]!)
    (found : (SpongefishCurrentRoundPackets.openingDraws grinding)[j]? = some (some (.fold i k)))
    (last : isLastFold i k = true) (more : i.val + 1 < (cfg).folds.size) :
    ∃ (xs : Fin 2 → Concrete.E) (r : Digest32) (rest : List Byte),
      (drawRuns E)[j]? = some ((WireKind.vector 2).codec.bytes xs ++ (WireKind.root.codec.bytes r ++ rest)) ∧
      col.roots[i.val + 1]? = some r ∧ j + 1 < (SpongefishCurrentRoundPackets.openingDraws grinding).length := by
  obtain ⟨pre,post,split,notin,index⟩ := flatMap_index grinding _ (WHIRHistory.schedule_nodup cfg) j _
    (by rw [← openingDraws_eq]; exact found)
  obtain ⟨bpre,bq,bpost,mid,st,fin,rfl,_,_,_,before,step,after⟩ :=
    walk_at H decode grinding lanes root0 E col calls walked _ pre post split
  have count := fold_prefix_count i k last more pre post split notin
  obtain ⟨_,vPre,_,_,⟨rts,rootsPre,rtsLen⟩,_⟩ := before
  obtain ⟨_,_,_,_,_,_,_,_,rootsPush,_,_⟩ := step
  have rootQ : rootFold (.fold i k : Coord p) = true := by simp [rootFold,last,more]
  obtain ⟨b,xs,r,rfl,pushed⟩ := rootsPush rootQ
  obtain ⟨_,_,_,_,⟨rts₂,rootsPost,_⟩,_⟩ := after
  simp only at rootsPre rootsPost pushed
  have midSize : mid.roots.size = i.val + 1 := by
    rw [rootsPre,← count,← rtsLen]
    simp [Collected.start,Nat.add_comm]
  refine ⟨xs,r,leadBytes bpost.flatten,?_,?_,?_⟩
  · have pow : (powDraws grinding (.fold i k : Coord p)).length = 0 := rfl
    rw [index,pow,Nat.add_zero,← vPre]
    simpa [leadBytes] using drawRuns_at bpre.flatten
      (.prover (.vector 2) ((WireKind.vector 2).codec.bytes xs) ::
        .prover .root (WireKind.root.codec.bytes r) :: bpost.flatten) b
  · rw [rootsPost,pushed,Array.getElem?_append_left (by simp [midSize])]
    simp [← midSize]
  · have place := split_position _ pre post split notin
    have pf := CausalPositions.position_fold i k col.tape
    have pq := CausalPositions.position_query i col.tape
    have kq := k.isLt
    have at' := WHIRHistory.schedule_get_position (.query i : Coord p)
    rw [split,List.getElem?_append_right (by omega),
      show position (.query i : Coord p) - pre.length = (position (.query i : Coord p) - pre.length - 1) + 1
        by omega,List.getElem?_cons_succ] at at'
    have queryAfter := List.mem_of_getElem? at'
    have queryDraw : some (.query i : Coord p) ∈ post.flatMap (drawList grinding) := by
      refine List.mem_flatMap.mpr ⟨_,queryAfter,?_⟩
      have width : PCSBCSRounds.rawWidth (.query i : Coord p) ≠ 0 := by
        simp [PCSBCSRounds.rawWidth,WHIRHistory.stackScalarCount,WHIRHistory.scalarCount]
      simp [drawList,pcsDraws,width]
    have positive := List.length_pos_of_mem queryDraw
    have foldDraws : (drawList grinding (.fold i k : Coord p)).length = 1 := rfl
    rw [openingDraws_eq,split,List.flatMap_append,List.flatMap_cons,List.length_append,
      List.length_append,foldDraws]
    rw [index]
    simp only [powDraws,List.length_nil,Nat.add_zero]
    omega

/-- Level roots on the opening frames: for histories whose frame `boundary + k + 1` is the `k`-th draw run (as given by `opening_frames`), every root-carrying fold draw `j'` has a later history whose frame `boundary + j' + 1` decodes, through `SpongefishCurrentRootPolicy.levelRoot`, to the walk's level root `i'+1`. -/
theorem level_roots_of_frames (H : MerkleTransport.Primitive) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) (root0 : Digest32) (E : List SourceEvent)
    (col : Collected p) (calls : List.Forall₂ CallEvent (openingCalls grinding) E)
    (walked : HashProgram.eval H (walk decode grinding lanes root0 E) = some col)
    (boundary : Nat) (histories : List FramedHistory)
    (length : histories.length = (SpongefishCurrentRoundPackets.openingDraws grinding).length)
    (content : ∀ (j : Nat) (h : FramedHistory) (k : Nat) (bytes : List Byte), histories[j]? = some h → k < j →
      (drawRuns E)[k]? = some bytes → ∃ previous, h.frames[boundary + k + 1]? = some (.absorb previous bytes))
    (i' : Fin (cfg).folds.size) (k : Fin (cfg).folds[i'.val]!) (j' : Nat)
    (last : isLastFold i' k = true) (more : i'.val + 1 < (cfg).folds.size)
    (found : (SpongefishCurrentRoundPackets.openingDraws grinding)[j']? = some (some (.fold i' k))) :
    ∃ (root : Digest32) (h : FramedHistory) (previous : Nat) (bytes : List Byte),
      col.roots[i'.val + 1]? = some root ∧ histories[j' + 1]? = some h ∧
      h.frames[boundary + j' + 1]? = some (.absorb previous bytes) ∧
      SpongefishCurrentRootPolicy.levelRoot bytes = some root := by
  obtain ⟨xs,r,rest,run,rootAt,later⟩ :=
    level_root H decode grinding lanes root0 E col calls walked j' i' k found last more
  obtain ⟨h,hAt⟩ : ∃ h, histories[j' + 1]? = some h := ⟨_,List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨previous,frame⟩ := content (j' + 1) h j' _ hAt (by omega) run
  refine ⟨r,h,previous,_,rootAt,hAt,frame,?_⟩
  rw [← List.append_assoc]
  exact SpongefishCurrentRootPolicy.levelRoot_fold_reply xs r rest

#print axioms opening_frames
#print axioms replies_exact_local
#print axioms replies_exact
#print axioms reply_positions
#print axioms reply_at
#print axioms query_reply
#print axioms tape_draw
#print axioms tape_zero
#print axioms seed_draw
#print axioms root_start
#print axioms level_root
#print axioms level_roots_of_frames

end Whir.SpongefishCurrentHistoryReplies
