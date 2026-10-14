import Whir.SpongefishCurrentPrimitiveEventCompiler
import Whir.SpongefishCurrentPhysicalRootCapture

/-! Byte-level current #607 hand-port into the existing public-compression mode
program. This is not Rust/Aeneas equivalence, native acceptance, or FS extraction.
Only output requests use construction coordinates; ordinary public compression
can be composed with the unchanged Program/bind and Mixed.compile interpreters.
The cache stores complete 32-byte replies, not independent 24-byte coins. -/
namespace Whir.SpongefishCurrentMixedModeCompiler
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishCurrentModeQueries
set_option autoImplicit false

deriving instance DecidableEq for Terminal
deriving instance DecidableEq for Coordinate

abbrev seq {A B : Type} := @WHIRModeFinal.bind A B

/-- Everything observed by the source cursor except its unobserved physical CV,
pending block, and output buffer. Transport and reached counters are retained. -/
structure Data where
  pending : Pending
  narg : List Byte
  bytesRead : Nat := 0
  messagesRead : Nat := 0
  hintsRead : Nat := 0
  hints : List (List Byte) := []
  events : List SourceEvent := []

def forget (cur : Cursor) : Data :=
  ⟨cur.pending,cur.narg,cur.bytesRead,cur.messagesRead,cur.hintsRead,cur.hints,cur.events⟩

abbrev Cache := Coordinate → Option Digest32

def GoodCache (c : Compression) (iv : Digest32) (cache : Cache) : Prop :=
  ∀ q d, cache q = some d → d = evalCoordinate c iv q

/-- Certificates concern byte framing and cursors only, never acceptance or C. -/
structure SemanticCursor where
  data : Data
  framed : FrameDomain data.pending
  bounded : data.pending.consumed ≤ maxCursor
  cache : Cache := fun _ => none

def start (cur : Cursor) (framed : FrameDomain cur.pending)
    (bounded : cur.pending.consumed ≤ maxCursor) : SemanticCursor :=
  ⟨forget cur,framed,bounded,fun _ => none⟩

def store (cache : Cache) (q : Coordinate) (d : Digest32) : Cache :=
  fun other => if other = q then some d else cache other

 theorem good_store (c : Compression) (iv : Digest32) (cache : Cache)
    (good : GoodCache c iv cache) (q : Coordinate) :
    GoodCache c iv (store cache q (evalCoordinate c iv q)) := by
  classical
  intro other d h
  unfold store at h
  split at h
  · rename_i equal; subst other; exact Option.some.inj h.symm
  · exact good other d h

/-- A cache miss asks the exact existing construction query. A cache hit reuses
all 32 bytes, including across calls and when a coordinate is repeated. -/
def request (cache : Cache) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) : Program (Cache × Digest32) :=
  match cache q with
  | some d => .done (cache,d)
  | none => .ask (.construction q valid) (fun d => .done (store cache q d,d))

theorem request_real (C : PrimitiveOracle) (iv : Digest32) (cache : Cache)
    (good : GoodCache (compressionOf C) iv cache) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) :
    let result := (runReal C iv (request cache q valid)).view.result
    GoodCache (compressionOf C) iv result.1 ∧ result.2 = evalCoordinate (compressionOf C) iv q := by
  unfold request
  cases found : cache q with
  | none => exact ⟨good_store _ _ _ good q,rfl⟩
  | some d => exact ⟨good,good q d found⟩

theorem request_counted (cache : Cache) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) : Counts (pathCost q) (request cache q valid) := by
  unfold request
  cases cache q with
  | none => exact ⟨Nat.le_refl _,fun _ => trivial⟩
  | some => trivial

 theorem coordinate_cost (m : Pending) (block : Nat) :
    pathCost (coordinate m block) = pathCost (coordinate m 0) := by
  simp [pathCost,DuplexEncoding.plan,coordinate]

/-- Coordinates are close-history plus floor(byte-position/32), not call index. -/
def collect (m : Pending) (positions : List Nat)
    (valid : ∀ p ∈ positions, DuplexEncoding.Admissible (coordinate m (p/32)))
    (cache : Cache) : Program (Cache × List Byte) :=
  match positions with
  | [] => .done (cache,[])
  | p :: ps => seq (request cache (coordinate m (p/32)) (valid p List.mem_cons_self))
      (fun (next,d) => seq (collect m ps (fun j h => valid j (List.mem_cons_of_mem _ h)) next)
        (fun (last,bs) => .done (last,d ⟨p%32,Nat.mod_lt _ (by decide)⟩ :: bs)))

 theorem collect_real (C : PrimitiveOracle) (iv : Digest32) (m : Pending)
    (positions : List Nat)
    (valid : ∀ p ∈ positions, DuplexEncoding.Admissible (coordinate m (p/32)))
    (cache : Cache) (good : GoodCache (compressionOf C) iv cache) :
    let result := (runReal C iv (collect m positions valid cache)).view.result
    GoodCache (compressionOf C) iv result.1 ∧
      result.2 = positions.map (fun p => evalCoordinate (compressionOf C) iv
        (coordinate m (p/32)) ⟨p%32,Nat.mod_lt _ (by decide)⟩) := by
  induction positions generalizing cache with
  | nil => exact ⟨good,rfl⟩
  | cons p ps ih =>
    simp only [collect,seq,WHIRModeFinal.bind_real_result]
    have first := request_real C iv cache good (coordinate m (p/32)) (valid p List.mem_cons_self)
    have tail := ih (fun j h => valid j (List.mem_cons_of_mem _ h)) _ first.1
    exact ⟨tail.1,by simp only [runReal,List.map_cons,first.2,tail.2]⟩

 theorem collect_counted (m : Pending) (positions : List Nat)
    (valid : ∀ p ∈ positions, DuplexEncoding.Admissible (coordinate m (p/32)))
    (cache : Cache) : Counts (positions.length * pathCost (coordinate m 0))
      (collect m positions valid cache) := by
  induction positions generalizing cache with
  | nil => trivial
  | cons p ps ih =>
    have tails : ∀ result : Cache × Digest32,
        Counts (ps.length * pathCost (coordinate m 0))
          (seq (collect m ps (fun j h => valid j (List.mem_cons_of_mem _ h)) result.1)
            (fun (last,bs) => .done (last,result.2 ⟨p%32,Nat.mod_lt _ (by decide)⟩ :: bs))) := by
      intro result
      exact SpongefishCurrentPrimitiveEventCompiler.seq_done_counted _ _ (ih _ result.1)
    simpa only [collect,List.length_cons,Nat.add_mul,Nat.one_mul,coordinate_cost,Nat.add_comm]
      using WHIRModeFinal.bind_counted _ _ (pathCost (coordinate m (p/32)))
        (ps.length * pathCost (coordinate m 0)) (request_counted _ _ _) tails

 def positions (m : Pending) (n : Nat) : List Nat :=
  (List.range n).map (m.consumed + ·)

 theorem positions_valid (m : Pending) (framed : FrameDomain m) (n : Nat)
    (guard : m.consumed + n ≤ maxCursor) :
    ∀ p ∈ positions m n, DuplexEncoding.Admissible (coordinate m (p/32)) := by
  intro p member
  obtain ⟨j,inRange,rfl⟩ := List.mem_map.mp member
  have within := List.mem_range.mp inRange
  apply coordinate_admissible m framed
  simp only [maxCursor] at guard
  omega

 def boundData (cur : SemanticCursor) (bytes : List Byte) : SemanticCursor :=
  {cur with
    data := {cur.data with pending := bind cur.data.pending bytes}
    framed := bind_frame_domain _ _ cur.framed cur.bounded
    bounded := by
      by_cases empty : bytes = []
      · simpa [SpongefishPCSRoundFrames.bind,empty] using cur.bounded
      · simp [SpongefishPCSRoundFrames.bind,empty,maxCursor]}

 def publicProgram (cur : SemanticCursor) (bytes : List Byte) : Program SemanticCursor :=
  .done {boundData cur bytes with data :=
    {(boundData cur bytes).data with events := cur.data.events ++ [.publicBytes bytes]}}

 def readNext (cur : SemanticCursor) (kind : WireKind) (value : kind.Value)
    (rest : List Byte) : SemanticCursor :=
  {boundData cur (kind.codec.bytes value) with data :=
    {(boundData cur (kind.codec.bytes value)).data with
      narg := rest
      bytesRead := cur.data.bytesRead + kind.codec.size
      messagesRead := cur.data.messagesRead + kind.messages
      events := cur.data.events ++ [.prover kind (kind.codec.bytes value)]}}

 def hintNext (cur : SemanticCursor) (bytes : List Byte) (rest : List (List Byte)) : SemanticCursor :=
  {cur with data := {cur.data with
    hints := rest
    hintsRead := cur.data.hintsRead+1
    events := cur.data.events ++ [.hint bytes]}}

 def drawn (cur : SemanticCursor) (n : Nat) (guard : cur.data.pending.consumed+n ≤ maxCursor)
    (cache : Cache) (bytes : List Byte) : SemanticCursor :=
  {data := {cur.data with
      pending := draw cur.data.pending n
      events := cur.data.events ++ [.verifier bytes]}
   framed := draw_frame_domain _ _ cur.framed
   bounded := by
     by_cases zero : n = 0
     · simpa [draw,zero] using cur.bounded
     · simpa [draw,zero] using guard
   cache := cache}

abbrev ReplayError := SpongefishCurrentPrimitiveEventCompiler.ReplayError
abbrev Result := Except (SemanticCursor × ReplayError) SemanticCursor

def eraseResult : Result → Except (Data × ReplayError) Data
  | .ok cur => .ok cur.data
  | .error (cur,e) => .error (cur.data,e)

def forgetResult : SpongefishCurrentPrimitiveEventCompiler.ReplayResult → Except (Data × ReplayError) Data
  | .ok cur => .ok (forget cur)
  | .error (cur,e) => .error (forget cur,e)

/-- Reads are parsed before binding. Failing reads/draws/hints retain the reached
cursor; hints never bind. Guards are precisely the existing source guards. -/
def replayProgram : SemanticCursor → List Call → Program Result
  | cur, [] => .done (.ok cur)
  | cur, .read kind :: calls =>
    match kind.codec.parse cur.data.narg with
    | none => .done (.error (cur,.readRejected kind))
    | some (value,rest) => replayProgram (readNext cur kind value rest) calls
  | cur, .hint :: calls =>
    match cur.data.hints with
    | [] => .done (.error (cur,.missingHint))
    | bytes :: rest => replayProgram (hintNext cur bytes rest) calls
  | cur, .draw g :: calls =>
    if _zero : g.bytes = 0 then
      replayProgram {cur with data := {cur.data with events := cur.data.events ++ [.verifier []]}} calls
    else if guard : cur.data.pending.consumed + g.bytes ≤ maxCursor then
      seq (collect cur.data.pending (positions cur.data.pending g.bytes)
        (positions_valid _ cur.framed _ guard) cur.cache)
        (fun (cache,bytes) => replayProgram (drawn cur g.bytes guard cache bytes) calls)
    else .done (.error (cur,.drawRejected .cursorExhausted))

/-- Explicit physical-byte envelope; old frame boundaries are charged too. -/
def weight (m : Pending) : Nat := (retainedBytes m).length + m.frames.length + 3

 theorem chunks_length (first : Bool) (previous : Nat) (pending bytes : List Byte) :
    (DuplexEncoding.chunks first previous pending bytes).length ≤ bytes.length+1 := by
  induction bytes generalizing first previous pending with
  | nil => simp only [DuplexEncoding.chunks]; split <;> simp
  | cons b bs ih =>
    simp only [DuplexEncoding.chunks,List.length_cons]
    split
    · simp only [List.length_cons]; have := ih false 0 [b]; omega
    · exact Nat.le_trans (ih _ _ _) (by omega)

 theorem path_weight (m : Pending) (block : Nat) : pathCost (coordinate m block) ≤ weight m := by
  have frames : ∀ fs : List ByteFrame,
      (fs.map ByteFrame.historicalCore |>.flatMap DuplexEncoding.framePlan).length ≤
        (fs.flatMap fun f => match f with | .absorb _ bs => bs).length + fs.length := by
    intro fs
    induction fs with
    | nil => simp
    | cons f fs ih =>
      cases f with
      | absorb previous bs =>
        simp only [List.map_cons,List.flatMap_cons,List.length_append,List.length_cons,
          ByteFrame.historicalCore,DuplexEncoding.framePlan] at ih ⊢
        have := chunks_length true previous [] bs
        omega
  have old := frames m.frames
  have closed := frames (close m).frames
  by_cases empty : m.run = []
  · simpa [pathCost,DuplexEncoding.plan,coordinate,close,empty,Pending.core,weight,retainedBytes,
      List.length_append] using (show
        ((m.frames.map ByteFrame.historicalCore).flatMap DuplexEncoding.framePlan).length+2 ≤
          (m.frames.flatMap fun f => match f with | .absorb _ bs => bs).length+m.frames.length+3 by omega)
  · simp only [close,empty,↓reduceIte,List.flatMap_append,List.flatMap_singleton,
      List.length_append,List.length_singleton] at closed
    change
      ((m.frames ++ [ByteFrame.absorb m.previous m.run]).map ByteFrame.historicalCore |>.flatMap
        DuplexEncoding.framePlan).length ≤
      (m.frames.flatMap fun f => match f with | .absorb _ bs => bs).length +
        m.run.length + (m.frames.length+1) at closed
    have bound :
        (((m.frames ++ [ByteFrame.absorb m.previous m.run]).map ByteFrame.historicalCore).flatMap
          DuplexEncoding.framePlan).length+2 ≤
        (m.frames.flatMap fun f => match f with | .absorb _ bs => bs).length+
          m.run.length+m.frames.length+3 := by omega
    simp only [pathCost,DuplexEncoding.plan,coordinate,close,empty,↓reduceIte,Pending.core,
      weight,retainedBytes,List.map_append,List.map_singleton,List.flatMap_append,
      List.flatMap_singleton,List.length_append,List.length_cons] at bound ⊢
    omega

 theorem bind_weight (m : Pending) (bytes : List Byte) :
    weight (bind m bytes) = weight m + bytes.length := by
  rw [weight,bind_retains,List.length_append]
  by_cases empty : bytes = [] <;>
    simp [SpongefishPCSRoundFrames.bind,empty,weight,Nat.add_comm,Nat.add_left_comm]

 theorem draw_weight (m : Pending) (n : Nat) : weight (draw m n) ≤ weight m + 1 := by
  rw [weight,draw_retains]
  by_cases zero : n = 0
  · simp [draw,zero,weight]
  · by_cases empty : m.run = [] <;> simp [draw,zero,close,empty,weight,Nat.add_assoc]

/-- Finite worst-case resource function, based on physical initial bytes/history
and literal call sizes. It overcharges cache hits and rejecting suffixes, but each
miss pays its entire construction path, not merely one squeezed byte. -/
def resource : Nat → List Call → Nat
  | _, [] => 0
  | w, .read kind :: calls => resource (w+kind.codec.size) calls
  | w, .draw g :: calls => g.bytes*w + resource (w+1) calls
  | w, .hint :: calls => resource w calls

 theorem replay_counted (cur : SemanticCursor) (calls : List Call) (w : Nat)
    (cap : weight cur.data.pending ≤ w) : Counts (resource w calls) (replayProgram cur calls) := by
  induction calls generalizing cur w with
  | nil => trivial
  | cons call calls ih =>
    cases call with
    | read kind =>
      simp only [replayProgram]
      cases kind.codec.parse cur.data.narg with
      | none => trivial
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        apply ih
        change weight (bind cur.data.pending (kind.codec.bytes value)) ≤ w+kind.codec.size
        rw [bind_weight]
        simp only [Codec.bytes,List.length_ofFn]
        omega
    | hint =>
      simp only [replayProgram]
      cases cur.data.hints with
      | nil => trivial
      | cons bytes rest => exact ih _ w cap
    | draw g =>
      simp only [replayProgram]
      split
      · apply WHIRModeFinal.counts_mono (ih _ (w+1) (by dsimp; omega))
        simp only [resource]; omega
      · split
        · apply WHIRModeFinal.counts_mono
            (WHIRModeFinal.bind_counted _ _ (g.bytes*w) (resource (w+1) calls) ?_ ?_)
          · exact Nat.le_refl _
          · apply WHIRModeFinal.counts_mono (collect_counted _ _ _ _)
            simp only [positions,List.length_map,List.length_range]
            exact Nat.mul_le_mul_left _ ((path_weight _ 0).trans cap)
          · intro pair
            apply ih
            exact (draw_weight _ _).trans (by omega)
        · trivial


 theorem public_real (C : PrimitiveOracle) (iv : Digest32) (cur : SemanticCursor)
    (actual : Cursor) (same : cur.data = forget actual) (bytes : List Byte) :
    (runReal C iv (publicProgram cur bytes)).view.result.data =
      forget (publicAbsorb (compressionOf C) actual bytes) := by
  simp [publicProgram,runReal,boundData,same,publicAbsorb,forget]

/-- Source representation is an immutable initial precondition, not an
accepted-current-state certificate. No physical CV enters the compiler. -/
 theorem cursor_eq (c : Compression) (iv : Digest32) (actual : Cursor)
    (represented : RepresentsCurrent c iv actual.pending actual.state) :
    actual.state.consumed = actual.pending.consumed :=
  (congrArg State.consumed represented.2.1).trans
    (materialize_consumed c iv actual.pending.core actual.state.output represented.1)

 theorem collect_source (C : PrimitiveOracle) (iv : Digest32) (actual : Cursor)
    (represented : RepresentsCurrent (compressionOf C) iv actual.pending actual.state)
    (framed : FrameDomain actual.pending) (cache : Cache)
    (good : GoodCache (compressionOf C) iv cache) (n : Nat) (positive : n ≠ 0)
    (guard : actual.pending.consumed+n ≤ maxCursor) (state : State) (bytes : List Byte)
    (squeezed : squeeze (compressionOf C) actual.state n = .ok (state,bytes)) :
    let result := (runReal C iv (collect actual.pending (positions actual.pending n)
      (positions_valid _ framed _ guard) cache)).view.result
    GoodCache (compressionOf C) iv result.1 ∧ result.2 = bytes := by
  have h := collect_real C iv actual.pending (positions actual.pending n)
    (positions_valid _ framed _ guard) cache good
  refine ⟨h.1,h.2.trans ?_⟩
  apply List.ext_getElem
  · simp [positions,(squeeze_exact_cursor _ _ _ _ _ squeezed).2]
  · intro j hj hb
    simp only [positions,List.map_map,List.getElem_map,List.getElem_range]
    exact (squeezed_byte _ _ _ _ _ represented n positive bytes squeezed j
      (by simpa [positions] using hj)).symm

/-- Success and rejection both agree with the instrumented actual replay after
erasing only unobserved physical state. The failing cursor and prefix events
and counters are preserved, rather than dropping an error to `none`. -/
theorem replay_real (C : PrimitiveOracle) (iv : Digest32) (cur : SemanticCursor)
    (actual : Cursor) (same : cur.data = forget actual)
    (represented : RepresentsCurrent (compressionOf C) iv actual.pending actual.state)
    (good : GoodCache (compressionOf C) iv cur.cache) (calls : List Call) :
    eraseResult (runReal C iv (replayProgram cur calls)).view.result =
      forgetResult (SpongefishCurrentPrimitiveEventCompiler.actualReplay
        (compressionOf C) actual calls) := by
  induction calls generalizing cur actual with
  | nil => exact congrArg Except.ok same
  | cons call calls ih =>
    have pending : cur.data.pending = actual.pending := congrArg Data.pending same
    have narg : cur.data.narg = actual.narg := congrArg Data.narg same
    have hints : cur.data.hints = actual.hints := congrArg Data.hints same
    have cursor := cursor_eq (compressionOf C) iv actual represented
    cases call with
    | read kind =>
      cases parsed : kind.codec.parse actual.narg with
      | none =>
        simp [replayProgram,parsed,runReal,eraseResult,forgetResult,forget,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,SpongefishPCSRoundFrames.read,same]
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        let next : Cursor := {actual with
          state := absorb (compressionOf C) actual.state (kind.codec.bytes value)
          pending := bind actual.pending (kind.codec.bytes value)
          narg := rest
          bytesRead := actual.bytesRead+kind.codec.size
          messagesRead := actual.messagesRead+kind.messages
          events := actual.events ++ [.prover kind (kind.codec.bytes value)]}
        have h := ih (readNext cur kind value rest) next
          (by simp [readNext,boundData,same,forget,next])
          (bind_bridge _ _ _ _ represented _) good
        simpa [replayProgram,narg,parsed,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,SpongefishPCSRoundFrames.read,next] using h
    | hint =>
      cases transport : actual.hints with
      | nil =>
        simp [replayProgram,transport,runReal,eraseResult,forgetResult,forget,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,takeHint,same]
      | cons bytes rest =>
        let next : Cursor := {actual with
          hints := rest
          hintsRead := actual.hintsRead+1
          events := actual.events ++ [.hint bytes]}
        have h := ih (hintNext cur bytes rest) next
          (by simp [hintNext,same,forget,next]) represented good
        simpa [replayProgram,hints,transport,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,takeHint,next] using h
    | draw g =>
      by_cases zero : g.bytes = 0
      · let next : Cursor := {actual with events := actual.events ++ [.verifier []]}
        have h := ih
          {cur with data := {cur.data with events := cur.data.events ++ [.verifier []]}}
          next (by simp [same,forget,next]) represented good
        simpa [replayProgram,zero,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeeze,draw,next] using h
      · by_cases guard : cur.data.pending.consumed+g.bytes ≤ maxCursor
        · have actualGuard : actual.pending.consumed+g.bytes ≤ maxCursor := by
            simpa only [pending] using guard
          let result := squeezeLoop (compressionOf C) g.bytes (finish (compressionOf C) actual.state)
          have squeezed : squeeze (compressionOf C) actual.state g.bytes = .ok result := by
            simp [squeeze,zero,cursor,actualGuard,result]
          let collected := (runReal C iv (collect cur.data.pending
            (positions cur.data.pending g.bytes)
            (positions_valid _ cur.framed _ guard) cur.cache)).view.result
          have source : GoodCache (compressionOf C) iv collected.1 ∧ collected.2 = result.2 := by
            have h := collect_source C iv actual represented
              (by simpa only [pending] using cur.framed) cur.cache good g.bytes zero
              actualGuard result.1 result.2 squeezed
            simpa only [collected,pending] using h
          let next : Cursor := {actual with
            state := result.1
            pending := draw actual.pending g.bytes
            events := actual.events ++ [.verifier result.2]}
          have h := ih (drawn cur g.bytes guard collected.1 collected.2) next
            (by simp [drawn,same,forget,next,source.2])
            (draw_bridge _ _ _ _ _ represented _ _ squeezed) source.1
          simpa [replayProgram,zero,guard,seq,WHIRModeFinal.bind_real_result,
            SpongefishCurrentPrimitiveEventCompiler.actualReplay,
            SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeezed,next,collected] using h
        · have exhausted : ¬actual.pending.consumed+g.bytes ≤ maxCursor := by
            simpa only [pending] using guard
          simp only [replayProgram,zero,↓reduceDIte,guard,runReal,eraseResult,
            SpongefishCurrentPrimitiveEventCompiler.actualReplay,
            SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeeze,cursor,
            exhausted,↓reduceIte]
          simp only [forgetResult]
          exact congrArg (fun d => Except.error (d,
            SpongefishCurrentPrimitiveEventCompiler.ReplayError.drawRejected .cursorExhausted)) same

theorem source_endpoint (C : PrimitiveOracle) (iv : Digest32) (actual : Cursor)
    (represented : RepresentsCurrent (compressionOf C) iv actual.pending actual.state)
    (framed : FrameDomain actual.pending) (calls : List Call) :
    let cur := start actual framed represented.1.2.2.1
    Counts (resource (weight actual.pending) calls) (replayProgram cur calls) ∧
    eraseResult (runReal C iv (replayProgram cur calls)).view.result =
      forgetResult (SpongefishCurrentPrimitiveEventCompiler.actualReplay
        (compressionOf C) actual calls) ∧
    (runReal C iv (replayProgram cur calls)).primitiveCost ≤
      resource (weight actual.pending) calls := by
  dsimp only
  have counted := replay_counted (start actual framed represented.1.2.2.1) calls
    (weight actual.pending) (Nat.le_refl _)
  exact ⟨counted,replay_real C iv _ actual rfl represented (by intro q d h; cases h) calls,
    runReal_counts C iv _ _ counted⟩

/-- Public binding and ordinary compression use the same existing Program.
These compositional entry points do not introduce a new framing convention. -/
def publicReplayProgram (cur : SemanticCursor) (bytes : List Byte)
    (calls : List Call) : Program Result :=
  seq (publicProgram cur bytes) (fun next => replayProgram next calls)

theorem publicReplay_counted (cur : SemanticCursor) (bytes : List Byte) (calls : List Call) :
    Counts (resource (weight cur.data.pending+bytes.length) calls)
      (publicReplayProgram cur bytes calls) := by
  change Counts _ (replayProgram _ calls)
  apply replay_counted
  change weight (bind cur.data.pending bytes) ≤ weight cur.data.pending+bytes.length
  exact Nat.le_of_eq (bind_weight _ _)

theorem publicReplay_real (C : PrimitiveOracle) (iv : Digest32) (cur : SemanticCursor)
    (actual : Cursor) (same : cur.data = forget actual)
    (represented : RepresentsCurrent (compressionOf C) iv actual.pending actual.state)
    (good : GoodCache (compressionOf C) iv cur.cache) (bytes : List Byte) (calls : List Call) :
    eraseResult (runReal C iv (publicReplayProgram cur bytes calls)).view.result =
      forgetResult (SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C)
        (publicAbsorb (compressionOf C) actual bytes) calls) := by
  unfold publicReplayProgram
  rw [seq,WHIRModeFinal.bind_real_result]
  apply replay_real
  · exact public_real C iv cur actual same bytes
  · exact bind_bridge _ _ _ _ represented _
  · exact good

/-- One ordinary observation can precede any current replay without becoming a
semantic absorb or selecting a fictitious independent verifier round. Its real
answer is the shared public C answer; Counts charges it on every continuation. -/
def ordinaryReplayProgram (input : Node) (cur : SemanticCursor)
    (calls : List Call) : Program Result :=
  seq (SpongefishCurrentPrimitiveEventCompiler.primitive input.cv input.block input.tweak input.last)
    (fun _ => replayProgram cur calls)

theorem ordinaryReplay_counted (input : Node) (cur : SemanticCursor) (calls : List Call) :
    Counts (1+resource (weight cur.data.pending) calls) (ordinaryReplayProgram input cur calls) := by
  exact WHIRModeFinal.bind_counted _ _ 1 _
    (SpongefishCurrentPrimitiveEventCompiler.primitive_certified _ _ _ _).1
    (fun _ => replay_counted cur calls _ (Nat.le_refl _))

theorem ordinaryReplay_real (C : PrimitiveOracle) (iv : Digest32) (input : Node)
    (cur : SemanticCursor) (actual : Cursor) (same : cur.data = forget actual)
    (represented : RepresentsCurrent (compressionOf C) iv actual.pending actual.state)
    (good : GoodCache (compressionOf C) iv cur.cache) (calls : List Call) :
    eraseResult (runReal C iv (ordinaryReplayProgram input cur calls)).view.result =
      forgetResult (SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) actual calls) := by
  simp only [ordinaryReplayProgram,seq,WHIRModeFinal.bind_real_result]
  exact replay_real C iv cur actual same represented good calls

#print axioms publicReplay_real
#print axioms publicReplay_counted
#print axioms ordinaryReplay_real
#print axioms ordinaryReplay_counted

#print axioms source_endpoint
#print axioms replay_counted
#print axioms collect_source

/-- Literal raw construction requests recover current raw32 headers when an
actual header receipt generated the pending run. No saved record is assumed. -/
 theorem header_request {B : Nat} (c : Compression) (iv : Digest32)
    (before header : Cursor) (shape : SpongefishSessionAdapter.Shape) (root : Digest32)
    (received : SpongefishCurrentAnchorHeader.readHeader c before shape = some (header,root))
    (framed : FrameDomain header.pending) (block : Nat) (bounded : block < 2^44)
    (work : pathCost (coordinate header.pending block) ≤ B) :
    SpongefishCurrentAnchorHeader.rawHeader shape iv
      (constructionKey B iv (coordinate header.pending block) work) = some root ∧
    SpongefishCurrentPhysicalRootCapture.recognize shape iv
      (.inr (constructionKey B iv (coordinate header.pending block) work)) =
      some (SpongefishCurrentPhysicalRootCapture.reference shape root) := by
  have valid := coordinate_admissible header.pending framed block bounded
  have facts := SpongefishCurrentAnchorHeader.readHeader_facts c before header shape root received
  have parsed := SpongefishCurrentAnchorHeader.closed_header header.pending shape facts.1 root
    before.pending.run facts.2.2.2.2.2.2
  have raw : SpongefishCurrentAnchorHeader.rawHeader shape iv
      (constructionKey B iv (coordinate header.pending block) work) = some root := by
    rw [SpongefishCurrentAnchorHeader.rawHeader,
      WHIRHeaderRoots.decodeRaw_construction iv _ valid work]
    exact parsed
  exact ⟨raw,SpongefishCurrentPhysicalRootCapture.recognize_rawHeader shape iv _ valid work
    block rfl root raw⟩

/-- No per-query admissibility or Counts premise: header framing is propagated
from the initial source invariants, the byte guard gives the block bound, and
the physical history envelope proves the complete raw path bound internally. -/
theorem header_request_derived (c : Compression) (iv : Digest32)
    (before header : Cursor) (shape : SpongefishSessionAdapter.Shape) (root : Digest32)
    (received : SpongefishCurrentAnchorHeader.readHeader c before shape = some (header,root))
    (represented : RepresentsCurrent c iv before.pending before.state)
    (framed : FrameDomain before.pending) (n j : Nat)
    (guard : header.pending.consumed+n ≤ maxCursor) (within : j < n) :
    let q := coordinate header.pending ((header.pending.consumed+j)/32)
    let work := path_weight header.pending ((header.pending.consumed+j)/32)
    DuplexEncoding.Admissible q ∧
    SpongefishCurrentAnchorHeader.rawHeader shape iv
      (constructionKey (weight header.pending) iv q work) = some root ∧
    SpongefishCurrentPhysicalRootCapture.recognize shape iv
      (.inr (constructionKey (weight header.pending) iv q work)) =
      some (SpongefishCurrentPhysicalRootCapture.reference shape root) := by
  have replay := SpongefishCurrentAnchorHeader.readHeader_replay c before header shape root received
  have propagated := all_round_frame_domain c iv before header
    [.read .scalar,.read .scalar,.read .scalar,.read .root] represented framed replay
  have block : (header.pending.consumed+j)/32 < 2^44 := by
    simp only [maxCursor] at guard
    omega
  exact ⟨coordinate_admissible _ propagated.2 _ block,
    header_request c iv before header shape root received propagated.2 _ block (path_weight _ _)⟩

#print axioms header_request_derived

end Whir.SpongefishCurrentMixedModeCompiler
