import Whir.SpongefishCurrentInitializedMode

/-! Current byte-source compiler retaining the actual record-capture context.
Seed, absorb and finalization CVs are ordinary observed answers; output bytes
are the existing cached construction replies. Only `State.output` is erased
by the physical-state relation. It is deliberately not a full State equality.
Constructor correspondence excludes Rust's empty-instance panic. This is a
source-inspected byte adapter, not a native PCS/Aeneas/knowledge theorem. -/
namespace Whir.SpongefishCurrentPhysicalModeCompiler
open Concrete FiatShamirGame DuplexRefinement DuplexModeGame
open SpongefishSessionAdapter SpongefishPCSRoundFrames SpongefishCurrentModeQueries
set_option autoImplicit false

namespace Semantic
export SpongefishCurrentMixedModeCompiler (Data SemanticCursor Cache GoodCache forget
  readNext hintNext drawn collect positions positions_valid collect_source weight
  bind_weight draw_weight path_weight collect_counted cursor_eq)
end Semantic

abbrev seq {A B : Type} := @WHIRModeFinal.bind A B

structure Cursor where
  semantic : Semantic.SemanticCursor
  physical : State

/-- Equality modulo ONLY the output cache, which is absent from capture. -/
def normalize (s : State) : State := {s with output := zeroDigest}
def SameState (physical actual : State) : Prop := normalize physical = normalize actual

theorem same_consumed (p a : State) (same : SameState p a) : p.consumed = a.consumed := by
  have equal := congrArg State.consumed (show normalize p = normalize a from same)
  exact equal

theorem same_capture (p a : State) (same : SameState p a) : capture p = capture a := by
  change capture (normalize p) = capture (normalize a)
  rw [same]

theorem same_absorb (c : Compression) (p a : State) (same : SameState p a)
    (bytes : List Byte) : SameState (absorb c p bytes) (absorb c a bytes) := by
  unfold SameState normalize at *
  rw [← absorb_setOutput,← absorb_setOutput,same]

theorem same_finish (c : Compression) (p a : State) (same : SameState p a) :
    SameState (finish c p) (finish c a) := by
  have commute (s : State) : normalize (finish c s) = finish c (normalize s) := by
    unfold normalize finish
    split <;> rfl
  unfold SameState at *
  rw [commute,commute,same]

theorem normalize_squeezeLoop (c : Compression) (n : Nat) (s : State) :
    normalize (squeezeLoop c n s).1 = normalize {s with consumed := s.consumed+n} := by
  apply state_ext
  · exact squeezeLoop_cv c n s
  · exact squeezeLoop_pending c n s
  · exact squeezeLoop_first c n s
  · exact squeezeLoop_previous c n s
  · exact squeezeLoop_consumed c n s
  · rfl

theorem same_draw (c : Compression) (p a : State) (same : SameState p a) (n : Nat)
    (counter : Nat) (equal : counter = a.consumed+n) :
    SameState {finish c p with consumed := counter}
      (squeezeLoop c n (finish c a)).1 := by
  unfold SameState
  rw [normalize_squeezeLoop,finish_consumed,← equal]
  exact congrArg (fun s : State => {s with consumed := counter}) (same_finish c p a same)

abbrev ReplayError := SpongefishCurrentPrimitiveEventCompiler.ReplayError
abbrev Result := Except (Cursor × ReplayError) Cursor
abbrev Captured := Semantic.Data × Context
abbrev CapturedResult := Except (Captured × ReplayError) Captured

def captureCursor (cur : Cursor) : Captured := (cur.semantic.data,capture cur.physical)
def captureActual (cur : SpongefishPCSRoundFrames.Cursor) : Captured :=
  (Semantic.forget cur,capture cur.state)

def eraseResult : Result → CapturedResult
  | .ok cur => .ok (captureCursor cur)
  | .error (cur,e) => .error (captureCursor cur,e)

def captureResult : SpongefishCurrentPrimitiveEventCompiler.ReplayResult → CapturedResult
  | .ok cur => .ok (captureActual cur)
  | .error (cur,e) => .error (captureActual cur,e)

/-- Parse and both draw guards precede physical observations. Rejection retains
all reached semantic data and capture fields. Hints leave physical state alone.
The stale physical output field is never used to produce verifier bytes. -/
def replayProgram : Cursor → List Call → Program Result
  | cur, [] => .done (.ok cur)
  | cur, .read kind :: calls =>
    match kind.codec.parse cur.semantic.data.narg with
    | none => .done (.error (cur,.readRejected kind))
    | some (value,rest) =>
      seq (SpongefishCurrentPrimitiveEventCompiler.absorbProgram cur.physical (kind.codec.bytes value))
        (fun state => replayProgram ⟨Semantic.readNext cur.semantic kind value rest,state⟩ calls)
  | cur, .hint :: calls =>
    match cur.semantic.data.hints with
    | [] => .done (.error (cur,.missingHint))
    | bytes :: rest => replayProgram ⟨Semantic.hintNext cur.semantic bytes rest,cur.physical⟩ calls
  | cur, .draw g :: calls =>
    if _zero : g.bytes = 0 then
      replayProgram {cur with semantic := {cur.semantic with data :=
        {cur.semantic.data with events := cur.semantic.data.events ++ [.verifier []]}}} calls
    else if guard : cur.semantic.data.pending.consumed + g.bytes ≤ maxCursor then
      seq (SpongefishCurrentPrimitiveEventCompiler.finishProgram cur.physical) (fun state =>
        seq (Semantic.collect cur.semantic.data.pending
          (Semantic.positions cur.semantic.data.pending g.bytes)
          (Semantic.positions_valid _ cur.semantic.framed _ guard) cur.semantic.cache)
          (fun (cache,bytes) => replayProgram
            ⟨Semantic.drawn cur.semantic g.bytes guard cache bytes,
              {state with consumed := cur.semantic.data.pending.consumed+g.bytes}⟩ calls))
    else .done (.error (cur,.drawRejected .cursorExhausted))

/-- Worst-case work includes ordinary reads/finalization AND every complete
construction path; arbitrary answers and rejecting suffixes are covered. -/
def resource : Nat → List Call → Nat
  | _, [] => 0
  | w, .read kind :: calls => kind.codec.size + resource (w+kind.codec.size) calls
  | w, .draw g :: calls => 1 + g.bytes*w + resource (w+1) calls
  | w, .hint :: calls => resource w calls

theorem replay_counted (cur : Cursor) (calls : List Call) (w : Nat)
    (cap : Semantic.weight cur.semantic.data.pending ≤ w) :
    Counts (resource w calls) (replayProgram cur calls) := by
  induction calls generalizing cur w with
  | nil => trivial
  | cons call calls ih =>
    cases call with
    | read kind =>
      simp only [replayProgram]
      cases kind.codec.parse cur.semantic.data.narg with
      | none => trivial
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        apply WHIRModeFinal.bind_counted _ _ kind.codec.size (resource (w+kind.codec.size) calls)
        · simpa only [Codec.bytes,List.length_ofFn] using
            (SpongefishCurrentPrimitiveEventCompiler.absorbProgram_certified cur.physical
              (kind.codec.bytes value)).1
        · intro state
          apply ih
          change Semantic.weight (bind cur.semantic.data.pending (kind.codec.bytes value)) ≤ w+kind.codec.size
          rw [Semantic.bind_weight]
          simp only [Codec.bytes,List.length_ofFn]
          omega
    | hint =>
      simp only [replayProgram]
      cases cur.semantic.data.hints with
      | nil => trivial
      | cons bytes rest => exact ih _ w cap
    | draw g =>
      simp only [replayProgram]
      split
      · apply WHIRModeFinal.counts_mono (ih _ (w+1) (by dsimp; omega))
        simp only [resource]; omega
      · split
        · simp only [resource,Nat.add_assoc]
          apply WHIRModeFinal.bind_counted _ _ 1 (g.bytes*w+resource (w+1) calls)
          · exact (SpongefishCurrentPrimitiveEventCompiler.finishProgram_certified cur.physical).1
          · intro state
            apply WHIRModeFinal.bind_counted _ _ (g.bytes*w) (resource (w+1) calls)
            · apply WHIRModeFinal.counts_mono (Semantic.collect_counted _ _ _ _)
              simp only [Semantic.positions,List.length_map,List.length_range]
              exact Nat.mul_le_mul_left _ ((Semantic.path_weight _ 0).trans cap)
            · intro pair
              apply ih
              exact (Semantic.draw_weight _ _).trans (by omega)
        · trivial

theorem replay_real (C : PrimitiveOracle) (iv : Digest32) (cur : Cursor)
    (actual : SpongefishPCSRoundFrames.Cursor)
    (same : cur.semantic.data = Semantic.forget actual)
    (physical : SameState cur.physical actual.state)
    (represented : RepresentsCurrent (compressionOf C) iv actual.pending actual.state)
    (good : Semantic.GoodCache (compressionOf C) iv cur.semantic.cache) (calls : List Call) :
    eraseResult (runReal C iv (replayProgram cur calls)).view.result =
      captureResult (SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) actual calls) := by
  induction calls generalizing cur actual with
  | nil => exact congrArg Except.ok (Prod.ext same (same_capture _ _ physical))
  | cons call calls ih =>
    have pending : cur.semantic.data.pending = actual.pending := congrArg (fun d => d.pending) same
    have narg : cur.semantic.data.narg = actual.narg := congrArg (fun d => d.narg) same
    have hints : cur.semantic.data.hints = actual.hints := congrArg (fun d => d.hints) same
    have cursor := Semantic.cursor_eq (compressionOf C) iv actual represented
    have captured : captureCursor cur = captureActual actual := Prod.ext same (same_capture _ _ physical)
    cases call with
    | read kind =>
      cases parsed : kind.codec.parse actual.narg with
      | none =>
        simp [replayProgram,narg,parsed,runReal,eraseResult,captureResult,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,SpongefishPCSRoundFrames.read,captured]
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        let next : SpongefishPCSRoundFrames.Cursor := {actual with
          state := absorb (compressionOf C) actual.state (kind.codec.bytes value)
          pending := bind actual.pending (kind.codec.bytes value)
          narg := rest
          bytesRead := actual.bytesRead+kind.codec.size
          messagesRead := actual.messagesRead+kind.messages
          events := actual.events ++ [.prover kind (kind.codec.bytes value)]}
        have h := ih ⟨Semantic.readNext cur.semantic kind value rest,
            absorb (compressionOf C) cur.physical (kind.codec.bytes value)⟩ next
          (by simp [SpongefishCurrentMixedModeCompiler.readNext,
            SpongefishCurrentMixedModeCompiler.boundData,same,Semantic.forget,next])
          (same_absorb _ _ _ physical _) (bind_bridge _ _ _ _ represented _) good
        simpa [replayProgram,narg,parsed,seq,WHIRModeFinal.bind_real_result,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,SpongefishPCSRoundFrames.read,next] using h
    | hint =>
      cases transport : actual.hints with
      | nil =>
        simp [replayProgram,hints,transport,runReal,eraseResult,captureResult,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,takeHint,captured]
      | cons bytes rest =>
        let next : SpongefishPCSRoundFrames.Cursor := {actual with
          hints := rest, hintsRead := actual.hintsRead+1, events := actual.events ++ [.hint bytes]}
        have h := ih ⟨Semantic.hintNext cur.semantic bytes rest,cur.physical⟩ next
          (by simp [SpongefishCurrentMixedModeCompiler.hintNext,same,Semantic.forget,next]) physical represented good
        simpa [replayProgram,hints,transport,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,takeHint,next] using h
    | draw g =>
      by_cases zero : g.bytes = 0
      · let next : SpongefishPCSRoundFrames.Cursor := {actual with events := actual.events ++ [.verifier []]}
        have h := ih {cur with semantic := {cur.semantic with data :=
            {cur.semantic.data with events := cur.semantic.data.events ++ [.verifier []]}}}
          next (by simp [same,Semantic.forget,next]) physical represented good
        simpa [replayProgram,zero,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeeze,draw,next] using h
      · by_cases guard : cur.semantic.data.pending.consumed+g.bytes ≤ maxCursor
        · have actualGuard : actual.pending.consumed+g.bytes ≤ maxCursor := by simpa only [pending] using guard
          let result := squeezeLoop (compressionOf C) g.bytes (finish (compressionOf C) actual.state)
          have squeezed : squeeze (compressionOf C) actual.state g.bytes = .ok result := by
            simp [squeeze,zero,cursor,actualGuard,result]
          let collected := (runReal C iv (Semantic.collect cur.semantic.data.pending
            (Semantic.positions cur.semantic.data.pending g.bytes)
            (Semantic.positions_valid _ cur.semantic.framed _ guard) cur.semantic.cache)).view.result
          have source : Semantic.GoodCache (compressionOf C) iv collected.1 ∧ collected.2 = result.2 := by
            have h := Semantic.collect_source C iv actual represented
              (by simpa only [pending] using cur.semantic.framed) cur.semantic.cache good g.bytes zero
              actualGuard result.1 result.2 squeezed
            simpa only [collected,pending] using h
          let next : SpongefishPCSRoundFrames.Cursor := {actual with
            state := result.1, pending := draw actual.pending g.bytes,
            events := actual.events ++ [.verifier result.2]}
          have h := ih ⟨Semantic.drawn cur.semantic g.bytes guard collected.1 collected.2,
              {finish (compressionOf C) cur.physical with consumed := cur.semantic.data.pending.consumed+g.bytes}⟩ next
            (by simp [SpongefishCurrentMixedModeCompiler.drawn,same,Semantic.forget,next,source.2])
            (same_draw _ _ _ physical _ _ (by rw [pending,cursor]))
            (draw_bridge _ _ _ _ _ represented _ _ squeezed) source.1
          simpa [replayProgram,zero,guard,seq,WHIRModeFinal.bind_real_result,
            SpongefishCurrentPrimitiveEventCompiler.actualReplay,
            SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeezed,next,collected] using h
        · have exhausted : ¬actual.pending.consumed+g.bytes ≤ maxCursor := by simpa only [pending] using guard
          simp only [replayProgram,zero,↓reduceDIte,guard,runReal,eraseResult,
            SpongefishCurrentPrimitiveEventCompiler.actualReplay,
            SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeeze,cursor,
            exhausted,↓reduceIte,captureResult]
          exact congrArg (fun d => Except.error (d,
            SpongefishCurrentPrimitiveEventCompiler.ReplayError.drawRejected .cursorExhausted)) captured

/-- Initial semantics comes from constructor bytes and the observed session;
physical state comes unchanged from observed setup, never a hidden C call. -/
def initial (actual : SpongefishPCSRoundFrames.Cursor) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) : Cursor :=
  ⟨SpongefishCurrentInitializedMode.initial actual.pending.domain instanceBytes narg hints,actual.state⟩

def program (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) : Program (Option CapturedResult) :=
  seq (SpongefishCurrentObservedSessionEntry.setupProgram parameter tag instanceBytes narg hints)
    (fun result => match result with
      | none => .done none
      | some actual => seq (replayProgram (initial actual instanceBytes narg hints) calls)
          (fun result => .done (some (eraseResult result))))

def budget (tag instanceBytes : List Byte) (calls : List Call) : Nat :=
  SpongefishCurrentObservedSessionEntry.setupBudget tag instanceBytes +
    resource (instanceBytes.length+3) calls

theorem program_counted (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) :
    Counts (budget tag instanceBytes calls) (program parameter tag instanceBytes narg hints calls) := by
  apply WHIRModeFinal.bind_counted _ _
    (SpongefishCurrentObservedSessionEntry.setupBudget tag instanceBytes)
    (resource (instanceBytes.length+3) calls)
    (SpongefishCurrentObservedSessionEntry.setupProgram_certified parameter tag instanceBytes narg hints).1
  intro result
  cases result with
  | none => trivial
  | some actual =>
    exact SpongefishCurrentPrimitiveEventCompiler.seq_done_counted _ _
      (replay_counted _ calls _ (by simp [initial]))

/-- Full Data AND exact actual capture on accepted and rejected cursors. The
representation premise used by the internal induction is derived from setup;
the initialized endpoint needs no external context/representation certificate. -/
theorem program_real (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    (runReal C parameter (program parameter tag instanceBytes narg hints calls)).view.result =
      (SpongefishCurrentObservedSessionEntry.actualEntry (compressionOf C) parameter
        tag instanceBytes narg hints calls).map captureResult := by
  rw [program,seq,WHIRModeFinal.bind_real_result,SpongefishCurrentObservedSessionEntry.setupProgram_real]
  by_cases empty : instanceBytes = []
  · simp [SpongefishCurrentObservedSessionEntry.actualEntry,
      SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty,runReal]
  · simp only [SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty,↓reduceIte,
      Option.map_some,seq,WHIRModeFinal.bind_real_result,runReal]
    have same := replay_real C parameter
      (initial (SpongefishCurrentObservedSessionEntry.cursor (derive (compressionOf C) parameter tag)
        instanceBytes narg hints (absorb (compressionOf C) (init (compressionOf C) parameter
          (derive (compressionOf C) parameter tag)) instanceBytes)) instanceBytes narg hints)
      (SpongefishCurrentObservedSessionEntry.cursor (derive (compressionOf C) parameter tag)
        instanceBytes narg hints (absorb (compressionOf C) (init (compressionOf C) parameter
          (derive (compressionOf C) parameter tag)) instanceBytes))
      (by simp [initial,SpongefishCurrentInitializedMode.initial,
        SpongefishCurrentObservedSessionEntry.cursor,Semantic.forget,SpongefishPCSRoundFrames.bind,empty])
      rfl (session_bridge (compressionOf C) parameter _ instanceBytes)
      (by intro q d found; cases found) calls
    simpa [SpongefishCurrentObservedSessionEntry.actualEntry,
      SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty] using congrArg some same

theorem program_work (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    (runReal C parameter (program parameter tag instanceBytes narg hints calls)).primitiveCost ≤
      budget tag instanceBytes calls :=
  runReal_counts C parameter _ _ (program_counted parameter tag instanceBytes narg hints calls)

#print axioms same_capture
#print axioms replay_real
#print axioms replay_counted
#print axioms program_real
#print axioms program_counted
#print axioms program_work
end Whir.SpongefishCurrentPhysicalModeCompiler
