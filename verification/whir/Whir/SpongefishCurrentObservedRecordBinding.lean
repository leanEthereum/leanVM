import Whir.SpongefishCurrentPhysicalModeCompiler
import Whir.SpongefishCurrentCommitmentReceive

/-! Observed current record binding. The immutable expected record is received
from the source interaction; its context is captured before the header. Field
mismatches retain the cursor AFTER the successful read and absorption.
This hand-port retains the existing canonical codec and decoded-hint assumptions;
it does not model Rust poisoning, native equations, metadata or PoW. -/
namespace Whir.SpongefishCurrentObservedRecordBinding
open Concrete FiatShamirGame DuplexRefinement DuplexModeGame
open SpongefishSessionAdapter SpongefishPCSRoundFrames SpongefishCurrentModeQueries
set_option autoImplicit false

abbrev Physical := SpongefishCurrentPhysicalModeCompiler.Cursor
abbrev Actual := SpongefishPCSRoundFrames.Cursor
abbrev seq {A B : Type} := @WHIRModeFinal.bind A B

/-- Internal induction invariant, not an input to the initialized endpoint. -/
def Linked (C : PrimitiveOracle) (iv : Digest32) (p : Physical) (a : Actual) : Prop :=
  p.semantic.data = SpongefishCurrentMixedModeCompiler.forget a ∧
  SpongefishCurrentPhysicalModeCompiler.SameState p.physical a.state ∧
  RepresentsCurrent (compressionOf C) iv a.pending a.state ∧
  SpongefishCurrentMixedModeCompiler.GoodCache (compressionOf C) iv p.semantic.cache

def LinkedResult (C : PrimitiveOracle) (iv : Digest32) :
    SpongefishCurrentPhysicalModeCompiler.Result →
    SpongefishCurrentPrimitiveEventCompiler.ReplayResult → Prop
  | .ok p, .ok a => Linked C iv p a
  | .error (p,e), .error (a,f) => Linked C iv p a ∧ e = f
  | _, _ => False

theorem replay_linked (C : PrimitiveOracle) (iv : Digest32) (cur : Physical)
    (actual : Actual) (linked : Linked C iv cur actual) (calls : List Call) :
    LinkedResult C iv
      (runReal C iv (SpongefishCurrentPhysicalModeCompiler.replayProgram cur calls)).view.result
      (SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) actual calls) := by
  obtain ⟨same,physical,represented,good⟩ := linked
  induction calls generalizing cur actual with
  | nil => exact ⟨same,physical,represented,good⟩
  | cons call calls ih =>
    have pending : cur.semantic.data.pending = actual.pending := congrArg (fun d => d.pending) same
    have narg : cur.semantic.data.narg = actual.narg := congrArg (fun d => d.narg) same
    have hints : cur.semantic.data.hints = actual.hints := congrArg (fun d => d.hints) same
    have cursor := SpongefishCurrentMixedModeCompiler.cursor_eq (compressionOf C) iv actual represented
    cases call with
    | read kind =>
      cases parsed : kind.codec.parse actual.narg with
      | none =>
        simp only [SpongefishCurrentPhysicalModeCompiler.replayProgram,narg,parsed,runReal,LinkedResult,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,SpongefishPCSRoundFrames.read]
        exact ⟨⟨same,physical,represented,good⟩,rfl⟩
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        let next : Actual := {actual with
          state := absorb (compressionOf C) actual.state (kind.codec.bytes value)
          pending := bind actual.pending (kind.codec.bytes value)
          narg := rest, bytesRead := actual.bytesRead+kind.codec.size,
          messagesRead := actual.messagesRead+kind.messages,
          events := actual.events ++ [.prover kind (kind.codec.bytes value)]}
        have h := ih ⟨SpongefishCurrentMixedModeCompiler.readNext cur.semantic kind value rest,
            absorb (compressionOf C) cur.physical (kind.codec.bytes value)⟩ next
          (by simp [SpongefishCurrentMixedModeCompiler.readNext,
            SpongefishCurrentMixedModeCompiler.boundData,same,SpongefishCurrentMixedModeCompiler.forget,next])
          (SpongefishCurrentPhysicalModeCompiler.same_absorb _ _ _ physical _)
          (bind_bridge _ _ _ _ represented _) good
        simpa [SpongefishCurrentPhysicalModeCompiler.replayProgram,narg,parsed,seq,
          SpongefishCurrentPhysicalModeCompiler.seq,WHIRModeFinal.bind_real_result,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,SpongefishPCSRoundFrames.read,next] using h
    | hint =>
      cases transport : actual.hints with
      | nil =>
        simp only [SpongefishCurrentPhysicalModeCompiler.replayProgram,hints,transport,runReal,LinkedResult,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,takeHint]
        exact ⟨⟨same,physical,represented,good⟩,trivial⟩
      | cons bytes rest =>
        let next : Actual := {actual with
          hints := rest, hintsRead := actual.hintsRead+1, events := actual.events ++ [.hint bytes]}
        have h := ih ⟨SpongefishCurrentMixedModeCompiler.hintNext cur.semantic bytes rest,cur.physical⟩ next
          (by simp [SpongefishCurrentMixedModeCompiler.hintNext,same,
            SpongefishCurrentMixedModeCompiler.forget,next]) physical represented good
        simpa [SpongefishCurrentPhysicalModeCompiler.replayProgram,hints,transport,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,takeHint,next] using h
    | draw g =>
      by_cases zero : g.bytes = 0
      · let next : Actual := {actual with events := actual.events ++ [.verifier []]}
        have h := ih {cur with semantic := {cur.semantic with data :=
            {cur.semantic.data with events := cur.semantic.data.events ++ [.verifier []]}}}
          next (by simp [same,SpongefishCurrentMixedModeCompiler.forget,next]) physical represented good
        simpa [SpongefishCurrentPhysicalModeCompiler.replayProgram,zero,
          SpongefishCurrentPrimitiveEventCompiler.actualReplay,
          SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeeze,draw,next] using h
      · by_cases guard : cur.semantic.data.pending.consumed+g.bytes ≤ maxCursor
        · have actualGuard : actual.pending.consumed+g.bytes ≤ maxCursor := by simpa only [pending] using guard
          let result := squeezeLoop (compressionOf C) g.bytes (finish (compressionOf C) actual.state)
          have squeezed : squeeze (compressionOf C) actual.state g.bytes = .ok result := by
            simp [squeeze,zero,cursor,actualGuard,result]
          let collected := (runReal C iv (SpongefishCurrentMixedModeCompiler.collect cur.semantic.data.pending
            (SpongefishCurrentMixedModeCompiler.positions cur.semantic.data.pending g.bytes)
            (SpongefishCurrentMixedModeCompiler.positions_valid _ cur.semantic.framed _ guard)
            cur.semantic.cache)).view.result
          have source : SpongefishCurrentMixedModeCompiler.GoodCache (compressionOf C) iv collected.1 ∧
              collected.2 = result.2 := by
            have h := SpongefishCurrentMixedModeCompiler.collect_source C iv actual represented
              (by simpa only [pending] using cur.semantic.framed) cur.semantic.cache good g.bytes zero
              actualGuard result.1 result.2 squeezed
            simpa only [collected,pending] using h
          let next : Actual := {actual with
            state := result.1
            pending := draw actual.pending g.bytes
            events := actual.events ++ [.verifier result.2]}
          have h := ih ⟨SpongefishCurrentMixedModeCompiler.drawn cur.semantic g.bytes guard collected.1 collected.2,
              {finish (compressionOf C) cur.physical with consumed := cur.semantic.data.pending.consumed+g.bytes}⟩ next
            (by simp [SpongefishCurrentMixedModeCompiler.drawn,same,
              SpongefishCurrentMixedModeCompiler.forget,next,source.2])
            (SpongefishCurrentPhysicalModeCompiler.same_draw _ _ _ physical _ _ (by rw [pending,cursor]))
            (draw_bridge _ _ _ _ _ represented _ _ squeezed) source.1
          simpa [SpongefishCurrentPhysicalModeCompiler.replayProgram,zero,guard,seq,
            SpongefishCurrentPhysicalModeCompiler.seq,WHIRModeFinal.bind_real_result,
            SpongefishCurrentPrimitiveEventCompiler.actualReplay,
            SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeezed,next,collected] using h
        · have exhausted : ¬actual.pending.consumed+g.bytes ≤ maxCursor := by simpa only [pending] using guard
          simp only [SpongefishCurrentPhysicalModeCompiler.replayProgram,zero,↓reduceDIte,guard,runReal,
            SpongefishCurrentPrimitiveEventCompiler.actualReplay,
            SpongefishCurrentPrimitiveEventCompiler.actualCall,squeezeGroup,squeeze,cursor,
            exhausted,↓reduceIte,LinkedResult]
          exact ⟨⟨same,physical,represented,good⟩,rfl⟩

inductive Error where
  | replay (error : SpongefishCurrentPrimitiveEventCompiler.ReplayError)
  | invalidShape
  | fieldMismatch (kind : WireKind)
  | anchorDecode

abbrev Step (S : Type) (A : Type) := Except (S × Error) (S × A)

def StepLinked {A : Type} (C : PrimitiveOracle) (iv : Digest32) :
    Step Physical A → Step Actual A → Prop
  | .ok (p,x), .ok (a,y) => Linked C iv p a ∧ x = y
  | .error (p,e), .error (a,f) => Linked C iv p a ∧ e = f
  | _, _ => False

def chain {S A B : Type} (p : Step S A) (next : S → A → Step S B) : Step S B :=
  match p with
  | .error e => .error e
  | .ok (s,a) => next s a

def chainProgram {A B : Type} (p : Program (Step Physical A))
    (next : Physical → A → Program (Step Physical B)) : Program (Step Physical B) :=
  seq p (fun result => match result with
    | .error e => .done (.error e)
    | .ok (s,a) => next s a)

theorem chain_linked {A B : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program (Step Physical A)) (a : Step Actual A)
    (next : Physical → A → Program (Step Physical B)) (actualNext : Actual → A → Step Actual B)
    (before : StepLinked C iv (runReal C iv p).view.result a)
    (after : ∀ p a x, Linked C iv p a →
      StepLinked C iv (runReal C iv (next p x)).view.result (actualNext a x)) :
    StepLinked C iv (runReal C iv (chainProgram p next)).view.result (chain a actualNext) := by
  rw [chainProgram,seq,WHIRModeFinal.bind_real_result]
  cases hp : (runReal C iv p).view.result with
  | error e =>
    cases a with
    | error f => simpa [hp,chain,runReal,StepLinked] using before
    | ok pair => simp [hp,StepLinked] at before
  | ok pair =>
    obtain ⟨p,x⟩ := pair
    cases a with
    | error e => simp [hp,StepLinked] at before
    | ok pair =>
      obtain ⟨a,y⟩ := pair
      have h : Linked C iv p a ∧ x = y := by simpa [hp,StepLinked] using before
      simpa [hp,chain,← h.2] using after p a x h.1

/-- Decode before any observed absorb, retaining the typed value. -/
def readProgram (cur : Physical) (kind : WireKind) : Program (Step Physical kind.Value) :=
  match kind.codec.parse cur.semantic.data.narg with
  | none => .done (.error (cur,.replay (.readRejected kind)))
  | some (value,rest) =>
    seq (SpongefishCurrentPrimitiveEventCompiler.absorbProgram cur.physical (kind.codec.bytes value))
      (fun state => .done (.ok
        (⟨SpongefishCurrentMixedModeCompiler.readNext cur.semantic kind value rest,state⟩,value)))

def actualRead (c : Compression) (cur : Actual) (kind : WireKind) : Step Actual kind.Value :=
  match SpongefishPCSRoundFrames.read c cur kind with
  | none => .error (cur,.replay (.readRejected kind))
  | some pair => .ok pair

theorem read_linked (C : PrimitiveOracle) (iv : Digest32) (cur : Physical) (actual : Actual)
    (linked : Linked C iv cur actual) (kind : WireKind) :
    StepLinked C iv (runReal C iv (readProgram cur kind)).view.result
      (actualRead (compressionOf C) actual kind) := by
  obtain ⟨same,physical,represented,good⟩ := linked
  have narg : cur.semantic.data.narg = actual.narg := congrArg (fun d => d.narg) same
  cases parsed : kind.codec.parse actual.narg with
  | none =>
    simp only [readProgram,narg,actualRead,SpongefishPCSRoundFrames.read,parsed,runReal,StepLinked]
    exact ⟨⟨same,physical,represented,good⟩,rfl⟩
  | some pair =>
    obtain ⟨value,rest⟩ := pair
    simp only [readProgram,narg,parsed,seq,WHIRModeFinal.bind_real_result,
      SpongefishCurrentPrimitiveEventCompiler.absorbProgram_real,runReal,
      actualRead,SpongefishPCSRoundFrames.read,StepLinked,Linked]
    refine ⟨⟨?_,SpongefishCurrentPhysicalModeCompiler.same_absorb _ _ _ physical _,
      bind_bridge _ _ _ _ represented _,good⟩,rfl⟩
    simp [SpongefishCurrentMixedModeCompiler.readNext,
      SpongefishCurrentMixedModeCompiler.boundData,same,SpongefishCurrentMixedModeCompiler.forget]

/-- Comparison is deliberately in the read's continuation, not a preflight. -/
def verifyFieldsProgram : Physical → List SpongefishRecordBindingParser.Message →
    Program (Step Physical Unit)
  | cur, [] => .done (.ok (cur,()))
  | cur, message :: rest =>
    chainProgram (readProgram cur message.1) (fun next value =>
      if message.1.codec.bytes value = message.bytes then verifyFieldsProgram next rest
      else .done (.error (next,.fieldMismatch message.1)))

def actualVerifyFields (c : Compression) : Actual → List SpongefishRecordBindingParser.Message →
    Step Actual Unit
  | cur, [] => .ok (cur,())
  | cur, message :: rest =>
    chain (actualRead c cur message.1) (fun next value =>
      if message.1.codec.bytes value = message.bytes then actualVerifyFields c next rest
      else .error (next,.fieldMismatch message.1))

theorem verifyFields_linked (C : PrimitiveOracle) (iv : Digest32) (cur : Physical)
    (actual : Actual) (linked : Linked C iv cur actual) (fields : List SpongefishRecordBindingParser.Message) :
    StepLinked C iv (runReal C iv (verifyFieldsProgram cur fields)).view.result
      (actualVerifyFields (compressionOf C) actual fields) := by
  induction fields generalizing cur actual with
  | nil => exact ⟨linked,rfl⟩
  | cons message fields ih =>
    apply chain_linked _ _ _ _ _ _ (read_linked C iv cur actual linked message.1)
    intro p a value h
    split
    · exact ih p a h
    · exact ⟨h,rfl⟩

/-- Erasing diagnostic reached cursors recovers the existing current parser. -/
theorem actualVerifyFields_erases (c : Compression) (cur : Actual)
    (fields : List SpongefishRecordBindingParser.Message) :
    (actualVerifyFields c cur fields).toOption.map Prod.fst =
      SpongefishRecordBindingParser.verifyFields c cur fields := by
  induction fields generalizing cur with
  | nil => rfl
  | cons message fields ih =>
    simp only [actualVerifyFields,actualRead,SpongefishRecordBindingParser.verifyFields,
      SpongefishRecordBindingParser.checkedRead]
    cases SpongefishPCSRoundFrames.read c cur message.1 with
    | none => rfl
    | some pair =>
      obtain ⟨next,value⟩ := pair
      simp only [chain]
      split
      · exact ih next
      · rfl

/-- Values come directly from cached construction replies; the ordinary
finalization answer alone updates the captured CV. -/
def drawProgram (cur : Physical) (g : Group) : Program (Step Physical (List Byte)) :=
  if _zero : g.bytes = 0 then
    .done (.ok ({cur with semantic := {cur.semantic with data :=
      {cur.semantic.data with events := cur.semantic.data.events ++ [.verifier []]}}},[]))
  else if guard : cur.semantic.data.pending.consumed+g.bytes ≤ maxCursor then
    seq (SpongefishCurrentPrimitiveEventCompiler.finishProgram cur.physical) (fun state =>
      seq (SpongefishCurrentMixedModeCompiler.collect cur.semantic.data.pending
        (SpongefishCurrentMixedModeCompiler.positions cur.semantic.data.pending g.bytes)
        (SpongefishCurrentMixedModeCompiler.positions_valid _ cur.semantic.framed _ guard) cur.semantic.cache)
        (fun (cache,bytes) => .done (.ok
          (⟨SpongefishCurrentMixedModeCompiler.drawn cur.semantic g.bytes guard cache bytes,
            {state with consumed := cur.semantic.data.pending.consumed+g.bytes}⟩,bytes))))
  else .done (.error (cur,.replay (.drawRejected .cursorExhausted)))

def actualDraw (c : Compression) (cur : Actual) (g : Group) : Step Actual (List Byte) :=
  match squeezeGroup c cur g with
  | .error e => .error (cur,.replay (.drawRejected e))
  | .ok pair => .ok pair

theorem draw_linked (C : PrimitiveOracle) (iv : Digest32) (cur : Physical) (actual : Actual)
    (linked : Linked C iv cur actual) (g : Group) :
    StepLinked C iv (runReal C iv (drawProgram cur g)).view.result
      (actualDraw (compressionOf C) actual g) := by
  obtain ⟨same,physical,represented,good⟩ := linked
  have pending : cur.semantic.data.pending = actual.pending := congrArg (fun d => d.pending) same
  have cursor := SpongefishCurrentMixedModeCompiler.cursor_eq (compressionOf C) iv actual represented
  by_cases zero : g.bytes = 0
  · simp only [drawProgram,zero,↓reduceDIte,runReal,actualDraw,squeezeGroup,squeeze,
      ↓reduceIte,draw,StepLinked,Linked]
    exact ⟨⟨by simp [same,SpongefishCurrentMixedModeCompiler.forget],physical,represented,good⟩,rfl⟩
  · by_cases guard : cur.semantic.data.pending.consumed+g.bytes ≤ maxCursor
    · have actualGuard : actual.pending.consumed+g.bytes ≤ maxCursor := by simpa only [pending] using guard
      let result := squeezeLoop (compressionOf C) g.bytes (finish (compressionOf C) actual.state)
      have squeezed : squeeze (compressionOf C) actual.state g.bytes = .ok result := by
        simp [squeeze,zero,cursor,actualGuard,result]
      let collected := (runReal C iv (SpongefishCurrentMixedModeCompiler.collect cur.semantic.data.pending
        (SpongefishCurrentMixedModeCompiler.positions cur.semantic.data.pending g.bytes)
        (SpongefishCurrentMixedModeCompiler.positions_valid _ cur.semantic.framed _ guard)
        cur.semantic.cache)).view.result
      have source : SpongefishCurrentMixedModeCompiler.GoodCache (compressionOf C) iv collected.1 ∧
          collected.2 = result.2 := by
        have h := SpongefishCurrentMixedModeCompiler.collect_source C iv actual represented
          (by simpa only [pending] using cur.semantic.framed) cur.semantic.cache good g.bytes zero
          actualGuard result.1 result.2 squeezed
        simpa only [collected,pending] using h
      simp only [drawProgram,zero,↓reduceDIte,guard,seq,WHIRModeFinal.bind_real_result,
        SpongefishCurrentPrimitiveEventCompiler.finishProgram_real,actualDraw,squeezeGroup,
        squeezed,runReal,StepLinked,Linked]
      refine ⟨⟨?_,?_,draw_bridge _ _ _ _ _ represented _ _ squeezed,source.1⟩,source.2⟩
      · change (SpongefishCurrentMixedModeCompiler.drawn cur.semantic g.bytes guard
          collected.1 collected.2).data =
          SpongefishCurrentMixedModeCompiler.forget {actual with
            state := result.1
            pending := draw actual.pending g.bytes
            events := actual.events ++ [.verifier result.2]}
        simp only [SpongefishCurrentMixedModeCompiler.drawn,source.2,same,
          SpongefishCurrentMixedModeCompiler.forget]
      · exact SpongefishCurrentPhysicalModeCompiler.same_draw _ _ _ physical _ _ (by rw [pending,cursor])
    · have exhausted : ¬actual.pending.consumed+g.bytes ≤ maxCursor := by simpa only [pending] using guard
      simp only [drawProgram,zero,↓reduceDIte,guard,runReal,actualDraw,squeezeGroup,
        squeeze,cursor,exhausted,↓reduceIte,StepLinked]
      exact ⟨⟨same,physical,represented,good⟩,rfl⟩

def receiveProgram (cur : Physical) (shape : Shape) : Program (Step Physical Record) :=
  if ¬shape.Valid then .done (.error (cur,.invalidShape)) else
    chainProgram
      (verifyFieldsProgram cur (SpongefishRecordBindingParser.scalarMessages
        (constants AnchoredHeaderCodec.anchorMarker shape))) (fun header _ =>
      chainProgram (readProgram header .root) (fun header root =>
      chainProgram (drawProgram header (.anchor (shape.logN-1))) (fun sampled bytes =>
        match (vectorCodec shape.logN).parse bytes with
        | none => .done (.error (sampled,.anchorDecode))
        | some (point,rest) =>
          if rest ≠ [] then .done (.error (sampled,.anchorDecode)) else
          chainProgram (readProgram sampled .scalar) (fun next value =>
            .done (.ok (next,{shape,root,context := capture cur.physical,point := List.ofFn point,value}))))))

def actualReceive (c : Compression) (cur : Actual) (shape : Shape) : Step Actual Record :=
  if ¬shape.Valid then .error (cur,.invalidShape) else
    chain (actualVerifyFields c cur (SpongefishRecordBindingParser.scalarMessages
      (constants AnchoredHeaderCodec.anchorMarker shape))) (fun header _ =>
    chain (actualRead c header .root) (fun header root =>
    chain (actualDraw c header (.anchor (shape.logN-1))) (fun sampled bytes =>
      match (vectorCodec shape.logN).parse bytes with
      | none => .error (sampled,.anchorDecode)
      | some (point,rest) =>
        if rest ≠ [] then .error (sampled,.anchorDecode) else
        chain (actualRead c sampled .scalar) (fun next value =>
          .ok (next,{shape,root,context := capture cur.state,point := List.ofFn point,value})))))

theorem receive_linked (C : PrimitiveOracle) (iv : Digest32) (cur : Physical) (actual : Actual)
    (linked : Linked C iv cur actual) (shape : Shape) :
    StepLinked C iv (runReal C iv (receiveProgram cur shape)).view.result
      (actualReceive (compressionOf C) actual shape) := by
  unfold receiveProgram actualReceive
  split
  · exact ⟨linked,rfl⟩
  · apply chain_linked _ _ _ _ _ _ (verifyFields_linked C iv cur actual linked _)
    intro p a _ h
    apply chain_linked _ _ _ _ _ _ (read_linked C iv p a h .root)
    intro p a root h
    apply chain_linked _ _ _ _ _ _ (draw_linked C iv p a h _)
    intro p a bytes h
    cases (vectorCodec shape.logN).parse bytes with
    | none => exact ⟨h,rfl⟩
    | some pair =>
      obtain ⟨point,rest⟩ := pair
      dsimp only
      split
      · exact ⟨h,rfl⟩
      · apply chain_linked _ _ _ _ _ _ (read_linked C iv p a h .scalar)
        intro p a value h
        exact ⟨h,congrArg (fun context => ({shape,root,context,point := List.ofFn point,value} : Record))
          (SpongefishCurrentPhysicalModeCompiler.same_capture _ _ linked.2.1)⟩

theorem chain_toOption {S A B : Type} (p : Step S A) (next : S → A → Step S B) :
    (chain p next).toOption = p.toOption.bind (fun (s,x) => (next s x).toOption) := by
  cases p <;> rfl

theorem actualRead_toOption (c : Compression) (cur : Actual) (kind : WireKind) :
    (actualRead c cur kind).toOption = SpongefishPCSRoundFrames.read c cur kind := by
  unfold actualRead
  cases SpongefishPCSRoundFrames.read c cur kind <;> rfl

theorem actualDraw_toOption (c : Compression) (cur : Actual) (g : Group) :
    (actualDraw c cur g).toOption = (squeezeGroup c cur g).toOption := by
  unfold actualDraw
  cases squeezeGroup c cur g <;> rfl

theorem actualVerifyFields_toOption (c : Compression) (cur : Actual)
    (fields : List SpongefishRecordBindingParser.Message) :
    (actualVerifyFields c cur fields).toOption =
      (SpongefishRecordBindingParser.verifyFields c cur fields).map (fun next => (next,())) := by
  have h := actualVerifyFields_erases c cur fields
  cases result : actualVerifyFields c cur fields with
  | error e => simpa [result,Except.toOption] using congrArg (Option.map (fun next => (next,()))) h
  | ok pair =>
    obtain ⟨next,u⟩ := pair
    cases u
    simpa [result,Except.toOption] using congrArg (Option.map (fun next => (next,()))) h

theorem actualReceive_erases (c : Compression) (cur : Actual) (shape : Shape) :
    (actualReceive c cur shape).toOption = SpongefishCurrentCommitmentReceive.receive c cur shape := by
  unfold actualReceive SpongefishCurrentCommitmentReceive.receive SpongefishCurrentAnchorHeader.readHeader
  dsimp only [Bind.bind,Option.bind]
  by_cases invalid : ¬shape.Valid
  · simp [invalid,Except.toOption]
  · simp only [invalid,↓reduceIte,chain_toOption,actualVerifyFields_toOption]
    cases fields : SpongefishRecordBindingParser.verifyFields c cur
      (SpongefishRecordBindingParser.scalarMessages (constants AnchoredHeaderCodec.anchorMarker shape)) with
    | none => rfl
    | some header =>
      dsimp only [Option.map,Option.bind]
      unfold actualRead
      cases readRoot : SpongefishPCSRoundFrames.read c header .root with
      | none => dsimp only [Except.toOption]
      | some pair =>
        obtain ⟨header,root⟩ := pair
        dsimp only [Except.toOption,Option.bind]
        unfold actualDraw
        cases drawn : squeezeGroup c header (.anchor (shape.logN-1)) with
        | error e => dsimp only [Except.toOption]
        | ok pair =>
          obtain ⟨sampled,bytes⟩ := pair
          dsimp only [Except.toOption,Option.bind]
          cases decoded : (vectorCodec shape.logN).parse bytes with
          | none => dsimp only [Except.toOption]
          | some pair =>
            obtain ⟨point,rest⟩ := pair
            dsimp only [Option.bind]
            by_cases nonempty : rest ≠ []
            · simp_all
            · simp only [nonempty,↓reduceIte]
              unfold chain
              cases SpongefishPCSRoundFrames.read c sampled .scalar <;> dsimp only [Except.toOption,Pure.pure]

def replayStage (cur : Physical) (calls : List Call) : Program (Step Physical Unit) :=
  seq (SpongefishCurrentPhysicalModeCompiler.replayProgram cur calls) (fun result =>
    .done (match result with
      | .error (next,e) => .error (next,.replay e)
      | .ok next => .ok (next,())))

def actualReplayStage (c : Compression) (cur : Actual) (calls : List Call) : Step Actual Unit :=
  match SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur calls with
  | .error (next,e) => .error (next,.replay e)
  | .ok next => .ok (next,())

theorem replayStage_linked (C : PrimitiveOracle) (iv : Digest32) (cur : Physical) (actual : Actual)
    (linked : Linked C iv cur actual) (calls : List Call) :
    StepLinked C iv (runReal C iv (replayStage cur calls)).view.result
      (actualReplayStage (compressionOf C) actual calls) := by
  have h := replay_linked C iv cur actual linked calls
  simp only [replayStage,seq,WHIRModeFinal.bind_real_result,actualReplayStage]
  cases p : (runReal C iv (SpongefishCurrentPhysicalModeCompiler.replayProgram cur calls)).view.result <;>
    cases a : SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) actual calls <;>
    simp [p,a,LinkedResult,StepLinked,runReal] at h ⊢
  · exact h
  · exact h

/-- The prefix and payload are literal source Call lists, not synthetic tape
certificates. The record passed to expected-field verification is the received
record, including the observed pre-header context and complete anchor point. -/
def bodyProgram (cur : Physical) (shape : Shape) (preCalls middle : List Call) :
    Program (Step Physical Record) :=
  chainProgram (replayStage cur preCalls) (fun pre _ =>
  chainProgram (receiveProgram pre shape) (fun received record =>
  chainProgram (replayStage received middle) (fun payload _ =>
  chainProgram (verifyFieldsProgram payload (SpongefishRecordBindingParser.messages record)) (fun next _ =>
    .done (.ok (next,record))))))

def actualBody (c : Compression) (cur : Actual) (shape : Shape) (preCalls middle : List Call) :
    Step Actual Record :=
  chain (actualReplayStage c cur preCalls) (fun pre _ =>
  chain (actualReceive c pre shape) (fun received record =>
  chain (actualReplayStage c received middle) (fun payload _ =>
  chain (actualVerifyFields c payload (SpongefishRecordBindingParser.messages record)) (fun next _ =>
    .ok (next,record)))))

theorem body_linked (C : PrimitiveOracle) (iv : Digest32) (cur : Physical) (actual : Actual)
    (linked : Linked C iv cur actual) (shape : Shape) (preCalls middle : List Call) :
    StepLinked C iv (runReal C iv (bodyProgram cur shape preCalls middle)).view.result
      (actualBody (compressionOf C) actual shape preCalls middle) := by
  apply chain_linked _ _ _ _ _ _ (replayStage_linked C iv cur actual linked preCalls)
  intro p a _ h
  apply chain_linked _ _ _ _ _ _ (receive_linked C iv p a h shape)
  intro p a record h
  apply chain_linked _ _ _ _ _ _ (replayStage_linked C iv p a h middle)
  intro p a _ h
  apply chain_linked _ _ _ _ _ _ (verifyFields_linked C iv p a h _)
  intro p a _ h
  exact ⟨h,rfl⟩

def captureStep {S A B : Type} (f : S → B) : Step S A → Step B A
  | .error (cur,e) => .error (f cur,e)
  | .ok (cur,x) => .ok (f cur,x)

theorem linked_capture {A : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Step Physical A) (a : Step Actual A) (h : StepLinked C iv p a) :
    captureStep SpongefishCurrentPhysicalModeCompiler.captureCursor p =
      captureStep SpongefishCurrentPhysicalModeCompiler.captureActual a := by
  cases p with
  | error pair =>
    obtain ⟨p,e⟩ := pair
    cases a with
    | ok pair => contradiction
    | error pair =>
      obtain ⟨a,f⟩ := pair
      obtain ⟨⟨same,physical,_,_⟩,equal⟩ := h
      cases equal
      exact congrArg (fun cur => Except.error (cur,e))
        (Prod.ext same (SpongefishCurrentPhysicalModeCompiler.same_capture _ _ physical))
  | ok pair =>
    obtain ⟨p,x⟩ := pair
    cases a with
    | error pair => contradiction
    | ok pair =>
      obtain ⟨a,y⟩ := pair
      obtain ⟨⟨same,physical,_,_⟩,equal⟩ := h
      cases equal
      exact congrArg (fun cur => Except.ok (cur,x))
        (Prod.ext same (SpongefishCurrentPhysicalModeCompiler.same_capture _ _ physical))

def program (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (shape : Shape) (preCalls middle : List Call) :
    Program (Option (Step SpongefishCurrentPhysicalModeCompiler.Captured Record)) :=
  seq (SpongefishCurrentObservedSessionEntry.setupProgram parameter tag instanceBytes narg hints)
    (fun result => match result with
      | none => .done none
      | some actual =>
        seq (bodyProgram (SpongefishCurrentPhysicalModeCompiler.initial actual instanceBytes narg hints)
          shape preCalls middle) (fun result =>
            .done (some (captureStep SpongefishCurrentPhysicalModeCompiler.captureCursor result))))

def actualEntry (c : Compression) (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (shape : Shape) (preCalls middle : List Call) :=
  (SpongefishCurrentObservedSessionEntry.actualSetup c parameter tag instanceBytes narg hints).map
    (fun cur => captureStep SpongefishCurrentPhysicalModeCompiler.captureActual
      (actualBody c cur shape preCalls middle))

theorem program_real (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (shape : Shape)
    (preCalls middle : List Call) :
    (runReal C parameter (program parameter tag instanceBytes narg hints shape preCalls middle)).view.result =
      actualEntry (compressionOf C) parameter tag instanceBytes narg hints shape preCalls middle := by
  rw [program,seq,WHIRModeFinal.bind_real_result,SpongefishCurrentObservedSessionEntry.setupProgram_real]
  by_cases empty : instanceBytes = []
  · simp [actualEntry,SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty,runReal]
  · simp only [SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty,↓reduceIte,
      Option.map_some,seq,WHIRModeFinal.bind_real_result,runReal]
    let actual := SpongefishCurrentObservedSessionEntry.cursor (derive (compressionOf C) parameter tag)
      instanceBytes narg hints (absorb (compressionOf C) (init (compressionOf C) parameter
        (derive (compressionOf C) parameter tag)) instanceBytes)
    have linked : Linked C parameter
        (SpongefishCurrentPhysicalModeCompiler.initial actual instanceBytes narg hints) actual := by
      refine ⟨?_,rfl,session_bridge (compressionOf C) parameter _ instanceBytes,?_⟩
      · simp [SpongefishCurrentPhysicalModeCompiler.initial,SpongefishCurrentInitializedMode.initial,
          actual,SpongefishCurrentObservedSessionEntry.cursor,SpongefishCurrentMixedModeCompiler.forget,
          SpongefishPCSRoundFrames.bind,empty]
      · intro q d found
        cases found
    have h := linked_capture C parameter _ _ (body_linked C parameter _ actual linked shape preCalls middle)
    simpa [actualEntry,SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty,actual]
      using congrArg some h

/-- Syntactic postconditions quantify over EVERY oracle answer, not only C. -/
def Returns {A : Type} (P : A → Prop) : Program A → Prop
  | .done a => P a
  | .ask _ next => ∀ answer, Returns P (next answer)

theorem returns_all {A : Type} (p : Program A) : Returns (fun _ => True) p := by
  induction p with
  | done => trivial
  | ask q next ih => exact ih

theorem returns_mono {A : Type} (p : Program A) (P Q : A → Prop)
    (h : Returns P p) (imp : ∀ a, P a → Q a) : Returns Q p := by
  induction p with
  | done a => exact imp a h
  | ask q next ih => exact fun d => ih d (h d)

theorem returns_seq {A B : Type} (p : Program A) (next : A → Program B)
    (P : A → Prop) (Q : B → Prop) (before : Returns P p)
    (after : ∀ a, P a → Returns Q (next a)) : Returns Q (seq p next) := by
  induction p with
  | done a => exact after a before
  | ask q cont ih => exact fun d => ih d (before d)

theorem seq_counted_returns {A B : Type} (p : Program A) (next : A → Program B)
    (P : A → Prop) (a b : Nat) (counted : Counts a p) (post : Returns P p)
    (after : ∀ r, P r → Counts b (next r)) : Counts (a+b) (seq p next) := by
  induction p generalizing a with
  | done r => exact WHIRModeFinal.counts_mono (after r post) (by omega)
  | ask q cont ih =>
    refine ⟨by have := counted.1; omega,fun d => ?_⟩
    have h := ih d (a-q.cost) (counted.2 d) (post d)
    have equal : a+b-q.cost = (a-q.cost)+b := by have := counted.1; omega
    simpa only [equal] using h

def Envelope (w : Nat) (cur : Physical) : Prop :=
  SpongefishCurrentMixedModeCompiler.weight cur.semantic.data.pending ≤ w ∧ cur.physical.pending.size ≤ 64

def StepEnvelope {A : Type} (w : Nat) : Step Physical A → Prop
  | .error (p,_) => Envelope w p
  | .ok (p,_) => Envelope w p

def replayCursor : SpongefishCurrentPhysicalModeCompiler.Result → Physical
  | .error (p,_) => p
  | .ok p => p

def growth : List Call → Nat
  | [] => 0
  | .read kind :: calls => kind.codec.size + growth calls
  | .draw _ :: calls => 1 + growth calls
  | .hint :: calls => growth calls

theorem envelope_mono (p : Physical) (a b : Nat) (h : Envelope a p) (le : a ≤ b) : Envelope b p :=
  ⟨h.1.trans le,h.2⟩

theorem absorb_returns (s : State) (bytes : List Byte) (bounded : s.pending.size ≤ 64) :
    Returns (fun t => t.pending.size ≤ 64)
      (SpongefishCurrentPrimitiveEventCompiler.absorbProgram s bytes) := by
  induction bytes generalizing s with
  | nil => exact bounded
  | cons b bs ih =>
    apply returns_seq _ _ (fun t => t.pending.size ≤ 64) _
    · unfold SpongefishCurrentPrimitiveEventCompiler.absorbByteProgram
      split <;> dsimp only <;> split
      all_goals
        first
        | exact fun _ => by dsimp only [Returns,WHIRModeFinal.bind]; simp
        | simp only [Returns,Array.size_push]; omega
    · intro t h
      exact ih t h

theorem finish_returns (s : State) (bounded : s.pending.size ≤ 64) :
    Returns (fun t => t.pending.size ≤ 64)
      (SpongefishCurrentPrimitiveEventCompiler.finishProgram s) := by
  unfold SpongefishCurrentPrimitiveEventCompiler.finishProgram
  split
  · exact bounded
  · intro d
    dsimp only [Returns,WHIRModeFinal.bind]
    simp

theorem read_returns (cur : Physical) (w : Nat) (h : Envelope w cur) (kind : WireKind) :
    Returns (StepEnvelope (w+kind.codec.size)) (readProgram cur kind) := by
  unfold readProgram
  cases kind.codec.parse cur.semantic.data.narg with
  | none => exact envelope_mono cur _ _ h (by omega)
  | some pair =>
    obtain ⟨value,rest⟩ := pair
    apply returns_seq _ _ (fun t => t.pending.size ≤ 64) _ (absorb_returns _ _ h.2)
    intro t bounded
    refine ⟨?_,bounded⟩
    change SpongefishCurrentMixedModeCompiler.weight
      (bind cur.semantic.data.pending (kind.codec.bytes value)) ≤ w+kind.codec.size
    rw [SpongefishCurrentMixedModeCompiler.bind_weight]
    simp only [Codec.bytes,List.length_ofFn]
    exact Nat.add_le_add_right h.1 _

theorem draw_returns (cur : Physical) (w : Nat) (h : Envelope w cur) (g : Group) :
    Returns (StepEnvelope (w+1)) (drawProgram cur g) := by
  unfold drawProgram
  split
  · exact envelope_mono cur _ _ h (by omega)
  · split
    · apply returns_seq _ _ (fun t => t.pending.size ≤ 64) _ (finish_returns _ h.2)
      intro t bounded
      apply returns_seq _ _ (fun _ => True) _ (returns_all _)
      intro pair _
      exact ⟨(SpongefishCurrentMixedModeCompiler.draw_weight _ _).trans
        (Nat.add_le_add_right h.1 1),bounded⟩
    · exact envelope_mono cur _ _ h (by omega)

def fieldsSize (fields : List SpongefishRecordBindingParser.Message) : Nat :=
  (fields.map fun m => m.1.codec.size).sum

theorem read_counted (cur : Physical) (kind : WireKind) :
    Counts kind.codec.size (readProgram cur kind) := by
  unfold readProgram
  cases kind.codec.parse cur.semantic.data.narg with
  | none => trivial
  | some pair =>
    exact SpongefishCurrentPrimitiveEventCompiler.seq_done_counted _ _
      (by simpa only [Codec.bytes,List.length_ofFn] using
        (SpongefishCurrentPrimitiveEventCompiler.absorbProgram_certified cur.physical
          (kind.codec.bytes pair.1)).1)

theorem verifyFields_counted (cur : Physical) (fields : List SpongefishRecordBindingParser.Message) :
    Counts (fieldsSize fields) (verifyFieldsProgram cur fields) := by
  induction fields generalizing cur with
  | nil => trivial
  | cons message fields ih =>
    apply WHIRModeFinal.bind_counted _ _ message.1.codec.size (fieldsSize fields) (read_counted _ _)
    intro result
    cases result with
    | error e => trivial
    | ok pair =>
      dsimp only
      split
      · exact ih pair.1
      · trivial

theorem verifyFields_returns (cur : Physical) (w : Nat) (h : Envelope w cur)
    (fields : List SpongefishRecordBindingParser.Message) :
    Returns (StepEnvelope (w+fieldsSize fields)) (verifyFieldsProgram cur fields) := by
  induction fields generalizing cur w with
  | nil => exact h
  | cons message fields ih =>
    apply returns_seq _ _ (StepEnvelope (w+message.1.codec.size)) _ (read_returns _ _ h _)
    intro result bounded
    cases result with
    | error e =>
      exact envelope_mono e.1 _ _ bounded (by simp only [fieldsSize,List.map_cons,List.sum_cons]; omega)
    | ok pair =>
      dsimp only
      split
      · simpa only [fieldsSize,List.map_cons,List.sum_cons,Nat.add_assoc] using ih pair.1 _ bounded
      · exact envelope_mono pair.1 _ _ bounded (by simp only [fieldsSize,List.map_cons,List.sum_cons]; omega)

theorem draw_counted (cur : Physical) (w : Nat) (h : Envelope w cur) (g : Group) :
    Counts (1+g.bytes*w) (drawProgram cur g) := by
  unfold drawProgram
  split
  · trivial
  · split
    · apply WHIRModeFinal.bind_counted _ _ 1 (g.bytes*w)
        (SpongefishCurrentPrimitiveEventCompiler.finishProgram_certified _).1
      intro state
      apply SpongefishCurrentPrimitiveEventCompiler.seq_done_counted
      apply WHIRModeFinal.counts_mono (SpongefishCurrentMixedModeCompiler.collect_counted _ _ _ _)
      simp only [SpongefishCurrentMixedModeCompiler.positions,List.length_map,List.length_range]
      exact Nat.mul_le_mul_left _ ((SpongefishCurrentMixedModeCompiler.path_weight _ 0).trans h.1)
    · trivial

theorem replay_returns (cur : Physical) (w : Nat) (h : Envelope w cur) (calls : List Call) :
    Returns (fun result => Envelope (w+growth calls) (replayCursor result))
      (SpongefishCurrentPhysicalModeCompiler.replayProgram cur calls) := by
  induction calls generalizing cur w with
  | nil => exact h
  | cons call calls ih =>
    cases call with
    | read kind =>
      simp only [SpongefishCurrentPhysicalModeCompiler.replayProgram]
      cases cur.semantic.data.narg |> kind.codec.parse with
      | none => exact envelope_mono _ _ _ h (by simp only [growth]; omega)
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        apply returns_seq _ _ (fun t => t.pending.size ≤ 64) _ (absorb_returns _ _ h.2)
        intro state bounded
        have next : Envelope (w+kind.codec.size)
            ⟨SpongefishCurrentMixedModeCompiler.readNext cur.semantic kind value rest,state⟩ := by
          refine ⟨?_,bounded⟩
          change SpongefishCurrentMixedModeCompiler.weight
            (bind cur.semantic.data.pending (kind.codec.bytes value)) ≤ w+kind.codec.size
          rw [SpongefishCurrentMixedModeCompiler.bind_weight]
          simpa only [Codec.bytes,List.length_ofFn] using Nat.add_le_add_right h.1 kind.codec.size
        simpa only [growth,Nat.add_assoc] using ih _ _ next
    | hint =>
      simp only [SpongefishCurrentPhysicalModeCompiler.replayProgram]
      cases cur.semantic.data.hints with
      | nil => exact envelope_mono _ _ _ h (by simp only [growth]; omega)
      | cons bytes rest => exact ih _ w h
    | draw g =>
      simp only [SpongefishCurrentPhysicalModeCompiler.replayProgram]
      split
      · have next : Envelope (w+1) {cur with semantic := {cur.semantic with data :=
            {cur.semantic.data with events := cur.semantic.data.events ++ [.verifier []]}}} :=
          ⟨h.1.trans (by omega),h.2⟩
        simpa only [growth,Nat.add_assoc] using ih _ _ next
      · split
        · apply returns_seq _ _ (fun t => t.pending.size ≤ 64) _ (finish_returns _ h.2)
          intro state bounded
          apply returns_seq _ _ (fun _ => True) _ (returns_all _)
          intro pair _
          have next : Envelope (w+1)
              ⟨SpongefishCurrentMixedModeCompiler.drawn cur.semantic g.bytes (by assumption) pair.1 pair.2,
                {state with consumed := cur.semantic.data.pending.consumed+g.bytes}⟩ :=
            ⟨(SpongefishCurrentMixedModeCompiler.draw_weight _ _).trans
              (Nat.add_le_add_right h.1 1),bounded⟩
          simpa only [growth,Nat.add_assoc] using ih _ _ next
        · exact envelope_mono _ _ _ h (by simp only [growth]; omega)

theorem replayStage_returns (cur : Physical) (w : Nat) (h : Envelope w cur) (calls : List Call) :
    Returns (StepEnvelope (w+growth calls)) (replayStage cur calls) := by
  apply returns_seq _ _ (fun result => Envelope (w+growth calls) (replayCursor result)) _
    (replay_returns cur w h calls)
  intro result bounded
  cases result <;> exact bounded

theorem replayStage_counted (cur : Physical) (w : Nat) (h : Envelope w cur) (calls : List Call) :
    Counts (SpongefishCurrentPhysicalModeCompiler.resource w calls) (replayStage cur calls) :=
  SpongefishCurrentPrimitiveEventCompiler.seq_done_counted _ _
    (SpongefishCurrentPhysicalModeCompiler.replay_counted cur calls w h.1)

theorem header_fieldsSize (shape : Shape) :
    fieldsSize (SpongefishRecordBindingParser.scalarMessages
      (constants AnchoredHeaderCodec.anchorMarker shape)) = 72 := rfl

def receiveBudget (w : Nat) (shape : Shape) : Nat :=
  72 + (32 + ((1+(Group.anchor (shape.logN-1)).bytes*(w+104))+24))

theorem chain_done_counted {A B : Type} (p : Program (Step Physical A))
    (f : Physical → A → Step Physical B) (a : Nat) (h : Counts a p) :
    Counts a (chainProgram p (fun cur x => .done (f cur x))) := by
  unfold chainProgram
  apply WHIRModeFinal.counts_mono (WHIRModeFinal.bind_counted _ _ a 0 h ?_) (by omega)
  intro result
  cases result <;> trivial

theorem receive_counted (cur : Physical) (w : Nat) (h : Envelope w cur) (shape : Shape) :
    Counts (receiveBudget w shape) (receiveProgram cur shape) := by
  unfold receiveProgram
  split
  · trivial
  · apply seq_counted_returns _ _ (StepEnvelope (w+72)) 72
      (32+((1+(Group.anchor (shape.logN-1)).bytes*(w+104))+24))
      (by simpa only [header_fieldsSize] using (verifyFields_counted cur
        (SpongefishRecordBindingParser.scalarMessages (constants AnchoredHeaderCodec.anchorMarker shape))))
      (by simpa only [header_fieldsSize] using (verifyFields_returns cur w h
        (SpongefishRecordBindingParser.scalarMessages (constants AnchoredHeaderCodec.anchorMarker shape))))
    intro result bounded
    cases result with
    | error e => trivial
    | ok pair =>
      dsimp only
      apply seq_counted_returns _ _ (StepEnvelope (w+72+32)) 32
        ((1+(Group.anchor (shape.logN-1)).bytes*(w+104))+24)
        (read_counted _ .root) (read_returns _ _ bounded .root)
      intro result bounded
      cases result with
      | error e => trivial
      | ok pair =>
        dsimp only
        apply WHIRModeFinal.bind_counted _ _ (1+(Group.anchor (shape.logN-1)).bytes*(w+104)) 24
          (draw_counted _ _ bounded _)
        intro result
        cases result with
        | error e => trivial
        | ok pair =>
          dsimp only
          cases (vectorCodec shape.logN).parse pair.2 with
          | none => trivial
          | some value =>
            dsimp only
            split
            · trivial
            · exact chain_done_counted _ _ 24 (read_counted _ .scalar)

def ReceivePost (w : Nat) (shape : Shape) : Step Physical Record → Prop
  | .error (p,_) => Envelope w p
  | .ok (p,r) => Envelope w p ∧ r.shape = shape ∧ r.context.pending.length ≤ 64 ∧
      r.point.length = shape.logN

theorem receive_returns (cur : Physical) (w : Nat) (h : Envelope w cur) (shape : Shape) :
    Returns (ReceivePost (w+129) shape) (receiveProgram cur shape) := by
  unfold receiveProgram
  split
  · exact envelope_mono _ _ _ h (by omega)
  · apply returns_seq _ _ (StepEnvelope (w+72)) _
      (by simpa only [header_fieldsSize] using (verifyFields_returns cur w h
        (SpongefishRecordBindingParser.scalarMessages (constants AnchoredHeaderCodec.anchorMarker shape))))
    intro result bounded
    cases result with
    | error e => exact envelope_mono _ _ _ bounded (by omega)
    | ok pair =>
      dsimp only
      apply returns_seq _ _ (StepEnvelope (w+72+32)) _ (read_returns _ _ bounded .root)
      intro result bounded
      cases result with
      | error e => exact envelope_mono _ _ _ bounded (by omega)
      | ok pair =>
        dsimp only
        apply returns_seq _ _ (StepEnvelope (w+72+32+1)) _ (draw_returns _ _ bounded _)
        intro result bounded
        cases result with
        | error e => exact envelope_mono _ _ _ bounded (by omega)
        | ok pair =>
          dsimp only
          cases (vectorCodec shape.logN).parse pair.2 with
          | none => exact envelope_mono _ _ _ bounded (by omega)
          | some value =>
            dsimp only
            split
            · exact envelope_mono _ _ _ bounded (by omega)
            · apply returns_seq _ _ (StepEnvelope (w+72+32+1+24)) _ (read_returns _ _ bounded .scalar)
              intro result bounded
              cases result with
              | error e => exact envelope_mono _ _ _ bounded (by omega)
              | ok pair =>
                refine ⟨envelope_mono _ _ _ bounded (by omega),rfl,?_,List.length_ofFn⟩
                simpa only [capture,Array.length_toList] using h.2

theorem fieldsSize_bytes (fields : List SpongefishRecordBindingParser.Message) :
    fieldsSize fields = (fields.flatMap SpongefishRecordBindingParser.Message.bytes).length := by
  induction fields with
  | nil => rfl
  | cons m fields ih =>
    simpa only [fieldsSize,List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,
      SpongefishRecordBindingParser.Message.bytes,Codec.bytes,List.length_ofFn] using congrArg (m.1.codec.size+·) ih

def openingBudget (shape : Shape) : Nat := 208+24*(3+shape.logN)

theorem opening_counted (cur : Physical) (record : Record) (shape : Shape)
    (_same : record.shape = shape) (pending : record.context.pending.length ≤ 64)
    (point : record.point.length = shape.logN) :
    Counts (openingBudget shape) (verifyFieldsProgram cur (SpongefishRecordBindingParser.messages record)) := by
  apply WHIRModeFinal.counts_mono (verifyFields_counted _ _)
  rw [fieldsSize_bytes,SpongefishRecordBindingParser.messages_bytes,openingBytes_length,point]
  have chunks : (record.context.pending.length+23)/24 ≤ 3 := by omega
  unfold openingBudget
  omega

def bodyBudget (w : Nat) (shape : Shape) (preCalls middle : List Call) : Nat :=
  SpongefishCurrentPhysicalModeCompiler.resource w preCalls +
    (receiveBudget (w+growth preCalls) shape +
      (SpongefishCurrentPhysicalModeCompiler.resource (w+growth preCalls+129) middle + openingBudget shape))

theorem body_counted (cur : Physical) (w : Nat) (h : Envelope w cur) (shape : Shape)
    (preCalls middle : List Call) : Counts (bodyBudget w shape preCalls middle)
      (bodyProgram cur shape preCalls middle) := by
  apply seq_counted_returns _ _ (StepEnvelope (w+growth preCalls))
    (SpongefishCurrentPhysicalModeCompiler.resource w preCalls)
    (receiveBudget (w+growth preCalls) shape +
      (SpongefishCurrentPhysicalModeCompiler.resource (w+growth preCalls+129) middle + openingBudget shape))
    (replayStage_counted _ _ h _) (replayStage_returns _ _ h _)
  intro result bounded
  cases result with
  | error e => trivial
  | ok pair =>
    dsimp only
    apply seq_counted_returns _ _ (ReceivePost (w+growth preCalls+129) shape)
      (receiveBudget (w+growth preCalls) shape)
      (SpongefishCurrentPhysicalModeCompiler.resource (w+growth preCalls+129) middle + openingBudget shape)
      (receive_counted _ _ bounded _) (receive_returns _ _ bounded _)
    intro result received
    cases result with
    | error e => trivial
    | ok pair =>
      dsimp only
      obtain ⟨bounded,same,pending,point⟩ := received
      apply WHIRModeFinal.bind_counted _ _
        (SpongefishCurrentPhysicalModeCompiler.resource (w+growth preCalls+129) middle) (openingBudget shape)
        (replayStage_counted _ _ bounded _)
      intro result
      cases result with
      | error e => trivial
      | ok payload =>
        dsimp only
        exact chain_done_counted _ _ (openingBudget shape)
          (opening_counted payload.1 pair.2 shape same pending point)

def SetupPost : Option Actual → Prop
  | none => True
  | some cur => cur.state.pending.size ≤ 64

theorem setup_returns (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) :
    Returns SetupPost
      (SpongefishCurrentObservedSessionEntry.setupProgram parameter tag instanceBytes narg hints) := by
  unfold SpongefishCurrentObservedSessionEntry.setupProgram
  split
  · trivial
  · apply returns_seq _ _ (fun _ => True) _ (returns_all _)
    intro session _
    apply returns_seq _ _ (fun cur : Actual => cur.state.pending.size ≤ 64) _
    · unfold SpongefishCurrentObservedSessionEntry.sessionProgram
      apply returns_seq _ _ (fun s => s.pending.size ≤ 64) _
      · intro cv
        simp [Returns,WHIRModeFinal.bind]
      · intro s bounded
        apply returns_seq _ _ (fun s => s.pending.size ≤ 64) _ (absorb_returns _ _ bounded)
        intro t ht
        exact ht
    · intro cur bounded
      exact bounded

def budget (tag instanceBytes : List Byte) (shape : Shape) (preCalls middle : List Call) : Nat :=
  SpongefishCurrentObservedSessionEntry.setupBudget tag instanceBytes +
    bodyBudget (instanceBytes.length+3) shape preCalls middle

theorem program_counted (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (shape : Shape) (preCalls middle : List Call) :
    Counts (budget tag instanceBytes shape preCalls middle)
      (program parameter tag instanceBytes narg hints shape preCalls middle) := by
  apply seq_counted_returns _ _ SetupPost
    (SpongefishCurrentObservedSessionEntry.setupBudget tag instanceBytes)
    (bodyBudget (instanceBytes.length+3) shape preCalls middle)
    (SpongefishCurrentObservedSessionEntry.setupProgram_certified parameter tag instanceBytes narg hints).1
    (setup_returns parameter tag instanceBytes narg hints)
  intro result bounded
  cases result with
  | none => trivial
  | some actual =>
    apply SpongefishCurrentPrimitiveEventCompiler.seq_done_counted
    apply body_counted
    exact ⟨by simp [SpongefishCurrentPhysicalModeCompiler.initial],bounded⟩

theorem program_work (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (shape : Shape)
    (preCalls middle : List Call) :
    (runReal C parameter (program parameter tag instanceBytes narg hints shape preCalls middle)).primitiveCost ≤
      budget tag instanceBytes shape preCalls middle :=
  runReal_counts C parameter _ _ (program_counted parameter tag instanceBytes narg hints shape preCalls middle)

def sourceBody (c : Compression) (cur : Actual) (shape : Shape) (preCalls middle : List Call) :
    Option (Actual × Record) := do
  let pre ← (SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur preCalls).toOption
  let (received,record) ← SpongefishCurrentCommitmentReceive.receive c pre shape
  let payload ← (SpongefishCurrentPrimitiveEventCompiler.actualReplay c received middle).toOption
  let next ← SpongefishRecordBindingParser.verify c payload record
  pure (next,record)

theorem actualReplayStage_toOption (c : Compression) (cur : Actual) (calls : List Call) :
    (actualReplayStage c cur calls).toOption =
      (SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur calls).toOption.map (fun next => (next,())) := by
  unfold actualReplayStage
  cases SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur calls <;> rfl

/-- All rejection paths erase to the existing receive and expected-record
verification; the stronger initialized equality also preserves diagnostics. -/
theorem actualBody_erases (c : Compression) (cur : Actual) (shape : Shape) (preCalls middle : List Call) :
    (actualBody c cur shape preCalls middle).toOption = sourceBody c cur shape preCalls middle := by
  unfold actualBody sourceBody
  dsimp only [Bind.bind,Option.bind]
  rw [chain_toOption,actualReplayStage_toOption]
  cases (SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur preCalls).toOption with
  | none => rfl
  | some pre =>
    dsimp only [Option.map,Option.bind]
    rw [chain_toOption,actualReceive_erases]
    cases SpongefishCurrentCommitmentReceive.receive c pre shape with
    | none => rfl
    | some pair =>
      obtain ⟨received,record⟩ := pair
      dsimp only [Option.bind]
      rw [chain_toOption,actualReplayStage_toOption]
      cases (SpongefishCurrentPrimitiveEventCompiler.actualReplay c received middle).toOption with
      | none => rfl
      | some payload =>
        dsimp only [Option.map,Option.bind]
        rw [chain_toOption,actualVerifyFields_toOption]
        unfold SpongefishRecordBindingParser.verify
        cases SpongefishRecordBindingParser.verifyFields c payload (SpongefishRecordBindingParser.messages record) <;> rfl

theorem captureStep_toOption {S A B : Type} (f : S → B) (result : Step S A) :
    (captureStep f result).toOption = result.toOption.map (fun (cur,x) => (f cur,x)) := by
  cases result <;> rfl

def sourceEntry (c : Compression) (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (shape : Shape) (preCalls middle : List Call) :
    Option (SpongefishCurrentPhysicalModeCompiler.Captured × Record) :=
  (SpongefishCurrentObservedSessionEntry.actualSetup c parameter tag instanceBytes narg hints).bind
    (fun cur => (sourceBody c cur shape preCalls middle).map
      (fun (next,record) => (SpongefishCurrentPhysicalModeCompiler.captureActual next,record)))

theorem program_source (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (shape : Shape)
    (preCalls middle : List Call) :
    ((runReal C parameter (program parameter tag instanceBytes narg hints shape preCalls middle)).view.result.bind
      (fun result => result.toOption)) =
      sourceEntry (compressionOf C) parameter tag instanceBytes narg hints shape preCalls middle := by
  rw [program_real]
  unfold actualEntry sourceEntry
  cases SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) parameter tag instanceBytes narg hints with
  | none => rfl
  | some cur =>
    dsimp only [Option.map,Option.bind]
    rw [captureStep_toOption,actualBody_erases]
    cases sourceBody (compressionOf C) cur shape preCalls middle with
    | none => rfl
    | some pair => cases pair; rfl

/-- The saved context is recovered from a genuine received record, not assumed
as a supplied record/context equality. No whole native verifier is asserted. -/
theorem sourceBody_accepted (c : Compression) (cur next : Actual) (shape : Shape)
    (preCalls middle : List Call) (record : Record)
    (accepted : sourceBody c cur shape preCalls middle = some (next,record)) :
    ∃ pre received payload,
      SpongefishCurrentPrimitiveEventCompiler.actualReplay c cur preCalls = .ok pre ∧
      SpongefishCurrentCommitmentReceive.receive c pre shape = some (received,record) ∧
      SpongefishCurrentPrimitiveEventCompiler.actualReplay c received middle = .ok payload ∧
      SpongefishRecordBindingParser.verify c payload record = some next ∧
      record.context = capture pre.state := by
  unfold sourceBody at accepted
  obtain ⟨pre,preRun,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨received,saved⟩,receivedRun,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨payload,payloadRun,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨after,verifyRun,equal⟩ := Option.bind_eq_some_iff.mp accepted
  have pairEq : (after,saved) = (next,record) := Option.some.inj equal
  cases pairEq
  have replay_ok (result : SpongefishCurrentPrimitiveEventCompiler.ReplayResult) (a : Actual)
      (h : result.toOption = some a) : result = .ok a := by
    cases result with
    | error e => contradiction
    | ok b => exact congrArg Except.ok (Option.some.inj h)
  exact ⟨pre,received,payload,replay_ok _ _ preRun,receivedRun,replay_ok _ _ payloadRun,
    verifyRun,(SpongefishCurrentCommitmentReceive.receive_retains c pre received shape record receivedRun).2.1⟩

/-- An accepted observed composition exposes the actual source setup, prefix,
receive, payload and expected-record verification, with derived saved context. -/
theorem program_accepted (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (shape : Shape)
    (preCalls middle : List Call) (snapshot : SpongefishCurrentPhysicalModeCompiler.Captured)
    (record : Record)
    (accepted : (runReal C parameter
      (program parameter tag instanceBytes narg hints shape preCalls middle)).view.result =
        some (.ok (snapshot,record))) :
    ∃ initial pre received payload next,
      SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) parameter
        tag instanceBytes narg hints = some initial ∧
      SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial preCalls = .ok pre ∧
      SpongefishCurrentCommitmentReceive.receive (compressionOf C) pre shape = some (received,record) ∧
      SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) received middle = .ok payload ∧
      SpongefishRecordBindingParser.verify (compressionOf C) payload record = some next ∧
      snapshot = SpongefishCurrentPhysicalModeCompiler.captureActual next ∧
      record.context = capture pre.state := by
  have source := program_source C parameter tag instanceBytes narg hints shape preCalls middle
  rw [accepted] at source
  have reached : sourceEntry (compressionOf C) parameter tag instanceBytes narg hints shape preCalls middle =
      some (snapshot,record) := source.symm
  unfold sourceEntry at reached
  obtain ⟨initial,setup,mapped⟩ := Option.bind_eq_some_iff.mp reached
  obtain ⟨⟨next,saved⟩,body,pairEq⟩ := Option.map_eq_some_iff.mp mapped
  have savedEq : saved = record := congrArg Prod.snd pairEq
  subst saved
  obtain ⟨pre,received,payload,preRun,receivedRun,payloadRun,verifyRun,context⟩ :=
    sourceBody_accepted (compressionOf C) initial next shape preCalls middle record body
  exact ⟨initial,pre,received,payload,next,setup,preRun,receivedRun,payloadRun,verifyRun,
    (congrArg Prod.fst pairEq).symm,context⟩

#print axioms program_accepted

#print axioms program_source
#print axioms sourceBody_accepted

#print axioms program_real
#print axioms program_counted
#print axioms program_work
#print axioms actualReceive_erases
#print axioms actualVerifyFields_erases

end Whir.SpongefishCurrentObservedRecordBinding
