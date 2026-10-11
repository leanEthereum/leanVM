import Whir.WHIRCallerPrefix

/-! Public caller-control shapes for the conditional #552 transcript. CPU and recursion callers run layout-shaped reductions before opening. In particular, `flock/src/lincheck.rs:495-517` runs a public number of rounds, then reads each public-sized scalar vector and one scalar without another sample. This module checks the mode-level family for an explicitly fixed public operation shape; it does not claim a universal refinement of the Rust callers. Payload bytes, nonce values and challenge-dependent messages may differ between clones. The original seed is retained and no boundary tag is added to the wire. Distinct public caller shapes may require distinct boundary counts even at the same abstract seed; selecting and binding the public family remains a caller obligation. -/
namespace Whir.WHIRCallerShape
open Concrete FiatShamirGame DuplexRefinement

/-- Raw mode operations, including byte absorptions not divisible by 24. -/
inductive Operation where
  | absorb (bytes : List Byte)
  | squeeze (count : Nat)
  | nonce (bits : Nat) (value : Scalar24)

/-- Only public operation control and lengths remain, never payload bytes. -/
inductive EventShape where
  | absorb (bytes : Nat)
  | squeeze (count : Nat)
  | nonce (bits : Nat)
  deriving DecidableEq, Repr

def operationShape : Operation → EventShape
  | .absorb bs => .absorb bs.length
  | .squeeze n => .squeeze n
  | .nonce bits _ => .nonce bits

def applyOperation (m : Model) : Operation → Model
  | .absorb bs => modelAbsorb m bs
  | .squeeze n => modelSqueeze m n
  | .nonce bits value => modelNonce m value bits

def runOperations (m : Model) (ops : List Operation) : Model :=
  ops.foldl applyOperation m

/-- This records all control-relevant fields of the actual ghost model. -/
structure StateShape where
  frames : Nat
  run : Nat
  previous : Nat
  consumed : Nat
  deriving DecidableEq, Repr

def abstractModel (m : Model) : StateShape :=
  ⟨m.history.frames.length,m.run.length,m.previous,m.consumed⟩

def closeShape (s : StateShape) : StateShape :=
  if s.run = 0 then s else {s with frames := s.frames + 1, run := 0, previous := 0}

def applyShape (s : StateShape) : EventShape → StateShape
  | .absorb n => if n = 0 then s else
      {s with run := s.run + n, previous := if s.consumed = 0 then s.previous else s.consumed, consumed := 0}
  | .squeeze n => if n = 0 then s else {closeShape s with consumed := s.consumed + n}
  | .nonce _ => ⟨(closeShape s).frames + 1,0,0,0⟩

def runShapes (s : StateShape) (events : List EventShape) : StateShape :=
  events.foldl applyShape s

@[simp] theorem abstract_closeRun (m : Model) :
    abstractModel (closeRun m) = closeShape (abstractModel m) := by
  by_cases h : m.run = [] <;>
    simp [closeRun, closeShape, abstractModel, h]

@[simp] theorem abstract_modelAbsorb (m : Model) (bs : List Byte) :
    abstractModel (modelAbsorb m bs) = applyShape (abstractModel m) (.absorb bs.length) := by
  by_cases h : bs = []
  · simp [modelAbsorb, applyShape, abstractModel, h]
  · simp [modelAbsorb, applyShape, abstractModel, h]
    rfl

@[simp] theorem abstract_modelSqueeze (m : Model) (n : Nat) :
    abstractModel (modelSqueeze m n) = applyShape (abstractModel m) (.squeeze n) := by
  by_cases h : n = 0
  · simp [modelSqueeze, applyShape, h]
  · simp only [modelSqueeze, applyShape, h, ↓reduceIte]
    have hc := abstract_closeRun m
    cases hc' : closeRun m
    simp only [hc', abstractModel] at hc ⊢
    rw [← hc]

theorem abstract_modelNonce (m : Model) (bits : Nat) (value : Scalar24) :
    abstractModel (modelNonce m value bits) = applyShape (abstractModel m) (.nonce bits) := by
  simp only [modelNonce, abstractModel, List.length_append, List.length_cons,
    List.length_nil, Nat.zero_add, applyShape]
  exact congrArg (fun s : StateShape => StateShape.mk (s.frames + 1) 0 0 0)
    (abstract_closeRun m)

theorem abstract_applyOperation (m : Model) (op : Operation) :
    abstractModel (applyOperation m op) = applyShape (abstractModel m) (operationShape op) := by
  cases op with
  | absorb bs => exact abstract_modelAbsorb m bs
  | squeeze n => exact abstract_modelSqueeze m n
  | nonce bits value => exact abstract_modelNonce m bits value

theorem abstract_runOperations (m : Model) (ops : List Operation) :
    abstractModel (runOperations m ops) = runShapes (abstractModel m) (ops.map operationShape) := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih =>
    simp only [runOperations, runShapes, List.foldl_cons, List.map_cons] at ih ⊢
    rw [ih, abstract_applyOperation]

/-- Same public shape determines every control field, even from an active run. -/
theorem same_shape (a b : Model) (ops ops' : List Operation)
    (initial : abstractModel a = abstractModel b)
    (control : ops.map operationShape = ops'.map operationShape) :
    abstractModel (runOperations a ops) = abstractModel (runOperations b ops') := by
  rw [abstract_runOperations, abstract_runOperations, initial, control]

def seedModel (domain statement : Digest32) : Model := ⟨⟨domain,statement,[]⟩,[],0,0⟩

def entryCount (shape : List EventShape) : Nat :=
  (closeShape (runShapes ⟨0,0,0,0⟩ shape)).frames

/-- A computed public boundary count, not an assumed fixed-history certificate. -/
theorem normalized_entry_count (domain statement : Digest32) (ops : List Operation) :
    (closeRun (runOperations (seedModel domain statement) ops)).history.frames.length =
      entryCount (ops.map operationShape) := by
  exact congrArg StateShape.frames
    ((abstract_closeRun _).trans (congrArg closeShape (abstract_runOperations _ _)))

theorem cloned_entry_count (domain statement : Digest32) (ops ops' : List Operation)
    (control : ops.map operationShape = ops'.map operationShape) :
    (closeRun (runOperations (seedModel domain statement) ops)).history.frames.length =
      (closeRun (runOperations (seedModel domain statement) ops')).history.frames.length := by
  rw [normalized_entry_count, normalized_entry_count, control]

/-- The existing WHIR scalar event compiler is an instance of raw operations. -/
def ofWHIREvent : WHIRHistory.Event → Operation
  | .observe xs => .absorb (WHIRHistory.scalarBytes xs)
  | .squeeze n => .squeeze n
  | .nonce bits value => .nonce bits (ByteCodec.encodeE value)

@[simp] theorem shape_of_observe (xs : List E) :
    operationShape (ofWHIREvent (.observe xs)) = .absorb (24 * xs.length) := by
  simp [operationShape, ofWHIREvent, WHIRHistory.scalarBytes_length]

@[simp] theorem apply_ofWHIREvent (m : Model) (event : WHIRHistory.Event) :
    applyOperation m (ofWHIREvent event) = WHIRHistory.modelEvent m event := by
  cases event <;> rfl

theorem run_ofWHIREvents (m : Model) (events : List WHIRHistory.Event) :
    runOperations m (events.map ofWHIREvent) = WHIRHistory.modelEvents m events := by
  induction events generalizing m with
  | nil => rfl
  | cons event events ih =>
    simp only [runOperations, WHIRHistory.modelEvents, List.map_cons, List.foldl_cons] at ih ⊢
    rw [apply_ofWHIREvent, ih]

theorem abstract_modelEvents (m : Model) (events : List WHIRHistory.Event) :
    abstractModel (WHIRHistory.modelEvents m events) =
      runShapes (abstractModel m) (events.map (operationShape ∘ ofWHIREvent)) := by
  rw [← run_ofWHIREvents, abstract_runOperations, List.map_map]

theorem normalized_modelEvents_entry_count (domain statement : Digest32)
    (events : List WHIRHistory.Event) :
    (closeRun (WHIRHistory.modelEvents (seedModel domain statement) events)).history.frames.length =
      entryCount (events.map (operationShape ∘ ofWHIREvent)) := by
  rw [← run_ofWHIREvents, normalized_entry_count, List.map_map]

/-- The final nonempty read resets the real cursor, regardless of earlier data. -/
theorem ending_absorb_consumed (c : Compression) (s : State) (bs : List Byte) (nonempty : bs ≠ []) :
    (absorb c s bs).consumed = 0 := absorb_nonempty_cursor c s bs nonempty

theorem ending_scalar_consumed (c : Compression) (s : State) (value : E) :
    (observe c s value).consumed = 0 := by
  apply absorb_nonempty_cursor
  intro h
  have hl := congrArg List.length h
  simp at hl

theorem ending_model_absorb_consumed (m : Model) (ops : List Operation)
    (bs : List Byte) (nonempty : bs ≠ []) :
    (runOperations m (ops ++ [.absorb bs])).consumed = 0 := by
  simp [runOperations, List.foldl_append, applyOperation, modelAbsorb, nonempty]

end Whir.WHIRCallerShape
