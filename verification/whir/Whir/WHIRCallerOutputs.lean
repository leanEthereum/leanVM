import Whir.WHIRCallerShape

/-! Prior caller outputs are real compression queries at strict history prefixes. Their count is bounded by the public caller shape, not by compression path length: a consumed cursor is encoded data and can name many output blocks. No oracle table is exposed by this enumeration; a resolver must obtain these particular answers through its global cache. -/
namespace Whir.WHIRCallerOutputs
open Concrete FiatShamirGame DuplexRefinement DuplexEncoding

def previousConsumed : Frame → Nat
  | .absorb n _ => n
  | .nonce n _ _ => n

def outputBlocks (n : Nat) : Nat := (n + 31) / 32

def callerOutputCount (frames : List Frame) : Nat :=
  (frames.map (fun f => outputBlocks (previousConsumed f))).sum

def outputsFrom (entry : FramedHistory) (pre : List Frame) : List Frame → List Coordinate
  | [] => []
  | f :: fs =>
      (List.range (outputBlocks (previousConsumed f))).map
        (fun block => ⟨{entry with frames := pre},.output block⟩) ++
      outputsFrom entry (pre ++ [f]) fs

def callerOutputs (entry : FramedHistory) : List Coordinate :=
  outputsFrom entry [] entry.frames

theorem outputsFrom_length (entry : FramedHistory) (pre frames : List Frame) :
    (outputsFrom entry pre frames).length = callerOutputCount frames := by
  induction frames generalizing pre with
  | nil => rfl
  | cons f fs ih => simp [outputsFrom, callerOutputCount, ih]

theorem callerOutputs_length (entry : FramedHistory) :
    (callerOutputs entry).length = callerOutputCount entry.frames := outputsFrom_length _ _ _

theorem outputsFrom_mem (entry : FramedHistory) (pre frames : List Frame) (q : Coordinate)
    (mem : q ∈ outputsFrom entry pre frames) :
    ∃ middle f suffix block, frames = middle ++ f :: suffix ∧
      block < outputBlocks (previousConsumed f) ∧
      q = ⟨{entry with frames := pre ++ middle},.output block⟩ := by
  induction frames generalizing pre with
  | nil => simp [outputsFrom] at mem
  | cons f fs ih =>
    rcases List.mem_append.mp mem with head | tail
    · obtain ⟨block,hb,hq⟩ := List.mem_map.mp head
      exact ⟨[],f,fs,block,rfl,List.mem_range.mp hb,by simpa using hq.symm⟩
    · obtain ⟨middle,g,suffix,block,eqn,hb,hq⟩ := ih (pre ++ [f]) tail
      refine ⟨f :: middle,g,suffix,block,by simp [eqn],hb,?_⟩
      simpa [List.append_assoc] using hq

theorem callerOutputs_mem (entry : FramedHistory) (q : Coordinate) (mem : q ∈ callerOutputs entry) :
    ∃ pre f suffix block, entry.frames = pre ++ f :: suffix ∧
      block < outputBlocks (previousConsumed f) ∧
      q = ⟨{entry with frames := pre},.output block⟩ := by
  simpa using outputsFrom_mem entry [] entry.frames q mem

theorem outputsFrom_append (entry : FramedHistory) (pre a b : List Frame) :
    outputsFrom entry pre (a ++ b) =
      outputsFrom entry pre a ++ outputsFrom entry (pre ++ a) b := by
  induction a generalizing pre with
  | nil => simp [outputsFrom]
  | cons f fs ih => simp [outputsFrom, ih, List.append_assoc]

theorem callerOutput_mem (entry : FramedHistory) (pre : List Frame) (f : Frame)
    (suffix : List Frame) (block : Nat) (split : entry.frames = pre ++ f :: suffix)
    (bound : block < outputBlocks (previousConsumed f)) :
    (⟨{entry with frames := pre},.output block⟩ : Coordinate) ∈ callerOutputs entry := by
  unfold callerOutputs
  rw [split, outputsFrom_append]
  apply List.mem_append_right
  simp only [List.nil_append, outputsFrom]
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨block,List.mem_range.mpr bound,rfl⟩

theorem callerOutputs_strict_prefix (entry : FramedHistory) (q : Coordinate)
    (mem : q ∈ callerOutputs entry) :
    q.history.domain = entry.domain ∧ q.history.statement = entry.statement ∧
      q.history.frames.length < entry.frames.length ∧
      q.history.frames = entry.frames.take q.history.frames.length := by
  obtain ⟨pre,f,suffix,block,split,_,rfl⟩ := callerOutputs_mem entry q mem
  simp [split]

theorem callerOutputs_admissible (entry : FramedHistory)
    (valid : ∀ f ∈ entry.frames, FrameValid f) (q : Coordinate) (mem : q ∈ callerOutputs entry) :
    Admissible q := by
  obtain ⟨pre,f,suffix,block,split,bound,rfl⟩ := callerOutputs_mem entry q mem
  have hf := valid f (by simp [split])
  have hp : previousConsumed f < 2^49 := by cases f <;> exact hf.1
  refine ⟨?_,?_⟩
  · intro g hg
    exact valid g (by simp only [split, List.mem_append, List.mem_cons]; exact Or.inl hg)
  · change block < 2^44
    unfold outputBlocks at bound
    omega

theorem callerOutputs_reachable_admissible (c : Compression) (iv domain statement : Digest32)
    {m : Model} {s : State} (reachable : Reachable c iv domain statement m s)
    (q : Coordinate) (mem : q ∈ callerOutputs (closeRun m).history) : Admissible q :=
  callerOutputs_admissible _ (WHIRCallerPrefix.reachable_entry_frameValid _ _ _ _ reachable) q mem

theorem callerOutputs_pathCost_le (entry : FramedHistory) (q : Coordinate)
    (mem : q ∈ callerOutputs entry) (terminal : Terminal) :
    DuplexFraming.pathCost q ≤ DuplexFraming.pathCost ⟨entry,terminal⟩ := by
  obtain ⟨pre,f,suffix,block,split,_,rfl⟩ := callerOutputs_mem entry q mem
  simp [DuplexFraming.pathCost, plan, split, List.flatMap_append]
  omega

theorem callerOutputs_extended_pathCost_le (entry : FramedHistory) (q : Coordinate)
    (mem : q ∈ callerOutputs entry) (suffix : List Frame) (terminal : Terminal) :
    DuplexFraming.pathCost q ≤ DuplexFraming.pathCost ⟨{entry with frames := entry.frames ++ suffix},terminal⟩ := by
  have h := callerOutputs_pathCost_le entry q mem terminal
  apply h.trans
  simp [DuplexFraming.pathCost, plan, List.flatMap_append]

/-- Recover only requested output bytes from answers already obtained for their keys. -/
def recoveredBytes (answers : Coordinate → Digest32) (history : FramedHistory) (offset n : Nat) : List Byte :=
  List.ofFn (fun i : Fin n => answers ⟨history,.output ((offset+i.val)/32)⟩
    ⟨(offset+i.val)%32,Nat.mod_lt _ (by decide)⟩)

theorem stream_ofFn (c : Compression) (cv : Digest32) (offset n : Nat) :
    stream c cv offset n = List.ofFn (fun i : Fin n =>
      outputBlock c cv ((offset+i.val)/32) ⟨(offset+i.val)%32,Nat.mod_lt _ (by decide)⟩) := by
  induction n generalizing offset with
  | zero => simp [stream]
  | succ n ih =>
    simp [stream, List.ofFn_succ, ih, Nat.add_comm, Nat.add_left_comm]

theorem callerBytes_recovery (c : Compression) (iv : Digest32) (entry : FramedHistory)
    (answers : Coordinate → Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = evalCoordinate c iv q)
    (pre : List Frame) (f : Frame) (suffix : List Frame)
    (split : entry.frames = pre ++ f :: suffix) (offset n : Nat)
    (within : offset + n ≤ previousConsumed f) :
    recoveredBytes answers {entry with frames := pre} offset n =
      stream c (evalHistory c iv {entry with frames := pre}) offset n := by
  rw [stream_ofFn]
  unfold recoveredBytes
  congr 1
  funext i
  have bound : (offset+i.val)/32 < outputBlocks (previousConsumed f) := by
    have hi := i.isLt
    unfold outputBlocks
    omega
  rw [observed _ (callerOutput_mem entry pre f suffix _ split bound)]
  rfl

theorem actual_callerBytes_recovery (c : Compression) (iv : Digest32) (entry : FramedHistory)
    (answers : Coordinate → Digest32)
    (observed : ∀ q ∈ callerOutputs entry, answers q = evalCoordinate c iv q)
    (pre : List Frame) (f : Frame) (suffix : List Frame)
    (split : entry.frames = pre ++ f :: suffix) (m : Model) (s t : State)
    (represented : Represents c iv m s)
    (history : (closeRun m).history = {entry with frames := pre})
    (n : Nat) (bytes : List Byte) (ok : squeeze c s n = .ok (t,bytes))
    (within : m.consumed + n ≤ previousConsumed f) :
    recoveredBytes answers {entry with frames := pre} m.consumed n = bytes := by
  rw [squeeze_frame_bytes c iv m s t represented n bytes ok, history]
  exact callerBytes_recovery c iv entry answers observed pre f suffix split _ _ within

end Whir.WHIRCallerOutputs

namespace Whir.WHIRCallerShape
open FiatShamirGame DuplexRefinement WHIRCallerOutputs

/-- Exact accumulated caller output-block count paired with the existing control abstraction. -/
def abstractOutputs (m : Model) : StateShape × Nat :=
  (abstractModel m,callerOutputCount m.history.frames)

def closeOutputs (s : StateShape × Nat) : StateShape × Nat :=
  (closeShape s.1, s.2 + if s.1.run = 0 then 0 else outputBlocks s.1.previous)

def applyOutputs (s : StateShape × Nat) (event : EventShape) : StateShape × Nat :=
  (applyShape s.1 event, match event with
    | .absorb _ => s.2
    | .squeeze n => if n = 0 then s.2 else (closeOutputs s).2
    | .nonce _ => (closeOutputs s).2 + outputBlocks s.1.consumed)

def runOutputs (s : StateShape × Nat) (events : List EventShape) : StateShape × Nat :=
  events.foldl applyOutputs s

theorem abstract_closeOutputs (m : Model) :
    abstractOutputs (closeRun m) = closeOutputs (abstractOutputs m) := by
  apply Prod.ext
  · exact abstract_closeRun m
  · by_cases h : m.run = [] <;>
      simp [abstractOutputs, closeOutputs, closeRun, abstractModel, h,
        callerOutputCount, previousConsumed, List.map_append]

theorem abstract_applyOutputs (m : Model) (op : Operation) :
    abstractOutputs (applyOperation m op) = applyOutputs (abstractOutputs m) (operationShape op) := by
  apply Prod.ext
  · exact abstract_applyOperation m op
  · cases op with
    | absorb bs =>
      by_cases h : bs = [] <;> simp [applyOperation, modelAbsorb, applyOutputs, operationShape, abstractOutputs, h]
    | squeeze n =>
      by_cases h : n = 0
      · simp [applyOperation, modelSqueeze, applyOutputs, operationShape, abstractOutputs, h]
      · simpa [applyOperation, modelSqueeze, applyOutputs, operationShape, abstractOutputs, h] using
          congrArg Prod.snd (abstract_closeOutputs m)
    | nonce bits value =>
      have hc : (closeRun m).consumed = m.consumed := by
        by_cases h : m.run = [] <;> simp [closeRun, h]
      have he := congrArg Prod.snd (abstract_closeOutputs m)
      simp only [abstractOutputs] at he
      simp only [applyOperation, modelNonce, applyOutputs, operationShape, abstractOutputs,
        callerOutputCount, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, previousConsumed, hc]
      exact congrArg (fun n => n + outputBlocks m.consumed) he

theorem abstract_runOutputs (m : Model) (ops : List Operation) :
    abstractOutputs (runOperations m ops) = runOutputs (abstractOutputs m) (ops.map operationShape) := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih =>
    simp only [runOperations, runOutputs, List.foldl_cons, List.map_cons] at ih ⊢
    rw [ih, abstract_applyOutputs]

/-- A concrete public cap; unlike path cost it accounts for every prior output block. -/
def callerOutputCap (shape : List EventShape) : Nat :=
  (closeOutputs (runOutputs (⟨0,0,0,0⟩,0) shape)).2

theorem normalized_callerOutputCount (domain statement : Digest32) (ops : List Operation) :
    callerOutputCount (closeRun (runOperations (seedModel domain statement) ops)).history.frames =
      callerOutputCap (ops.map operationShape) := by
  exact congrArg Prod.snd
    ((abstract_closeOutputs _).trans (congrArg closeOutputs (abstract_runOutputs _ _)))

theorem normalized_modelEvents_outputCount (domain statement : Digest32)
    (events : List WHIRHistory.Event) :
    callerOutputCount (closeRun (WHIRHistory.modelEvents (seedModel domain statement) events)).history.frames =
      callerOutputCap (events.map (operationShape ∘ ofWHIREvent)) := by
  rw [← run_ofWHIREvents, normalized_callerOutputCount, List.map_map]

end Whir.WHIRCallerShape
