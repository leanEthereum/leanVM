module

public import LeanVMCircuits.MemoryLoad
public import LeanVMCircuits.MemoryStore
public import LeanVMCircuits.Flatten
import all Init.Data.Array.Basic
import all Init.Data.Vector.FinRange

-- Closed kernel reduction traverses the nested ripple carry, byte shifts and mux operations.
set_option maxRecDepth 65536

@[expose] public section

namespace LeanVMCircuits.Flock.Load

open LeanVMCircuits

def inputs : Var LeanVMCircuits.Load.Input Bit := {
  v1 := Vector.mapFinRange 64 fun i => .var ⟨i.val⟩
  imm := Vector.mapFinRange 64 fun i => .var ⟨64 + i.val⟩
  low := .var ⟨128⟩
  high := .var ⟨129⟩
  signed := .var ⟨130⟩
  cell := Vector.mapFinRange 64 fun i => .var ⟨131 + i.val⟩
}

def source := LeanVMCircuits.Load.circuit.toSubcircuit 195 inputs

def output := LeanVMCircuits.Load.circuit.output inputs 195

def lowerLoad : Except String Artifact := lowerAt source.ops (toElements (M := LeanVMCircuits.Load.Output) output).toList

theorem supported : lowerLoad.isOk = true := by decide +kernel

def artifact : Artifact := checked lowerLoad supported

theorem source_eq : lowerLoad = .ok artifact := checked_eq _ _

def result (input : LeanVMCircuits.Load.Input Bit) : LeanVMCircuits.Load.Output Bit :=
  let address := Memory.address input.v1 input.imm
  { bus := Memory.bus input.low input.high address,
    value := Memory.load input.low input.high input.signed address input.cell }

theorem soundness (env : Environment Bit)
    (hlegal : Memory.LegalWidth (eval env inputs).low (eval env inputs).high)
    (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    artifact.outputs.map (Affine.eval env.get) = (toElements (result (eval env inputs))).toList := by
  have h := lowerAt_correct _ _ artifact source_eq env
  have hs := (source.soundness env
    (by change Memory.LegalWidth (eval env inputs).low (eval env inputs).high; exact hlegal)
    (h.1.mp hrows) h.2.1).1
  change LeanVMCircuits.Load.Spec (eval env inputs) (eval env output) at hs
  have hout : eval env output = result (eval env inputs) := by
    rcases hs with ⟨hbus, hvalue⟩
    exact congrArg₂ LeanVMCircuits.Load.Output.mk hbus hvalue
  calc
    artifact.outputs.map (Affine.eval env.get) = (toElements (M := LeanVMCircuits.Load.Output) output).toList.map (Expression.eval env) := h.2.2
    _ = (toElements (M := LeanVMCircuits.Load.Output) (eval env output)).toList := by
      rw [ProvableType.toElements_eval, Vector.toList_map]
    _ = (toElements (result (eval env inputs))).toList := congrArg (fun x => (toElements x).toList) hout

theorem layout :
    artifact.rows.map Row.output = (List.range 253).map (195 + ·) ∧
      artifact.outputs.length = 128 := by decide +kernel

theorem wellFormed : Flock.wellFormed 195 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 195 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 195 initial wellFormed

end LeanVMCircuits.Flock.Load

namespace LeanVMCircuits.Flock.Store

open LeanVMCircuits

def inputs : Var LeanVMCircuits.Store.Input Bit := {
  v1 := Vector.mapFinRange 64 fun i => .var ⟨i.val⟩
  v2 := Vector.mapFinRange 64 fun i => .var ⟨64 + i.val⟩
  imm := Vector.mapFinRange 64 fun i => .var ⟨128 + i.val⟩
  low := .var ⟨192⟩
  high := .var ⟨193⟩
  cell := Vector.mapFinRange 64 fun i => .var ⟨194 + i.val⟩
}

def source := LeanVMCircuits.Store.circuit.toSubcircuit 258 inputs

def output := LeanVMCircuits.Store.circuit.output inputs 258

def lowerStore : Except String Artifact := lowerAt source.ops (toElements (M := LeanVMCircuits.Store.Output) output).toList

theorem supported : lowerStore.isOk = true := by decide +kernel

def artifact : Artifact := checked lowerStore supported

theorem source_eq : lowerStore = .ok artifact := checked_eq _ _

def result (input : LeanVMCircuits.Store.Input Bit) : LeanVMCircuits.Store.Output Bit :=
  let address := Memory.address input.v1 input.imm
  { bus := Memory.bus input.low input.high address,
    value := Memory.store input.low input.high address input.v2 input.cell }

theorem soundness (env : Environment Bit)
    (hlegal : LeanVMCircuits.Store.circuit.Assumptions (eval env inputs))
    (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    artifact.outputs.map (Affine.eval env.get) = (toElements (result (eval env inputs))).toList := by
  have h := lowerAt_correct _ _ artifact source_eq env
  have hs := (source.soundness env
    (by change LeanVMCircuits.Store.circuit.Assumptions (eval env inputs); exact hlegal)
    (h.1.mp hrows) h.2.1).1
  change LeanVMCircuits.Store.Spec (eval env inputs) (eval env output) at hs
  have hout : eval env output = result (eval env inputs) := by
    rcases hs with ⟨hbus, hvalue⟩
    exact congrArg₂ LeanVMCircuits.Store.Output.mk hbus hvalue
  calc
    artifact.outputs.map (Affine.eval env.get) = (toElements (M := LeanVMCircuits.Store.Output) output).toList.map (Expression.eval env) := h.2.2
    _ = (toElements (M := LeanVMCircuits.Store.Output) (eval env output)).toList := by
      rw [ProvableType.toElements_eval, Vector.toList_map]
    _ = (toElements (result (eval env inputs))).toList := congrArg (fun x => (toElements x).toList) hout

theorem layout :
    artifact.rows.map Row.output = (List.range 309).map (258 + ·) ∧
      artifact.outputs.length = 128 := by decide +kernel

theorem wellFormed : Flock.wellFormed 258 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 258 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 258 initial wellFormed

end LeanVMCircuits.Flock.Store
