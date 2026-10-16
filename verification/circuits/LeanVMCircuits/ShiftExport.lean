module

public import LeanVMCircuits.Shift
-- Import reference bodies, not unsafe runtime implementations, for closed kernel certification.
import all Init.Data.Array.Basic
import all Init.Data.Vector.FinRange

-- Kernel reduction traverses 1158 flat operations and recursively composed word selectors.
set_option maxRecDepth 65536

@[expose] public section

namespace LeanVMCircuits.Flock.Shift

open LeanVMCircuits

def inputs : Var LeanVMCircuits.Shift.Input Bit := {
  v1 := Vector.mapFinRange 64 fun i => .var ⟨i.val⟩
  v2 := Vector.mapFinRange 64 fun i => .var ⟨64 + i.val⟩
  imm := Vector.mapFinRange 64 fun i => .var ⟨128 + i.val⟩
  right := .var ⟨192⟩
  arith := .var ⟨193⟩
  word := .var ⟨194⟩
}

def source := LeanVMCircuits.Shift.circuit.toSubcircuit 195 inputs

def output := LeanVMCircuits.Shift.circuit.output inputs 195

def lowerShift : Except String Artifact := lowerAt source.ops output.toList

theorem supported : lowerShift.isOk = true := by decide +kernel

def artifact : Artifact := checked lowerShift supported

theorem source_eq : lowerShift = .ok artifact := checked_eq _ _

def result (env : Environment Bit) : Vector Bit 64 :=
  let input := eval env inputs
  if input.word = 1 then Words.high (LeanVMCircuits.Shift.shifted input)[31] (LeanVMCircuits.Shift.shifted input)
    else LeanVMCircuits.Shift.shifted input

theorem soundness (env : Environment Bit)
    (hlegal : LeanVMCircuits.Shift.Assumptions (eval env inputs))
    (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    artifact.outputs.map (Affine.eval env.get) = (result env).toList := by
  have h := lowerAt_correct _ _ artifact source_eq env
  have hs := (source.soundness env
    (by change LeanVMCircuits.Shift.Assumptions (eval env inputs); exact hlegal)
    (h.1.mp hrows) h.2.1).1
  change LeanVMCircuits.Shift.Spec (eval env inputs) (eval env output) at hs
  change eval env output = result env at hs
  calc
    artifact.outputs.map (Affine.eval env.get) = output.toList.map (Expression.eval env) := h.2.2
    _ = (eval env output).toList := by simp only [circuit_norm, Vector.toList_map]
    _ = (result env).toList := congrArg Vector.toList hs

theorem layout :
    artifact.rows.map Row.output = (List.range 579).map (195 + ·) ∧
      artifact.outputs.length = 64 := by decide +kernel

theorem wellFormed : Flock.wellFormed 195 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 195 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 195 initial wellFormed

end LeanVMCircuits.Flock.Shift
