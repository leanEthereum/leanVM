module

public import LeanVMCircuits.AluCircuit
public import LeanVMCircuits.AluLawful
public import LeanVMCircuits.Flatten
import all Init.Data.Array.Basic
import all Init.Data.Vector.FinRange

set_option maxRecDepth 65536

@[expose] public section

namespace LeanVMCircuits.Flock.Alu

open LeanVMCircuits

def inputs : Var LeanVMCircuits.Alu.Input Bit := {
  v1 := Vector.mapFinRange 64 fun i => .var ⟨i.val⟩
  v2 := Vector.mapFinRange 64 fun i => .var ⟨64 + i.val⟩
  imm := Vector.mapFinRange 64 fun i => .var ⟨128 + i.val⟩
  flags := Vector.mapFinRange 15 fun i => .var ⟨192 + i.val⟩
  dt := Vector.mapFinRange 64 fun i => .var ⟨207 + i.val⟩
  pc4 := Vector.mapFinRange 64 fun i => .var ⟨271 + i.val⟩
}

def source := LeanVMCircuits.Alu.circuit.toSubcircuit 335 inputs

def output := LeanVMCircuits.Alu.circuit.output inputs 335

def lowerAlu : Except String Artifact :=
  lowerAt source.ops (toElements (M := LeanVMCircuits.Alu.Output) output).toList

theorem supported : lowerAlu.isOk = true := by decide +kernel

def artifact : Artifact := checked lowerAlu supported

theorem source_eq : lowerAlu = .ok artifact := checked_eq _ _

theorem soundness (env : Environment Bit) (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    artifact.outputs.map (Affine.eval env.get) =
      (toElements (LeanVMCircuits.Alu.rawReference (eval env inputs))).toList := by
  have h := lowerAt_correct _ _ artifact source_eq env
  have hs := (source.soundness env (by change True; trivial) (h.1.mp hrows) h.2.1).1
  change LeanVMCircuits.Alu.Spec (eval env inputs) (eval env output) at hs
  have hout := LeanVMCircuits.Alu.spec_raw (eval env inputs) (eval env output) hs
  calc
    artifact.outputs.map (Affine.eval env.get) =
        (toElements (M := LeanVMCircuits.Alu.Output) output).toList.map (Expression.eval env) := h.2.2
    _ = (toElements (M := LeanVMCircuits.Alu.Output) (eval env output)).toList := by
      rw [ProvableType.toElements_eval, Vector.toList_map]
    _ = (toElements (LeanVMCircuits.Alu.rawReference (eval env inputs))).toList :=
      congrArg (fun x => (toElements x).toList) hout

theorem soundness_reference (env : Environment Bit)
    (hlegal : LeanVMCircuits.Alu.Legal (eval env inputs).flags)
    (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    artifact.outputs.map (Affine.eval env.get) =
      (toElements (LeanVMCircuits.Alu.reference (eval env inputs))).toList := by
  have h := lowerAt_correct _ _ artifact source_eq env
  have hs := (source.soundness env (by change True; trivial) (h.1.mp hrows) h.2.1).1
  change LeanVMCircuits.Alu.Spec (eval env inputs) (eval env output) at hs
  rcases hs with ⟨arithmetic, ha, he⟩
  have hout := he.trans (LeanVMCircuits.Alu.afterArithmetic_reference
    (eval env inputs) arithmetic hlegal ha)
  calc
    artifact.outputs.map (Affine.eval env.get) =
        (toElements (M := LeanVMCircuits.Alu.Output) output).toList.map (Expression.eval env) := h.2.2
    _ = (toElements (M := LeanVMCircuits.Alu.Output) (eval env output)).toList := by
      rw [ProvableType.toElements_eval, Vector.toList_map]
    _ = (toElements (LeanVMCircuits.Alu.reference (eval env inputs))).toList :=
      congrArg (fun x => (toElements x).toList) hout

theorem layout :
    artifact.rows.map Row.output = (List.range 551).map (335 + ·) ∧
      artifact.outputs.length = 128 := by decide +kernel

/-- Jump products are their public output bits, not extra private witness slots. -/
def outputProducts : List (Nat × Nat × Nat) := (List.range 64).map fun bit => (822 + bit, 1, bit)

theorem output_products_layout :
    artifact.outputs.drop 64 = (List.range 64).map (fun bit => Affine.var (822 + bit)) := by
  decide +kernel

theorem wellFormed : Flock.wellFormed 335 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 335 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 335 initial wellFormed

end LeanVMCircuits.Flock.Alu
