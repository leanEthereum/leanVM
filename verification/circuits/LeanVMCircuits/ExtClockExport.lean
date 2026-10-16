module

public import LeanVMCircuits.ExtClockCircuit
public import LeanVMCircuits.Flatten
import all Init.Data.Array.Basic
import all Init.Data.Vector.FinRange

-- Closed kernel reduction traverses the six incrementers and the two gated words.
set_option maxRecDepth 65536

@[expose] public section

namespace LeanVMCircuits.Flock.ExtClock

open LeanVMCircuits

/-- The extras' input ports, after the clock's: `v1`, `v2`, `vd` (the pointers `a`, `b`, `d`), then the flags. -/
def inputs : Var LeanVMCircuits.ExtClock.Input Bit := {
  v1 := Vector.mapFinRange 64 fun i => .var ⟨i.val⟩
  v2 := Vector.mapFinRange 64 fun i => .var ⟨64 + i.val⟩
  vd := Vector.mapFinRange 64 fun i => .var ⟨128 + i.val⟩
  flags := Vector.mapFinRange 2 fun i => .var ⟨192 + i.val⟩
}

def source := LeanVMCircuits.ExtClock.circuit.toSubcircuit 194 inputs

def output := LeanVMCircuits.ExtClock.circuit.output inputs 194

def lowerExtClock : Except String Artifact :=
  lowerAt source.ops (toElements (M := fields 386) output).toList

theorem supported : lowerExtClock.isOk = true := by decide +kernel

def artifact : Artifact := checked lowerExtClock supported

theorem source_eq : lowerExtClock = .ok artifact := checked_eq _ _

/-- Every assignment satisfying the rows outputs the flags' bits, then `p + 8` and `p + 16` modulo `2^64` for each
pointer, `v2`'s zero when `base` is set. -/
theorem soundness (env : Environment Bit) (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    LeanVMCircuits.ExtClock.Addresses (eval env inputs) (artifact.outputs.map (Affine.eval env.get)) := by
  have h := lowerAt_correct _ _ artifact source_eq env
  have hs := (source.soundness env (by change True; trivial) (h.1.mp hrows) h.2.1).1
  change LeanVMCircuits.ExtClock.Spec (eval env inputs) (eval env output) at hs
  have hout : artifact.outputs.map (Affine.eval env.get) = (toElements (M := fields 386) (eval env output)).toList :=
    calc
      artifact.outputs.map (Affine.eval env.get) =
          (toElements (M := fields 386) output).toList.map (Expression.eval env) := h.2.2
      _ = (toElements (M := fields 386) (eval env output)).toList := by
        rw [ProvableType.toElements_eval, Vector.toList_map]
  rw [hout]
  exact hs

theorem layout :
    artifact.rows.map Row.output = (List.range 479).map (194 + ·) ∧
      artifact.outputs.length = 386 := by decide +kernel

/-- `v2`'s gated addresses are their public output bits (ports 5 and 6 of the Ext clock circuit), not extra private
witness slots. -/
def outputProducts : List (Nat × Nat × Nat) :=
  (List.range 64).map (fun bit => (370 + bit, 5, bit)) ++ (List.range 64).map (fun bit => (492 + bit, 6, bit))

theorem output_products_layout :
    (artifact.outputs.drop 130).take 128 = outputProducts.map (fun placement => Affine.var placement.1) := by
  decide +kernel

theorem wellFormed : Flock.wellFormed 194 artifact.rows = true := by decide +kernel

theorem complete (initial : ℕ → Bit) :
    ∃ final, AgreeBelow 194 initial final ∧ artifact.rows.Forall (Row.Holds final) :=
  witness_exists artifact.rows 194 initial wellFormed

end LeanVMCircuits.Flock.ExtClock
