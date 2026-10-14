module

public import LeanVMCircuits.WordMode

@[expose] public section

namespace LeanVMCircuits.ShiftPreparation

structure Input (F : Type) where
  v1 : Vector F 64
  v2 : Vector F 64
  imm : Vector F 64
  arith : F
  word : F
  deriving ProvableStruct

structure Output (F : Type) where
  amount : Vector F 6
  word : Vector F 64
  fill : F
  deriving ProvableStruct

def amountBits (input : Input Bit) : Vector Bit 6 :=
  Vector.mapFinRange 6 fun i =>
    if input.word = 1 ∧ i.val = 5 then 0 else input.v2[i.val]'(by omega) + input.imm[i.val]'(by omega)

def operand (input : Input Bit) : Vector Bit 64 :=
  if input.word = 1 then Words.high (if input.arith = 1 then input.v1[31] else 0) input.v1 else input.v1

def Spec (input : Input Bit) (output : Output Bit) : Prop :=
  output.amount = amountBits input ∧ output.word = operand input ∧
    output.fill = if input.arith = 1 then (operand input)[63] else 0

def main (input : Var Input Bit) : Circuit Bit (Var Output Bit) := do
  let top ← Mux.circuit { selector := 1 + input.word, x := input.v2[5] + input.imm[5], y := 0 }
  let amount := (Vector.mapFinRange 5 fun i => input.v2[i.val]'(by omega) + input.imm[i.val]'(by omega)).push top
  let lowSign ← Mux.circuit { selector := input.arith, x := input.v1[31], y := 0 }
  let word ← WordMode.circuit { selector := input.word, fill := lowSign, word := input.v1 }
  let fill ← Mux.circuit { selector := input.arith, x := word[63], y := 0 }
  return { amount, word, fill }

instance elaborated : ElaboratedCircuit Bit Input Output main := by elaborate_circuit

@[circuit_norm]
def circuit : FormalCircuit Bit Input Output where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [Spec, operand]
    rcases h_input with ⟨hv1, hv2, himm, ha, hw⟩
    rcases h_holds with ⟨htop, hlow, hword, hfill⟩
    simp only [Mux.Spec, circuit_norm] at htop hlow hfill
    rw [hlow] at hword
    simp only [Mux.select] at hword hfill
    have hv1sign := congrArg (fun v : Vector Bit 64 => v[31]) hv1
    simp only [Vector.getElem_map] at hv1sign
    rw [hv1sign] at hword
    have hwordbit := congrArg (fun v : Vector Bit 64 => v[63]) hword
    simp only [Vector.getElem_map] at hwordbit
    rw [hwordbit] at hfill
    refine ⟨?_, hword, hfill⟩
    apply Vector.ext
    intro i hi
    have hv2bit := congrArg (fun v : Vector Bit 64 => v[i]'(by omega)) hv2
    have himmbit := congrArg (fun v : Vector Bit 64 => v[i]'(by omega)) himm
    simp only [Vector.getElem_map] at hv2bit himmbit
    interval_cases i <;> simp_all [amountBits, Mux.not_selection, circuit_norm, Vector.getElem_mapFinRange]
  completeness := by circuit_proof_start

end LeanVMCircuits.ShiftPreparation
