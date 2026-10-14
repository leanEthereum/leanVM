module

public import LeanVMCircuits.MemorySemantics

@[expose] public section

namespace LeanVMCircuits.StoreSpans

structure Input (F : Type) where
  low : F
  high : F
  amount : Vector F 3
  deriving ProvableStruct

structure Output (F : Type) where
  low : Vector F 2
  middle : Vector F 2
  high : Vector F 2
  deriving ProvableStruct

def select (input : Input Bit) : Output Bit :=
  { low := #v[BooleanOr.select (1 + input.amount[0]) (input.low + input.high),
      BooleanOr.select input.amount[0] (input.low + input.high)]
    middle := #v[BooleanOr.select (1 + input.amount[1]) input.high,
      BooleanOr.select input.amount[1] input.high]
    high := #v[1 + input.amount[2], input.amount[2]] }

def main (input : Var Input Bit) : Circuit Bit (Var Output Bit) := do
  let low0 ← BooleanOr.circuit { x := (1 : Expression Bit) + input.amount[0], y := input.low + input.high }
  let low1 ← BooleanOr.circuit { x := input.amount[0], y := input.low + input.high }
  let middle0 ← BooleanOr.circuit { x := (1 : Expression Bit) + input.amount[1], y := input.high }
  let middle1 ← BooleanOr.circuit { x := input.amount[1], y := input.high }
  return { low := #v[low0, low1], middle := #v[middle0, middle1], high := #v[(1 : Expression Bit) + input.amount[2], input.amount[2]] }

instance elaborated : ElaboratedCircuit Bit Input Output main := by elaborate_circuit

def circuit : FormalCircuit Bit Input Output where
  main
  elaborated
  Spec := fun input output => output = select input
  soundness := by
    circuit_proof_start [main, BooleanOr.circuit]
    have h0 := congrArg (fun v : Vector Bit 3 => v[0]) h_input.2.2
    have h1 := congrArg (fun v : Vector Bit 3 => v[1]) h_input.2.2
    have h2 := congrArg (fun v : Vector Bit 3 => v[2]) h_input.2.2
    simp only [Vector.getElem_map] at h0 h1 h2
    simp only [circuit_norm, h0, h1] at h_holds
    rcases h_holds with ⟨hlow0, hlow1, hmiddle0, hmiddle1⟩
    simp only [select, circuit_norm, h0, h1, h2, hlow0, hlow1, hmiddle0, hmiddle1]
  completeness := by circuit_proof_start [main, BooleanOr.circuit]

@[circuit_norm] theorem circuit_assumptions :
    circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec :
    circuit.Spec = fun input output => output = select input := rfl
@[circuit_norm] theorem circuit_requirements :
    circuit.channelsWithRequirements = [] := by simp only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_guarantees :
    circuit.elaborated.channelsWithGuarantees = [] := by
  dsimp +instances only [circuit, elaborated]
@[circuit_norm] theorem circuit_length (input : Var Input Bit) :
    circuit.localLength input = 4 := by
  change ElaboratedCircuit.localLength main input = 4
  rw [← ElaboratedCircuit.localLength_eq (main := main) input 0]
  simp only [main, BooleanOr.circuit, circuit_norm]

end LeanVMCircuits.StoreSpans
