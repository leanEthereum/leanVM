module

public import LeanVMCircuits.MemorySemantics

@[expose] public section

namespace LeanVMCircuits.ByteSelection

structure Input (F : Type) where
  low : F
  middle : F
  high : F
  value : Vector F 8
  cell : Vector F 8
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Var (fields 8) Bit) := do
  let low ← Product.circuit { x := input.low, y := input.middle }
  let written ← Product.circuit { x := low, y := input.high }
  WordMux.circuit 8 { selector := written, x := input.value, y := input.cell }

def Spec (input : Input Bit) (output : Vector Bit 8) : Prop :=
  output = if input.low = 1 ∧ input.middle = 1 ∧ input.high = 1 then input.value else input.cell

instance elaborated : ElaboratedCircuit Bit Input (fields 8) main := by elaborate_circuit

def circuit : FormalCircuit Bit Input (fields 8) where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [main, Spec, Product.circuit, Product.Spec]
    rcases h_input with ⟨hl, hm, hh, hv, hc⟩
    rcases h_holds with ⟨hlow, hwritten, hout⟩
    simp only [WordMux.Spec, WordMux.select, circuit_norm] at hout
    rw [hwritten, hlow] at hout
    dsimp +instances only [FormalCircuitBase.output, WordMux.circuit] at hout ⊢
    simp only [← ElaboratedCircuit.output_eq] at hout ⊢
    rcases bit_zero_or_one input_low with hlow | hlow <;>
      rcases bit_zero_or_one input_middle with hmiddle | hmiddle <;>
      rcases bit_zero_or_one input_high with hhigh | hhigh <;>
      simpa [hlow, hmiddle, hhigh, hv, hc] using hout
  completeness := by circuit_proof_start [main, Product.circuit]

@[circuit_norm] theorem circuit_assumptions :
    circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements :
    circuit.channelsWithRequirements = [] := by simp only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_guarantees :
    circuit.elaborated.channelsWithGuarantees = [] := by
  dsimp +instances only [circuit, elaborated]
  simp only [circuit_norm]
@[circuit_norm] theorem circuit_length (input : Var Input Bit) :
    circuit.localLength input = 10 := by
  change ElaboratedCircuit.localLength main input = 10
  rw [← ElaboratedCircuit.localLength_eq (main := main) input 0]
  simp only [main, Product.circuit, circuit_norm]

end LeanVMCircuits.ByteSelection
