module

public import LeanVMCircuits.ShiftSemantics

@[expose] public section

namespace LeanVMCircuits.ShiftStage

structure Input (F : Type) where
  selector : F
  fill : F
  word : Vector F 64
  deriving ProvableStruct

def main (amount : ℕ) (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) :=
  WordMux.circuit 64 { selector := input.selector, x := Words.right amount input.fill input.word, y := input.word }

instance elaborated (amount : ℕ) : ElaboratedCircuit Bit Input (fields 64) (main amount) := by
  elaborate_circuit

@[circuit_norm]
def circuit (amount : ℕ) : FormalCircuit Bit Input (fields 64) where
  main := main amount
  elaborated := elaborated amount
  Spec := fun input output =>
    output = Words.right (if input.selector = 1 then amount else 0) input.fill input.word
  soundness := by
    circuit_proof_start
    rcases h_input with ⟨hs, hf, hw⟩
    simp only [WordMux.Spec, WordMux.select, circuit_norm, Words.right_map] at h_holds
    rw [hw, hf] at h_holds
    dsimp +instances only [WordMux.circuit] at h_holds ⊢
    by_cases h : input_selector = 1 <;>
      simpa [h, Words.right_zero, FormalCircuitBase.output, WordMux.circuit, ← ElaboratedCircuit.output_eq] using h_holds
  completeness := by circuit_proof_start

end LeanVMCircuits.ShiftStage

namespace LeanVMCircuits.ReverseUnless

structure Input (F : Type) where
  selector : F
  word : Vector F 64
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) :=
  WordMux.circuit 64 { selector := input.selector, x := input.word, y := Words.reverse input.word }

instance elaborated : ElaboratedCircuit Bit Input (fields 64) main := by elaborate_circuit

@[circuit_norm]
def circuit : FormalCircuit Bit Input (fields 64) where
  main
  elaborated
  Spec := fun input output => if input.selector = 1 then output = input.word else output = Words.reverse input.word
  soundness := by
    circuit_proof_start
    rcases h_input with ⟨hs, hw⟩
    simp only [WordMux.Spec, WordMux.select, circuit_norm, Words.reverse_map] at h_holds
    rw [hw] at h_holds
    dsimp +instances only [WordMux.circuit] at h_holds ⊢
    by_cases h : input_selector = 1 <;>
      simpa [h, FormalCircuitBase.output, WordMux.circuit, ← ElaboratedCircuit.output_eq] using h_holds
  completeness := by circuit_proof_start

end LeanVMCircuits.ReverseUnless
