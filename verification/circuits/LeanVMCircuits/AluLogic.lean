module

public import LeanVMCircuits.BooleanOps

@[expose] public section

namespace LeanVMCircuits.AluLogic

structure Input (F : Type) where
  andOr : F
  orXor : F
  x : F
  y : F
  difference : F
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Expression Bit) := do
  let both ← Product.circuit { x := input.x, y := input.y }
  let andTerm ← Product.circuit { x := input.andOr, y := both }
  let xorTerm ← Product.circuit { x := input.orXor, y := input.difference }
  return andTerm + xorTerm

def Spec (input : Input Bit) (output : Bit) : Prop :=
  output = input.andOr * (input.x * input.y) + input.orXor * input.difference

instance elaborated : ElaboratedCircuit Bit Input field main := by elaborate_circuit

def circuit : FormalCircuit Bit Input field where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [main, Product.circuit, Product.Spec]
    simp_all [circuit_norm]
  completeness := by
    circuit_proof_start [main, Product.circuit, Product.Spec]

@[circuit_norm] theorem circuit_assumptions :
    circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 3 := rfl


end LeanVMCircuits.AluLogic
