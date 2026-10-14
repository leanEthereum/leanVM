module

public import LeanVMCircuits.BooleanOps

@[expose] public section

namespace LeanVMCircuits.AluBranch

structure Input (F : Type) where
  flags : Vector F 15
  ne : F
  lt : F
  ltu : F
  deriving ProvableStruct

def selected (input : Input Bit) : Bit :=
  input.flags[14] + input.flags[8] * (1 + input.ne) + input.flags[9] * input.ne +
    input.flags[10] * input.lt + input.flags[11] * (1 + input.lt) +
    input.flags[12] * input.ltu + input.flags[13] * (1 + input.ltu)

def main (input : Var Input Bit) : Circuit Bit (Expression Bit) := do
  let eq ← Product.circuit { x := input.flags[8], y := 1 + input.ne }
  let ne ← Product.circuit { x := input.flags[9], y := input.ne }
  let lt ← Product.circuit { x := input.flags[10], y := input.lt }
  let ge ← Product.circuit { x := input.flags[11], y := 1 + input.lt }
  let ltu ← Product.circuit { x := input.flags[12], y := input.ltu }
  let geu ← Product.circuit { x := input.flags[13], y := 1 + input.ltu }
  return input.flags[14] + eq + ne + lt + ge + ltu + geu

instance elaborated : ElaboratedCircuit Bit Input field main := by elaborate_circuit

def Spec (input : Input Bit) (output : Bit) : Prop := output = selected input

def circuit : FormalCircuit Bit Input field where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [main, Product.circuit, Product.Spec]
    rcases h_input with ⟨hf, hne, hlt, hltu⟩
    have hflag (i : ℕ) (hi : i < 15) := congrArg (fun flags : Vector Bit 15 => flags[i]) hf
    simp only [Vector.getElem_map] at hflag
    simp_all [selected, circuit_norm]
  completeness := by circuit_proof_start [main, Product.circuit, Product.Spec]

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 6 := rfl

end LeanVMCircuits.AluBranch
