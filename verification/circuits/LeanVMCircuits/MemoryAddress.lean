module

public import LeanVMCircuits.MemorySemantics

-- Reducing the indexed output of the 64-bit recursive adder crosses the default elaboration depth.
set_option maxRecDepth 4096

@[expose] public section

namespace LeanVMCircuits.MemoryAddress

structure Input (F : Type) where
  v1 : Vector F 64
  imm : Vector F 64
  low : F
  high : F
  deriving ProvableStruct

structure Output (F : Type) where
  address : Vector F 64
  bus : Vector F 64
  deriving ProvableStruct
theorem eval_output (env : Environment Bit) (output : Var Output Bit) :
    ProvableStruct.eval env output =
      Output.mk (output.address.map (Expression.eval env)) (output.bus.map (Expression.eval env)) := by
  rcases output with ⟨address, bus⟩
  provable_struct_simp
  simp only [circuit_norm]

def main (input : Var Input Bit) : Circuit Bit (Var Output Bit) := do
  let address ← WrappingAdder.adder64 { x := input.v1, y := input.imm }
  let low ← Product.circuit { x := address[0], y := input.low + input.high }
  let high ← Product.circuit { x := address[1], y := input.high }
  return { address, bus := Memory.busParts low high address }

def Spec (input : Input Bit) (output : Output Bit) : Prop :=
  output.address = Memory.address input.v1 input.imm ∧
    output.bus = Memory.bus input.low input.high output.address

instance elaborated : ElaboratedCircuit Bit Input Output main := by elaborate_circuit

def circuit : FormalCircuit Bit Input Output where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [main, Spec, WrappingAdder.adder64, WrappingAdder.circuit,
      WrappingAdder.Spec, Product.circuit, Product.Spec]
    rcases h_holds with ⟨ha, hlow, hhigh⟩
    constructor
    · apply Adder.value_injective
      simpa [Memory.address, Words.value_ofNat, Nat.mod_mod] using ha
    · rw [Memory.busParts_map (Expression.eval env) (by rfl)]
      simp only [Memory.bus, circuit_norm]
      rw [hlow, hhigh]
  completeness := by
    circuit_proof_start [main, WrappingAdder.adder64, WrappingAdder.circuit, Product.circuit]

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
    circuit.localLength input = 65 := by
  change ElaboratedCircuit.localLength main input = 65
  rw [← ElaboratedCircuit.localLength_eq (main := main) input 0]
  simp only [main, circuit_norm, WrappingAdder.adder64, Product.circuit]

end LeanVMCircuits.MemoryAddress
