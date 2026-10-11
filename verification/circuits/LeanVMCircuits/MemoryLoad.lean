module

public import LeanVMCircuits.MemoryAddress
public import LeanVMCircuits.MemoryShift
public import LeanVMCircuits.MemorySelection
public import LeanVMCircuits.MemoryDomain
import all Init.Data.Array.Basic

@[expose] public section

namespace LeanVMCircuits.Load

structure Input (F : Type) where
  v1 : Vector F 64
  imm : Vector F 64
  low : F
  high : F
  signed : F
  cell : Vector F 64
  deriving ProvableStruct

structure Output (F : Type) where
  bus : Vector F 64
  value : Vector F 64
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Var Output Bit) := do
  let address ← MemoryAddress.circuit { v1 := input.v1, imm := input.imm, low := input.low, high := input.high }
  let shifted ← LoadShift.circuit { amount := #v[address.address[0], address.address[1], address.address[2]], word := input.cell }
  let value ← LoadExtend.circuit { low := input.low, high := input.high, signed := input.signed, word := shifted }
  return { bus := address.bus, value }

def Spec (input : Input Bit) (output : Output Bit) : Prop :=
  let address := Memory.address input.v1 input.imm
  output.bus = Memory.bus input.low input.high address ∧
    output.value = Memory.load input.low input.high input.signed address input.cell

def output (input : Var Input Bit) (offset : ℕ) : Var Output Bit :=
  let address := MemoryAddress.circuit.output { v1 := input.v1, imm := input.imm, low := input.low, high := input.high } offset
  let shifted := LoadShift.circuit.output {
    amount := #v[address.address[0], address.address[1], address.address[2]], word := input.cell
  } (offset + 65)
  let value := LoadExtend.circuit.output {
    low := input.low, high := input.high, signed := input.signed, word := shifted
  } (offset + 225)
  { bus := address.bus, value }

instance elaborated : ElaboratedCircuit Bit Input Output main := by
  let base : ElaboratedCircuit Bit Input Output main := by elaborate_circuit
  exact {
    base with
    localLength := fun _ => 253
    localLength_eq := by intro input offset; simp only [main, circuit_norm]
    output := output
    output_eq := by intro input offset; simp only [main, output, circuit_norm]
  }

@[circuit_norm]
def circuit : FormalCircuit Bit Input Output where
  main
  elaborated
  Assumptions := fun input => Memory.LegalWidth input.low input.high
  Spec
  soundness := by
    circuit_proof_start [main, output, Spec, MemoryAddress.Spec]
    rcases h_holds with ⟨⟨haddress, hbus⟩, hshift, hvalue⟩
    conv at hbus => rhs; arg 3; rw [haddress]
    rw [MemoryAddress.eval_output] at hbus
    have hvalue := hvalue h_assumptions
    have hamount := congrArg (fun address : Vector Bit 64 => #v[address[0], address[1], address[2]]) haddress
    constructor
    · exact hbus
    · rw [hvalue, hshift]
      rw [hamount]
      exact (Memory.load_eq_extend input_low input_high input_signed
        (Memory.address input_v1 input_imm) input_cell h_assumptions).symm
  completeness := by
    circuit_proof_start [main]
    exact h_assumptions

end LeanVMCircuits.Load
