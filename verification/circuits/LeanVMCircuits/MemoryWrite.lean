module

public import LeanVMCircuits.MemoryMask
public import LeanVMCircuits.MemoryMaskSemantics

@[expose] public section

namespace LeanVMCircuits.StoreMask

structure Input (F : Type) where
  low : F
  high : F
  amount : Vector F 3
  value : Vector F 64
  cell : Vector F 64
  deriving ProvableStruct

def select (input : Input Bit) : Vector Bit 64 :=
  Memory.joinBytes (Vector.ofFn fun j =>
    if StoreSpans.contains { low := input.low, high := input.high, amount := input.amount } j
    then Memory.byte j input.value else Memory.byte j input.cell)

def byteInput (input : Var Input Bit) (spans : Var StoreSpans.Output Bit) (j : Fin 8) :
    Var ByteSelection.Input Bit :=
  { low := spans.low[j.val % 2]'(by omega)
    middle := spans.middle[j.val / 2 % 2]'(by omega)
    high := spans.high[j.val / 4]'(by omega)
    value := Memory.byte j input.value
    cell := Memory.byte j input.cell }

def main (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let spans ← StoreSpans.circuit { low := input.low, high := input.high, amount := input.amount }
  let byte0 ← ByteSelection.circuit (byteInput input spans 0)
  let byte1 ← ByteSelection.circuit (byteInput input spans 1)
  let byte2 ← ByteSelection.circuit (byteInput input spans 2)
  let byte3 ← ByteSelection.circuit (byteInput input spans 3)
  let byte4 ← ByteSelection.circuit (byteInput input spans 4)
  let byte5 ← ByteSelection.circuit (byteInput input spans 5)
  let byte6 ← ByteSelection.circuit (byteInput input spans 6)
  let byte7 ← ByteSelection.circuit (byteInput input spans 7)
  return Memory.joinBytes #v[byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7]

def output (input : Var Input Bit) (offset : ℕ) : Var (fields 64) Bit :=
  let spans := StoreSpans.circuit.output { low := input.low, high := input.high, amount := input.amount } offset
  Memory.joinBytes #v[
    ByteSelection.circuit.output (byteInput input spans 0) (offset + 4),
    ByteSelection.circuit.output (byteInput input spans 1) (offset + 14),
    ByteSelection.circuit.output (byteInput input spans 2) (offset + 24),
    ByteSelection.circuit.output (byteInput input spans 3) (offset + 34),
    ByteSelection.circuit.output (byteInput input spans 4) (offset + 44),
    ByteSelection.circuit.output (byteInput input spans 5) (offset + 54),
    ByteSelection.circuit.output (byteInput input spans 6) (offset + 64),
    ByteSelection.circuit.output (byteInput input spans 7) (offset + 74)]

instance elaborated : ElaboratedCircuit Bit Input (fields 64) main := by
  let base : ElaboratedCircuit Bit Input (fields 64) main := by elaborate_circuit
  exact {
    base with
    localLength := fun _ => 84
    localLength_eq := by intro input offset; simp only [main, circuit_norm]
    output := output
    output_eq := by intro input offset; simp only [main, output, circuit_norm]
  }

def circuit : FormalCircuit Bit Input (fields 64) where
  main
  elaborated
  Spec := fun input output => output = select input
  soundness := by
    circuit_proof_start [main, output, byteInput, ByteSelection.Spec]
    rcases h_input with ⟨hl, hh, ha, hv, hc⟩
    simp only [Memory.byte_map, Memory.joinBytes_map, circuit_norm, hv, hc] at h_holds ⊢
    rcases h_holds with ⟨hspans, h0, h1, h2, h3, h4, h5, h6, h7⟩
    norm_num only [Nat.add_assoc] at h0 h1 h2 h3 h4 h5 h6 h7
    simp only [select]
    congr 1
    apply Vector.ext
    intro i hi
    interval_cases i
    · simpa [circuit_norm, StoreSpans.contains, hspans] using h0
    · simpa [circuit_norm, StoreSpans.contains, hspans] using h1
    · simpa [circuit_norm, StoreSpans.contains, hspans] using h2
    · simpa [circuit_norm, StoreSpans.contains, hspans] using h3
    · simpa [circuit_norm, StoreSpans.contains, hspans] using h4
    · simpa [circuit_norm, StoreSpans.contains, hspans] using h5
    · simp only [circuit_norm, StoreSpans.contains]
      split_ifs <;> simp_all [circuit_norm] <;> tauto
    · simp only [circuit_norm, StoreSpans.contains]
      split_ifs <;> simp_all [circuit_norm] <;> tauto
  completeness := by circuit_proof_start [main, byteInput]

@[circuit_norm] theorem circuit_assumptions (input : Input Bit) :
    circuit.Assumptions input = True := rfl

@[circuit_norm] theorem circuit_spec (input : Input Bit) (value : Vector Bit 64) :
    circuit.Spec input value = (value = select input) := rfl

@[circuit_norm] theorem circuit_requirements :
    circuit.channelsWithRequirements = [] := by rfl

@[circuit_norm] theorem circuit_guarantees :
    circuit.channelsWithGuarantees = [] := by rfl

@[circuit_norm] theorem circuit_length (input : Var Input Bit) :
    circuit.localLength input = 84 := rfl

end LeanVMCircuits.StoreMask
