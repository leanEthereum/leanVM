module

public import LeanVMCircuits.MemorySemantics
public import LeanVMCircuits.BarrelShift

@[expose] public section

namespace LeanVMCircuits.MemoryRightStage

structure Input (n : ℕ) (F : Type) where
  selector : F
  word : Vector F n
  deriving ProvableStruct

def main (n m amount : ℕ) (input : Var (Input n) Bit) : Circuit Bit (Var (fields m) Bit) :=
  WordMux.circuit m {
    selector := input.selector
    x := Words.resize m 0 (Words.right amount 0 input.word)
    y := Words.resize m 0 input.word
  }

instance elaborated (n m amount : ℕ) : ElaboratedCircuit Bit (Input n) (fields m) (main n m amount) := by
  elaborate_circuit

@[circuit_norm]
def circuit (n m amount : ℕ) : FormalCircuit Bit (Input n) (fields m) where
  main := main n m amount
  elaborated := elaborated n m amount
  Spec := fun input output =>
    output = Words.resize m 0 (Words.right (if input.selector = 1 then amount else 0) 0 input.word)
  soundness := by
    circuit_proof_start
    rcases h_input with ⟨hs, hw⟩
    simp only [WordMux.Spec, WordMux.select, circuit_norm, Words.resize_map, Words.right_map] at h_holds
    rw [hw] at h_holds
    dsimp +instances only [WordMux.circuit] at h_holds ⊢
    by_cases h : input_selector = 1 <;>
      simpa [h, Words.right_zero, FormalCircuitBase.output, WordMux.circuit, ← ElaboratedCircuit.output_eq] using h_holds
  completeness := by circuit_proof_start

end LeanVMCircuits.MemoryRightStage

namespace LeanVMCircuits.MemoryLeftStage

def main (n m amount : ℕ) (input : Var (MemoryRightStage.Input n) Bit) : Circuit Bit (Var (fields m) Bit) :=
  WordMux.circuit m {
    selector := input.selector
    x := Words.leftTo m amount 0 input.word
    y := Words.resize m 0 input.word
  }

instance elaborated (n m amount : ℕ) :
    ElaboratedCircuit Bit (MemoryRightStage.Input n) (fields m) (main n m amount) := by elaborate_circuit

@[circuit_norm]
def circuit (n m amount : ℕ) : FormalCircuit Bit (MemoryRightStage.Input n) (fields m) where
  main := main n m amount
  elaborated := elaborated n m amount
  Spec := fun input output =>
    output = Words.leftTo m (if input.selector = 1 then amount else 0) 0 input.word
  soundness := by
    circuit_proof_start
    rcases h_input with ⟨hs, hw⟩
    simp only [WordMux.Spec, WordMux.select, circuit_norm, Words.resize_map, Words.leftTo_map] at h_holds
    rw [hw] at h_holds
    dsimp +instances only [WordMux.circuit] at h_holds ⊢
    by_cases h : input_selector = 1 <;>
      simpa [h, Words.leftTo_zero, FormalCircuitBase.output, WordMux.circuit, ← ElaboratedCircuit.output_eq] using h_holds
  completeness := by circuit_proof_start

end LeanVMCircuits.MemoryLeftStage

namespace LeanVMCircuits.LoadShift

structure Input (F : Type) where
  amount : Vector F 3
  word : Vector F 64
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Var (fields 32) Bit) := do
  let first ← MemoryRightStage.circuit 64 64 8 { selector := input.amount[0], word := input.word }
  let second ← MemoryRightStage.circuit 64 64 16 { selector := input.amount[1], word := first }
  MemoryRightStage.circuit 64 32 32 { selector := input.amount[2], word := second }

instance elaborated : ElaboratedCircuit Bit Input (fields 32) main := by elaborate_circuit

def circuit : FormalCircuit Bit Input (fields 32) where
  main
  elaborated
  Spec := fun input output => output = Words.resize 32 0 (Words.right (8 * Adder.value input.amount) 0 input.word)
  soundness := by
    circuit_proof_start [MemoryRightStage.circuit]
    rcases h_holds with ⟨hfirst, hsecond, hthird⟩
    have hbit0 := congrArg (fun v : Vector Bit 3 => v[0]) h_input.1
    have hbit1 := congrArg (fun v : Vector Bit 3 => v[1]) h_input.1
    have hbit2 := congrArg (fun v : Vector Bit 3 => v[2]) h_input.1
    simp only [Vector.getElem_map] at hbit0 hbit1 hbit2
    simp only [hbit0, hbit1, hbit2] at hfirst hsecond hthird
    simp only [Words.resize_self] at hfirst hsecond hthird ⊢
    rw [hfirst] at hsecond
    rw [hsecond] at hthird
    simp only [Words.right_add, BarrelShift.bit_weight] at hthird
    convert hthird using 1
    congr 3
    rw [Adder.value_three]
    ring
  completeness := by circuit_proof_start [MemoryRightStage.circuit]

@[circuit_norm] theorem circuit_assumptions :
    circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec :
    circuit.Spec = fun input output =>
      output = Words.resize 32 0 (Words.right (8 * Adder.value input.amount) 0 input.word) := rfl
@[circuit_norm] theorem circuit_requirements :
    circuit.channelsWithRequirements = [] := by simp only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_guarantees :
    circuit.elaborated.channelsWithGuarantees = [] := by
  dsimp +instances only [circuit, elaborated]
  simp only [circuit_norm]

@[circuit_norm] theorem circuit_length (input : Var Input Bit) :
    circuit.localLength input = 160 := by
  change ElaboratedCircuit.localLength main input = 160
  rw [← ElaboratedCircuit.localLength_eq (main := main) input 0]
  simp only [main, MemoryRightStage.circuit, circuit_norm]

end LeanVMCircuits.LoadShift

namespace LeanVMCircuits.StoreShift

structure Input (F : Type) where
  amount : Vector F 3
  word : Vector F 32
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let first ← MemoryLeftStage.circuit 32 40 8 { selector := input.amount[0], word := input.word }
  let second ← MemoryLeftStage.circuit 40 56 16 { selector := input.amount[1], word := first }
  MemoryLeftStage.circuit 56 64 32 { selector := input.amount[2], word := second }

instance elaborated : ElaboratedCircuit Bit Input (fields 64) main := by elaborate_circuit

def circuit : FormalCircuit Bit Input (fields 64) where
  main
  elaborated
  Spec := fun input output => output = Words.leftTo 64 (8 * Adder.value input.amount) 0 input.word
  soundness := by
    circuit_proof_start [MemoryLeftStage.circuit]
    rcases h_holds with ⟨hfirst, hsecond, hthird⟩
    have hbit0 := congrArg (fun v : Vector Bit 3 => v[0]) h_input.1
    have hbit1 := congrArg (fun v : Vector Bit 3 => v[1]) h_input.1
    have hbit2 := congrArg (fun v : Vector Bit 3 => v[2]) h_input.1
    simp only [Vector.getElem_map] at hbit0 hbit1 hbit2
    simp only [hbit0, hbit1, hbit2] at hfirst hsecond hthird
    simp only [BarrelShift.bit_weight] at hfirst hsecond hthird
    have hb0 := ZMod.val_lt input_amount[0]
    have hb1 := ZMod.val_lt input_amount[1]
    have hfits0 : 32 + 8 * input_amount[0].val ≤ 40 := by omega
    have hfits1 : 32 + (16 * input_amount[1].val + 8 * input_amount[0].val) ≤ 56 := by omega
    rw [hfirst, Words.leftTo_add 56 40 _ _ _ _ hfits0] at hsecond
    rw [hsecond, Words.leftTo_add 64 56 _ _ _ _ hfits1] at hthird
    convert hthird using 1
    congr 2
    rw [Adder.value_three]
    ring
  completeness := by circuit_proof_start [MemoryLeftStage.circuit]

@[circuit_norm] theorem circuit_assumptions :
    circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec :
    circuit.Spec = fun input output =>
      output = Words.leftTo 64 (8 * Adder.value input.amount) 0 input.word := rfl
@[circuit_norm] theorem circuit_requirements :
    circuit.channelsWithRequirements = [] := by simp only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_guarantees :
    circuit.elaborated.channelsWithGuarantees = [] := by
  dsimp +instances only [circuit, elaborated]
  simp only [circuit_norm]

@[circuit_norm] theorem circuit_length (input : Var Input Bit) :
    circuit.localLength input = 160 := by
  change ElaboratedCircuit.localLength main input = 160
  rw [← ElaboratedCircuit.localLength_eq (main := main) input 0]
  simp only [main, MemoryLeftStage.circuit, circuit_norm]

end LeanVMCircuits.StoreShift
