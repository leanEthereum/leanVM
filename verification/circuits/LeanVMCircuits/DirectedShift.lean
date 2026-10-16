module

public import LeanVMCircuits.ShiftPreparation

@[expose] public section

namespace LeanVMCircuits.DirectedShift

structure Input (F : Type) where
  amount : Vector F 6
  fill : F
  right : F
  word : Vector F 64
  deriving ProvableStruct

def Assumptions (input : Input Bit) : Prop := input.right = 1 ∨ input.fill = 0

def Spec (input : Input Bit) (output : Vector Bit 64) : Prop :=
  output = if input.right = 1 then Words.right (Adder.value input.amount) input.fill input.word
    else Words.left (Adder.value input.amount) 0 input.word

def main (barrel : BarrelShift.Certified 6) (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let forward ← ReverseUnless.circuit { selector := input.right, word := input.word }
  let shifted ← barrel.circuit { amount := input.amount, fill := input.fill, word := forward }
  ReverseUnless.circuit { selector := input.right, word := shifted }

instance elaborated (barrel : BarrelShift.Certified 6) : ElaboratedCircuit Bit Input (fields 64) (main barrel) where
  localLength _ := 512
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, FormalCircuitBase.localLength, BarrelShift.certified_length]
  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]
    and_intros <;> ac_rfl
  channelsLawful := by
    simp [ElaboratedCircuit.ChannelsLawful, main, circuit_norm,
      FormalCircuitBase.channelsWithGuarantees, barrel.guarantees_eq]

def build (barrel : BarrelShift.Certified 6) : FormalCircuit Bit Input (fields 64) where
  main := main barrel
  elaborated := elaborated barrel
  Assumptions
  Spec
  requirementsChannelsLawful := by simp only [main, circuit_norm, barrel.requirements_eq]
  soundness := by
    circuit_proof_start [main, Assumptions, Spec]
    simp only [barrel.assumptions_eq, barrel.spec_eq, barrel.requirements_eq,
      true_implies, or_true, and_true, BarrelShift.Spec] at *
    rcases h_holds with ⟨hf, hb, hr⟩
    simp only [circuit_norm, FormalCircuitBase.output, ← ElaboratedCircuit.output_eq,
      FormalCircuitBase.localLength, BarrelShift.certified_length] at hf hb hr ⊢
    by_cases h : input_right = 1
    · simp [h] at hf hr ⊢
      rw [hf] at hb
      rw [hr]
      exact hb
    · have hz : input_fill = 0 := h_assumptions.resolve_left h
      simp [h] at hf hr ⊢
      rw [hf] at hb
      rw [hr, hb, hz, Words.reverse_right]
  completeness := by
    circuit_proof_start [main]
    simp [barrel.assumptions_eq]

def circuit := build (BarrelShift.certified 6)

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = Assumptions := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl

end LeanVMCircuits.DirectedShift
