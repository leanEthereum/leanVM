module

public import LeanVMCircuits.ShiftStages

@[expose] public section

namespace LeanVMCircuits.BarrelShift

structure Input (n : ℕ) (F : Type) where
  amount : Vector F n
  fill : F
  word : Vector F 64
  deriving ProvableStruct

def Spec (n : ℕ) (input : Input n Bit) (output : Vector Bit 64) : Prop :=
  output = Words.right (Adder.value input.amount) input.fill input.word

theorem bit_weight (bit : Bit) (weight : ℕ) :
    (if bit = 1 then weight else 0) = weight * bit.val := by
  have hb := ZMod.val_lt bit
  have eb : bit = (bit.val : Bit) := (ZMod.natCast_zmod_val bit).symm
  interval_cases hbb : bit.val <;> simp_all

structure Certified (n : ℕ) where
  circuit : FormalCircuit Bit (Input n) (fields 64)
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec n
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = 64 * n

@[circuit_norm] theorem certified_length (n : ℕ) (previous : Certified n) (input : Var (Input n) Bit) :
    previous.circuit.elaborated.localLength input = 64 * n := previous.length_eq input

def zero : Certified 0 where
  circuit := {
    main := fun input => pure input.word
    Spec := Spec 0
    soundness := by
      circuit_proof_start
      simp_all [Adder.value_zero, Words.right_zero, circuit_norm]
    completeness := by circuit_proof_start
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := rfl
  length_eq := by intro input; simp only [circuit_norm, mul_zero]

def step (n : ℕ) (previous : Certified n) : Certified (n + 1) where
  circuit := {
    main := fun input => do
      let lower ← previous.circuit { amount := input.amount.pop, fill := input.fill, word := input.word }
      ShiftStage.circuit (2 ^ n) { selector := input.amount[n], fill := input.fill, word := lower }
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by
      simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [ShiftStage.circuit]
      simp only [previous.assumptions_eq, previous.spec_eq,
        previous.requirements_eq, true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, ← ElaboratedCircuit.output_eq] at h_holds ⊢
      simp only [FormalCircuitBase.localLength, certified_length] at h_holds ⊢
      rcases h_input with ⟨ha, hf, hw⟩
      have hab := congrArg (fun v : Vector Bit (n + 1) => v[n]) ha
      simp only [Vector.getElem_map] at hab
      simp only [Vector.map_pop, ha, hab] at h_holds ⊢
      rcases h_holds with ⟨hlower, hupper⟩
      rw [hlower] at hupper
      simp only [Words.right_add, bit_weight] at hupper
      rw [Adder.value_pop input_amount]
      convert hupper using 1
      congr 1
      ring
    completeness := by
      circuit_proof_start [ShiftStage.circuit]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by
    simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by
    intro input
    simp only [circuit_norm, certified_length]
    omega

def certified : (n : ℕ) → Certified n
  | 0 => zero
  | n + 1 => step n (certified n)

def circuit (n : ℕ) := (certified n).circuit

@[circuit_norm] theorem circuit_assumptions (n : ℕ) :
    (circuit n).Assumptions = fun _ => True := (certified n).assumptions_eq
@[circuit_norm] theorem circuit_spec (n : ℕ) :
    (circuit n).Spec = Spec n := (certified n).spec_eq
@[circuit_norm] theorem circuit_requirements (n : ℕ) :
    (circuit n).channelsWithRequirements = [] := (certified n).requirements_eq
@[circuit_norm] theorem circuit_guarantees (n : ℕ) :
    (circuit n).elaborated.channelsWithGuarantees = [] := (certified n).guarantees_eq

end LeanVMCircuits.BarrelShift
