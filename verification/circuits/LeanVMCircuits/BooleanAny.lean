module

public import LeanVMCircuits.BooleanOps

@[expose] public section

namespace LeanVMCircuits.BooleanAny

def present {n : ℕ} (word : Vector Bit n) : Prop := 1 ∈ word.toList

instance {n : ℕ} (word : Vector Bit n) : Decidable (present word) := inferInstanceAs (Decidable (1 ∈ word.toList))

theorem present_push {n : ℕ} (word : Vector Bit n) (bit : Bit) :
    present (word.push bit) ↔ present word ∨ bit = 1 := by
  simp [present, Vector.toList_push, eq_comm]

theorem present_pop {n : ℕ} (word : Vector Bit (n + 1)) :
    present word ↔ present word.pop ∨ word[n] = 1 := by
  conv_lhs => rw [← word.push_pop_back]
  simpa only [Vector.back_eq_getElem, Nat.add_sub_cancel] using present_push word.pop word.back

structure Input (n : ℕ) (F : Type) where
  word : Vector F n
  deriving ProvableStruct

def Spec (n : ℕ) (input : Input (n + 1) Bit) (output : Bit) : Prop :=
  output = if present input.word then 1 else 0

structure Certified (n : ℕ) where
  circuit : FormalCircuit Bit (Input (n + 1)) field
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec n
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = n

@[circuit_norm] theorem certified_length (n : ℕ) (previous : Certified n) (input : Var (Input (n + 1)) Bit) :
    previous.circuit.elaborated.localLength input = n := previous.length_eq input

@[circuit_norm] theorem certified_guarantees (n : ℕ) (previous : Certified n) :
    previous.circuit.elaborated.channelsWithGuarantees = [] := previous.guarantees_eq

def zero : Certified 0 where
  circuit := {
    main := fun input => pure input.word[0]
    Spec := Spec 0
    soundness := by
      circuit_proof_start
      have hw : input_word = #v[input_word[0]] := by
        apply Vector.ext
        intro i hi
        have he : i = 0 := by omega
        subst i
        simp
      simp only [circuit_norm] at *
      have hp : present input_word ↔ input_word[0] = 1 := by
        simp only [present, Vector.toList]
        rw [hw]
        simp [eq_comm]
      rcases bit_zero_or_one input_word[0] with hb | hb <;> simp [hp, hb]
    completeness := by circuit_proof_start
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := rfl
  length_eq := by intro input; rfl

def step (n : ℕ) (previous : Certified n) : Certified (n + 1) where
  circuit := {
    main := fun input => do
      let lower ← previous.circuit { word := input.word.pop }
      BooleanOr.circuit { x := lower, y := input.word[n + 1] }
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [BooleanOr.circuit]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, ← ElaboratedCircuit.output_eq,
        FormalCircuitBase.localLength, certified_length, circuit_norm, Vector.map_pop] at h_holds ⊢
      rw [h_input] at h_holds
      rcases h_holds with ⟨hlower, hupper⟩
      rw [hupper, hlower]
      have hbit := congrArg (fun word : Vector Bit (n + 1 + 1) => word[n + 1]) h_input
      simp only [Vector.getElem_map] at hbit
      rw [hbit]
      have hp := present_pop input_word
      by_cases h : present input_word.pop <;> simp [BooleanOr.select, hp, h]
    completeness := by
      circuit_proof_start [BooleanOr.circuit]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by intro input; simp only [circuit_norm, certified_length]

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
@[circuit_norm] theorem circuit_length (n : ℕ) (input : Var (Input (n + 1)) Bit) :
    (circuit n).localLength input = n := (certified n).length_eq input

end LeanVMCircuits.BooleanAny
