module

public import LeanVMCircuits.BooleanOps

@[expose] public section

namespace LeanVMCircuits.WordScale

structure Input (n : ℕ) (F : Type) where
  selector : F
  word : Vector F n
  deriving ProvableStruct

def select (n : ℕ) (input : Input n Bit) : Vector Bit n := input.word.map (input.selector * ·)

def Spec (n : ℕ) (input : Input n Bit) (output : Vector Bit n) : Prop := output = select n input

theorem select_boolean (n : ℕ) (input : Input n Bit) :
    select n input = if input.selector = 1 then input.word else Vector.replicate n 0 := by
  rcases bit_zero_or_one input.selector with hs | hs
  · apply Vector.ext
    intro i hi
    simp [select, hs]
  · simp [select, hs]

structure Certified (n : ℕ) where
  circuit : FormalCircuit Bit (Input n) (fields n)
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec n
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = n

@[circuit_norm] theorem certified_length (n : ℕ) (previous : Certified n) (input : Var (Input n) Bit) :
    previous.circuit.elaborated.localLength input = n := previous.length_eq input
@[circuit_norm] theorem certified_guarantees (n : ℕ) (previous : Certified n) :
    previous.circuit.elaborated.channelsWithGuarantees = [] := previous.guarantees_eq

def zero : Certified 0 where
  circuit := {
    main := fun _ => pure #v[]
    Spec := Spec 0
    soundness := by
      circuit_proof_start
      simp [select, circuit_norm]
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
      let lower ← previous.circuit { selector := input.selector, word := input.word.pop }
      let upper ← Product.circuit { x := input.selector, y := input.word[n] }
      return lower.push upper
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [Product.circuit, Product.Spec]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, select, FormalCircuitBase.output, FormalCircuitBase.localLength,
        certified_length, Vector.map_push, circuit_norm] at h_holds ⊢
      rcases h_input with ⟨hs, hw⟩
      have hb := congrArg (fun word : Vector Bit (n + 1) => word[n]) hw
      simp only [Vector.getElem_map] at hb
      simp only [Vector.map_pop, hw, hb] at h_holds ⊢
      rcases h_holds with ⟨hlower, hupper⟩
      conv_lhs => arg 1; rw [hlower]
      conv_lhs => arg 2; rw [hupper]
      simpa only [Vector.back_eq_getElem, Nat.add_sub_cancel, Vector.getElem_map] using
        (input_word.map (input_selector * ·)).push_pop_back
    completeness := by
      circuit_proof_start [Product.circuit, Product.Spec]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by
    intro input
    simp only [circuit_norm, certified_length]

def certified : (n : ℕ) → Certified n
  | 0 => zero
  | n + 1 => step n (certified n)

def circuit (n : ℕ) := (certified n).circuit

@[circuit_norm] theorem circuit_assumptions (n : ℕ) :
    (circuit n).Assumptions = fun _ => True := (certified n).assumptions_eq
@[circuit_norm] theorem circuit_spec (n : ℕ) : (circuit n).Spec = Spec n := (certified n).spec_eq
@[circuit_norm] theorem circuit_requirements (n : ℕ) :
    (circuit n).channelsWithRequirements = [] := (certified n).requirements_eq
@[circuit_norm] theorem circuit_guarantees (n : ℕ) :
    (circuit n).elaborated.channelsWithGuarantees = [] := (certified n).guarantees_eq
@[circuit_norm] theorem circuit_length (n : ℕ) (input : Var (Input n) Bit) :
    (circuit n).localLength input = n := (certified n).length_eq input

end LeanVMCircuits.WordScale
