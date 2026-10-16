module

public import LeanVMCircuits.BitOps

@[expose] public section

namespace LeanVMCircuits.WordMux

structure Input (n : ℕ) (F : Type) where
  selector : F
  x : Vector F n
  y : Vector F n
  deriving ProvableStruct

def select (n : ℕ) (input : Input n Bit) : Vector Bit n :=
  if input.selector = 1 then input.x else input.y

def Spec (n : ℕ) (input : Input n Bit) (output : Vector Bit n) : Prop := output = select n input

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
      have hx : input_x = #v[] := by apply Vector.ext; intro i hi; omega
      have hy : input_y = #v[] := by apply Vector.ext; intro i hi; omega
      simp_all [select, circuit_norm]
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
      let lower ← previous.circuit { selector := input.selector, x := input.x.pop, y := input.y.pop }
      let upper ← Mux.circuit { selector := input.selector, x := input.x[n], y := input.y[n] }
      return lower.push upper
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [Mux.circuit, Mux.Spec]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, ← ElaboratedCircuit.output_eq,
        FormalCircuitBase.localLength, certified_length, Vector.map_push, circuit_norm] at h_holds ⊢
      rcases h_input with ⟨hs, hx, hy⟩
      have hxbit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hx
      have hybit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hy
      simp only [Vector.getElem_map] at hxbit hybit
      simp only [Vector.map_pop, hx, hy, hxbit, hybit] at h_holds ⊢
      rcases h_holds with ⟨hlower, hupper⟩
      rw [hlower, hupper]
      have hxrebuild : input_x.pop.push input_x[n] = input_x := input_x.push_pop_back
      have hyrebuild : input_y.pop.push input_y[n] = input_y := input_y.push_pop_back
      by_cases h : input_selector = 1 <;> simp [select, Mux.select, h, hxrebuild, hyrebuild]
    completeness := by
      circuit_proof_start [Mux.circuit, Mux.Spec]
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
@[circuit_norm] theorem circuit_spec (n : ℕ) :
    (circuit n).Spec = Spec n := (certified n).spec_eq
@[circuit_norm] theorem circuit_requirements (n : ℕ) :
    (circuit n).channelsWithRequirements = [] := (certified n).requirements_eq
@[circuit_norm] theorem circuit_guarantees (n : ℕ) :
    (circuit n).elaborated.channelsWithGuarantees = [] := (certified n).guarantees_eq
@[circuit_norm] theorem circuit_length (n : ℕ) (input : Var (Input n) Bit) :
    (circuit n).localLength input = n := (certified n).length_eq input

end LeanVMCircuits.WordMux
