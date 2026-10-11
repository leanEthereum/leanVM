module

public import LeanVMCircuits.AluLogic

@[expose] public section

namespace LeanVMCircuits.AluLogicWord

structure Input (n : ℕ) (F : Type) where
  andOr : F
  orXor : F
  x : Vector F n
  y : Vector F n
  difference : Vector F n
  deriving ProvableStruct

def select (n : ℕ) (input : Input n Bit) : Vector Bit n :=
  Vector.mapFinRange n fun i =>
    input.andOr * (input.x[i] * input.y[i]) + input.orXor * input.difference[i]

def Spec (n : ℕ) (input : Input n Bit) (output : Vector Bit n) : Prop := output = select n input

theorem select_push (n : ℕ) (input : Input (n + 1) Bit) :
    select (n + 1) input =
      (select n {
        andOr := input.andOr
        orXor := input.orXor
        x := input.x.pop
        y := input.y.pop
        difference := input.difference.pop }).push
        (input.andOr * (input.x[n] * input.y[n]) + input.orXor * input.difference[n]) := by
  apply Vector.ext
  intro i hi
  by_cases h : i < n
  · simp [select, Vector.getElem_mapFinRange, h]
  · have he : i = n := by omega
    subst i
    simp [select, Vector.getElem_mapFinRange]

structure Certified (n : ℕ) where
  circuit : FormalCircuit Bit (Input n) (fields n)
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec n
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = 3 * n

@[circuit_norm] theorem certified_length (n : ℕ) (previous : Certified n) (input : Var (Input n) Bit) :
    previous.circuit.elaborated.localLength input = 3 * n := previous.length_eq input

@[circuit_norm] theorem certified_guarantees (n : ℕ) (previous : Certified n) :
    previous.circuit.elaborated.channelsWithGuarantees = [] := previous.guarantees_eq

def zero : Certified 0 where
  circuit := {
    main := fun _ => pure #v[]
    Spec := Spec 0
    soundness := by
      circuit_proof_start
      simp [select]
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
      let lower ← previous.circuit {
        andOr := input.andOr
        orXor := input.orXor
        x := input.x.pop
        y := input.y.pop
        difference := input.difference.pop }
      let upper ← AluLogic.circuit {
        andOr := input.andOr
        orXor := input.orXor
        x := input.x[n]
        y := input.y[n]
        difference := input.difference[n] }
      return lower.push upper
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [AluLogic.Spec]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, FormalCircuitBase.localLength,
        certified_length, Vector.map_push, circuit_norm] at h_holds ⊢
      rcases h_input with ⟨ha, ho, hx, hy, hd⟩
      have hxb := congrArg (fun word : Vector Bit (n + 1) => word[n]) hx
      have hyb := congrArg (fun word : Vector Bit (n + 1) => word[n]) hy
      have hdb := congrArg (fun word : Vector Bit (n + 1) => word[n]) hd
      simp only [Vector.getElem_map] at hxb hyb hdb
      simp only [Vector.map_pop, hx, hy, hd, hxb, hyb, hdb] at h_holds ⊢
      rcases h_holds with ⟨hlower, hupper⟩
      change env.get (i₀ + 3 * n + 1) + env.get (i₀ + 3 * n + 1 + 1) = _ at hupper
      conv_lhs => arg 1; rw [hlower]
      conv_lhs => arg 2; rw [hupper]
      exact (select_push n {
        andOr := input_andOr
        orXor := input_orXor
        x := input_x
        y := input_y
        difference := input_difference
      }).symm
    completeness := by
      circuit_proof_start [AluLogic.Spec]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
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
@[circuit_norm] theorem circuit_length (n : ℕ) (input : Var (Input n) Bit) :
    (circuit n).localLength input = 3 * n := (certified n).length_eq input

end LeanVMCircuits.AluLogicWord
