module

public import Clean.Circuit.Subcircuit
public import Clean.Utils.Tactics
public import Clean.Utils.Tactics.ProvableStructDeriving
public import Mathlib.Tactic

@[expose] public section

namespace LeanVMCircuits

abbrev Bit := F 2

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

namespace FullAdder

structure Input (F : Type) where
  x : F
  y : F
  carry : F
  deriving ProvableStruct

structure Output (F : Type) where
  sum : F
  carry : F
  deriving ProvableStruct

/-- One GF(2) product implements majority; the sum is affine. -/
def main (input : Var Input Bit) : Circuit Bit (Var Output Bit) := do
  let xc := input.x + input.carry
  let yc := input.y + input.carry
  let product ← witness (xc * yc)
  assertZero (product - xc * yc)
  return { sum := xc + input.y, carry := product + input.carry }

/-- Independent integer addition of three bits, including the carry out. -/
def Spec (input : Input Bit) (output : Output Bit) : Prop :=
  output.sum.val + 2 * output.carry.val = input.x.val + input.y.val + input.carry.val

instance elaborated : ElaboratedCircuit Bit Input Output main := by
  elaborate_circuit

theorem bit_addition (x y c : Bit) :
    (x + c + y).val + 2 * ((x + c) * (y + c) + c).val = x.val + y.val + c.val := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hc := ZMod.val_lt c
  have ex : x = (x.val : Bit) := (ZMod.natCast_zmod_val x).symm
  have ey : y = (y.val : Bit) := (ZMod.natCast_zmod_val y).symm
  have ec : c = (c.val : Bit) := (ZMod.natCast_zmod_val c).symm
  interval_cases hxx : x.val <;> interval_cases hyy : y.val <;> interval_cases hcc : c.val <;>
    simp_all <;> decide

theorem soundness : Soundness Bit main (fun _ => True) Spec := by
  circuit_proof_start
  rcases h_input with ⟨hx, hy, hc⟩
  rw [sub_eq_zero] at h_holds
  rw [h_holds]
  exact bit_addition _ _ _

theorem completeness : Completeness Bit main (fun _ => True) := by
  circuit_proof_start
  simp_all

@[circuit_norm]
def circuit : FormalCircuit Bit Input Output where
  main
  elaborated
  Spec
  soundness
  completeness

end FullAdder

namespace Adder

structure Input (n : ℕ) (F : Type) where
  x : Vector F n
  y : Vector F n
  carry : F
  deriving ProvableStruct

structure Output (n : ℕ) (F : Type) where
  sum : Vector F n
  carry : F
  deriving ProvableStruct

/-- Little-endian unsigned interpretation, independent of circuit constraints. -/
def value {n : ℕ} (bits : Vector Bit n) : ℕ :=
  bits.toList.foldr (fun b acc => b.val + 2 * acc) 0

theorem value_push {n : ℕ} (bits : Vector Bit n) (b : Bit) :
    value (bits.push b) = value bits + 2 ^ n * b.val := by
  induction bits using Vector.induct with
  | nil => simp [value]
  | @cons n head tail ih =>
    rw [Vector.listCons_push]
    simp only [value, Vector.toList_listCons, List.foldr_cons] at *
    rw [ih, pow_succ]
    ring

theorem value_zero (bits : Vector Bit 0) : value bits = 0 := by
  have h : bits = #v[] := by ext i hi; omega
  simp [h, value]

theorem value_pop {n : ℕ} (bits : Vector Bit (n + 1)) :
    value bits = value bits.pop + 2 ^ n * bits[n].val := by
  have h := value_push bits.pop bits.back
  rw [Vector.push_pop_back, Vector.back_eq_getElem] at h
  exact h

theorem value_lt {n : ℕ} (bits : Vector Bit n) : value bits < 2 ^ n := by
  induction bits using Vector.induct with
  | nil => simp [value]
  | @cons n head tail ih =>
    have hbit := ZMod.val_lt head
    simp only [value, Vector.toList_listCons, List.foldr_cons, pow_succ] at *
    omega

def Spec (n : ℕ) (input : Input n Bit) (output : Output n Bit) : Prop :=
  value output.sum + 2 ^ n * output.carry.val = value input.x + value input.y + input.carry.val

/-- Metadata invariants keep recursive subcircuit specifications opaque to Clean's elaborator. -/
structure Certified (n : ℕ) where
  circuit : FormalCircuit Bit (Input n) (Output n)
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec n
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = n

@[circuit_norm] theorem certified_length (n : ℕ) (previous : Certified n) (input : Var (Input n) Bit) :
    previous.circuit.elaborated.localLength input = n := previous.length_eq input

def zero : Certified 0 where
  circuit := {
    main := fun input => pure { sum := #v[], carry := input.carry }
    Spec := Spec 0
    soundness := by
      circuit_proof_start
      simp_all [value_zero, circuit_norm]
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
      let lower ← previous.circuit { x := input.x.pop, y := input.y.pop, carry := input.carry }
      let upper ← FullAdder.circuit { x := input.x[n], y := input.y[n], carry := lower.carry }
      return { sum := lower.sum.push upper.sum, carry := upper.carry }
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by
      simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [FullAdder.circuit, FullAdder.Spec]
      simp only [previous.assumptions_eq, previous.spec_eq,
        previous.requirements_eq, true_implies, or_true] at *
      simp only [Spec, FormalCircuitBase.output, ← ElaboratedCircuit.output_eq] at h_holds ⊢
      generalize hlow : (previous.circuit.main
        { x := input_var_x.pop, y := input_var_y.pop, carry := input_var_carry }).output i₀ = low at *
      rcases low with ⟨ls, lc⟩
      provable_struct_simp
      simp only [Vector.map_push, value_push, circuit_norm] at h_holds ⊢
      rcases h_input with ⟨hx, hy, hc⟩
      have hxbit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hx
      have hybit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hy
      simp only [Vector.getElem_map] at hxbit hybit
      simp only [hxbit, hybit, Vector.map_pop, hx, hy] at h_holds ⊢
      rw [value_pop input_x, value_pop input_y, pow_succ]
      rcases h_holds with ⟨hlower, hupper⟩
      simp only [FormalCircuitBase.localLength, certified_length] at hupper ⊢
      nlinarith [congrArg (fun v : ℕ => 2 ^ n * v) hupper]
    completeness := by
      circuit_proof_start [FullAdder.circuit, FullAdder.Spec]
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

/-- Clean composes certified one-bit adders in least-significant-bit product order. -/
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

end Adder

namespace WrappingAdder

structure Input (n : ℕ) (F : Type) where
  x : Vector F n
  y : Vector F n
  deriving ProvableStruct

/-- The final sum is affine. The discarded overflow has no witness or product slot. -/
def main (n : ℕ) (input : Var (Input (n + 1)) Bit) : Circuit Bit (Var (fields (n + 1)) Bit) := do
  let lower ← Adder.circuit n { x := input.x.pop, y := input.y.pop, carry := 0 }
  return lower.sum.push (input.x[n] + lower.carry + input.y[n])

instance elaborated (n : ℕ) : ElaboratedCircuit Bit (Input (n + 1)) (fields (n + 1)) (main n) := by
  elaborate_circuit

def Spec (n : ℕ) (input : Input (n + 1) Bit) (output : Vector Bit (n + 1)) : Prop :=
  Adder.value output = (Adder.value input.x + Adder.value input.y) % 2 ^ (n + 1)

theorem wrapping_value {n : ℕ} (x y : Vector Bit (n + 1)) (sum : Vector Bit n) (carry : Bit)
    (h : Adder.value sum + 2 ^ n * carry.val = Adder.value x.pop + Adder.value y.pop) :
    Adder.value (sum.push (x[n] + carry + y[n])) =
      (Adder.value x + Adder.value y) % 2 ^ (n + 1) := by
  have hupper := FullAdder.bit_addition x[n] y[n] carry
  have htotal : Adder.value x + Adder.value y =
      Adder.value (sum.push (x[n] + carry + y[n])) +
        ((x[n] + carry) * (y[n] + carry) + carry).val * 2 ^ (n + 1) := by
    rw [Adder.value_pop x, Adder.value_pop y, Adder.value_push, pow_succ]
    nlinarith [congrArg (fun v : ℕ => 2 ^ n * v) hupper]
  rw [htotal]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (Adder.value_lt _)]

def circuit (n : ℕ) : FormalCircuit Bit (Input (n + 1)) (fields (n + 1)) where
  main := main n
  elaborated := elaborated n
  Spec := Spec n
  soundness := by
    circuit_proof_start
    simp only [Adder.Spec, circuit_norm] at h_holds
    simp only [FormalCircuitBase.output, ← ElaboratedCircuit.output_eq] at h_holds ⊢
    generalize hlow : ((Adder.circuit n).main
      { x := input_var_x.pop, y := input_var_y.pop, carry := 0 }).output i₀ = low at *
    rcases low with ⟨ls, lc⟩
    provable_struct_simp
    simp only [Vector.map_push, circuit_norm] at h_holds ⊢
    rcases h_input with ⟨hx, hy⟩
    have hxbit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hx
    have hybit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hy
    simp only [Vector.getElem_map] at hxbit hybit
    simp only [hxbit, hybit, Vector.map_pop, hx, hy, circuit_norm] at h_holds ⊢
    simp only [Adder.circuit, Circuit.output] at hlow
    simp only [hlow, circuit_norm] at ⊢
    simp only [ZMod.val_zero, add_zero] at h_holds
    exact wrapping_value _ _ _ _ h_holds
  completeness := by circuit_proof_start

@[circuit_norm] theorem circuit_assumptions (n : ℕ) :
    (circuit n).Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec (n : ℕ) :
    (circuit n).Spec = Spec n := rfl
@[circuit_norm] theorem circuit_requirements (n : ℕ) :
    (circuit n).channelsWithRequirements = [] := by simp only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_guarantees (n : ℕ) :
    (circuit n).elaborated.channelsWithGuarantees = [] := by
  dsimp +instances only [circuit, elaborated]
  exact Adder.circuit_guarantees n
@[circuit_norm] theorem circuit_length (n : ℕ) (input : Var (Input (n + 1)) Bit) :
    (circuit n).localLength input = n := by
  dsimp +instances only [FormalCircuitBase.localLength, circuit, elaborated]
  simp only [circuit_norm]

/-- The production doubleword memory-address circuit. -/
def adder64 := circuit 63

end WrappingAdder
end LeanVMCircuits
