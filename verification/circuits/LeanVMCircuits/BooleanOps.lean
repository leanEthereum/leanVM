module

public import LeanVMCircuits.BitOps

@[expose] public section

namespace LeanVMCircuits.Product

structure Input (F : Type) where
  x : F
  y : F
  deriving ProvableStruct

def main (input : Var Input Bit) : Circuit Bit (Expression Bit) := do
  let product ← witness (input.x * input.y)
  assertZero (product - input.x * input.y)
  return product

def Spec (input : Input Bit) (output : Bit) : Prop := output = input.x * input.y

instance elaborated : ElaboratedCircuit Bit Input field main := by elaborate_circuit

@[circuit_norm]
def circuit : FormalCircuit Bit Input field where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start
    exact sub_eq_zero.mp h_holds
  completeness := by circuit_proof_start; simp_all

end LeanVMCircuits.Product

namespace LeanVMCircuits

theorem bit_zero_or_one (x : Bit) : x = 0 ∨ x = 1 := by
  have hx := ZMod.val_lt x
  have ex : x = (x.val : Bit) := (ZMod.natCast_zmod_val x).symm
  interval_cases hxx : x.val <;> simp_all

@[simp] theorem bit_one_val : (1 : Bit).val = 1 := by decide

@[simp] theorem bit_one_add_one : (1 : Bit) + 1 = 0 := by decide

namespace BooleanOr

def main (input : Var Product.Input Bit) : Circuit Bit (Expression Bit) := do
  let product ← Product.circuit input
  return input.x + input.y + product

def select (x y : Bit) : Bit := if x = 1 ∨ y = 1 then 1 else 0

theorem selection (x y : Bit) : x + y + x * y = select x y := by
  rcases bit_zero_or_one x with rfl | rfl <;>
    rcases bit_zero_or_one y with rfl | rfl <;> decide

instance elaborated : ElaboratedCircuit Bit Product.Input field main := by elaborate_circuit

@[circuit_norm]
def circuit : FormalCircuit Bit Product.Input field where
  main
  elaborated
  Spec := fun input output => output = select input.x input.y
  soundness := by
    circuit_proof_start [Product.circuit, Product.Spec]
    rw [h_holds]
    exact selection _ _
  completeness := by circuit_proof_start [Product.circuit]

end BooleanOr
end LeanVMCircuits
