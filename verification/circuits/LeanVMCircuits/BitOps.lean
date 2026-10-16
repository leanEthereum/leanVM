module

public import LeanVMCircuits.AdderFamily

@[expose] public section

namespace LeanVMCircuits.Mux

structure Input (F : Type) where
  selector : F
  x : F
  y : F
  deriving ProvableStruct

def select (selector x y : Bit) : Bit := if selector = 1 then x else y

def main (input : Var Input Bit) : Circuit Bit (Expression Bit) := do
  let product ← witness (input.selector * (input.x + input.y))
  assertZero (product - input.selector * (input.x + input.y))
  return input.y + product

def Spec (input : Input Bit) (output : Bit) : Prop := output = select input.selector input.x input.y

instance elaborated : ElaboratedCircuit Bit Input field main := by elaborate_circuit

theorem selection (selector x y : Bit) : y + selector * (x + y) = select selector x y := by
  have hs := ZMod.val_lt selector
  have es : selector = (selector.val : Bit) := (ZMod.natCast_zmod_val selector).symm
  interval_cases hss : selector.val <;> simp_all [select]
  have hyy : y + y = 0 := by
    simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel y
  calc
    y + (x + y) = x + (y + y) := by ac_rfl
    _ = x := by rw [hyy, add_zero]

theorem not_selection (selector x : Bit) : select (1 + selector) x 0 = if selector = 1 then 0 else x := by
  have hs := ZMod.val_lt selector
  have es : selector = (selector.val : Bit) := (ZMod.natCast_zmod_val selector).symm
  interval_cases hss : selector.val <;> simp_all [select]

@[circuit_norm]
def circuit : FormalCircuit Bit Input field where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start
    rw [sub_eq_zero] at h_holds
    rw [h_holds]
    exact selection _ _ _
  completeness := by circuit_proof_start; simp_all

end LeanVMCircuits.Mux
