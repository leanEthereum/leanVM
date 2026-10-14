import Whir.Concrete
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

/-! Cardinalities of the executable carriers, independently of any field laws. -/
namespace Whir.FieldModel
open Concrete

/-- The machine word representation is exactly a 64-bit finite ordinal. -/
def wordEquiv : K ≃ Fin (2^64) where
  toFun := UInt64.toFin
  invFun := UInt64.ofFin
  left_inv := by intro a; rfl
  right_inv := by intro a; rfl

/-- Cardinality evidence is proof-only: compiling this enumeration would
eagerly allocate all 2^64 elements during executable module initialization. -/
noncomputable instance : Fintype K := Fintype.ofEquiv (Fin (2^64)) wordEquiv.symm

/-- The extension carrier has three independent machine-word coordinates. -/
def extensionEquiv : E ≃ K × K × K where
  toFun a := (a.c0, a.c1, a.c2)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro a; rcases a with ⟨a,b,c⟩; rfl

noncomputable instance : Fintype E := Fintype.ofEquiv (K × K × K) extensionEquiv.symm

@[simp] theorem card_K : Fintype.card K = 2^64 := by
  rw [Fintype.card_congr wordEquiv, Fintype.card_fin]

@[simp] theorem card_E : Fintype.card E = 2^192 := by
  rw [Fintype.card_congr extensionEquiv, Fintype.card_prod, Fintype.card_prod, card_K]
  norm_num

@[simp] theorem natCard_E : Nat.card E = 2^192 := by
  rw [Nat.card_eq_fintype_card, card_E]

end Whir.FieldModel
