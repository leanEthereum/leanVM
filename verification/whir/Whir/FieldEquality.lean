import Whir.Concrete

/-! Boolean equality for the concrete three-word extension representation is exact.
This depends only on UInt64 equality, not on any field arithmetic theorem. -/
namespace Whir.Concrete

theorem E_beq_iff (a b : E) : (a == b) = true ↔ a = b := by
  cases a
  cases b
  simp [BEq.beq, instBEqE.beq]

instance : LawfulBEq E where
  rfl := (E_beq_iff _ _).mpr rfl
  eq_of_beq := (E_beq_iff _ _).mp

end Whir.Concrete
