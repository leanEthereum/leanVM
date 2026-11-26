/-
  Rv64mc.Spec.Field.Basic

  How the field's values sit in registers: a `u128` is returned and passed in two registers, its low word first
  (`a0`, then `a1`), and an `E` by value as its limbs `c0`, `c1` (`Model.Limbs`), so `self` in `a0`, `a1` and the
  second operand in `a2`, `a3`.
-/

import Rv64mc.Core.Holds
import Rv64mc.Model.Field

namespace Rv64mc.Spec.Field

open RiscvZkvm.Rv64

/-- The low word of a `u128`: the register it is returned in first. -/
def lo128 (x : BitVec 128) : Word := x.setWidth 64

/-- The high word of a `u128`. -/
def hi128 (x : BitVec 128) : Word := (x >>> 64).setWidth 64

end Rv64mc.Spec.Field
