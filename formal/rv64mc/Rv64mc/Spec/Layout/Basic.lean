/-
  Rv64mc.Spec.Layout.Basic

  How `layout.rs`'s small values sit in registers: a `bool` is `0` or `1` in one register, and an `Option<usize>`
  returned by value is its tag (`0` for `None`, `1` for `Some`) in `a0` and its value in `a1`, the value read only
  under `Some`.
-/

import Rv64mc.Core.Holds

namespace Rv64mc.Spec.Layout

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- A `bool` in a register. -/
def ofBool (b : Bool) : Word := if b then 1 else 0

/-- **The `Option<usize>` `o` is returned** in `a0` (the tag) and `a1` (the value, under `Some`). -/
def OptUsizeRet (r' : Reg → Word) (o : Option Nat) : Prop :=
  match o with
  | none => r' .x10 = 0#64
  | some v => r' .x10 = 1#64 ∧ r' .x11 = BitVec.ofNat 64 v

end Rv64mc.Spec.Layout
