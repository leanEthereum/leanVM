/-
  Rv64mc.Tactic.RegFile

  A register file as its 32 values (`rf`), the form `rv_sym` keeps one in: a register is read by an instance of
  `rf_get_<r>` and written by one of `rf_set_<r>`, so that neither a read nor a write is a reduction the kernel has to
  find, and a read costs the same however many writes came before it.

  ## Main definitions

  * `rf`

  ## Main results

  * `rf_get_<r>`, `rf_set_<r>`: a read and a write of register `r`
  * `rf_eta`: any register file as the `rf` of its values
-/

import LprogRiscV.Lsym

namespace Rv64mc.Tactic

open RiscvZkvm.Rv64 Lprog

/-- The register file whose register `xk` holds `ak`. -/
def rf (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 : Word) : Reg → Word
  | .x0 => a0
  | .x1 => a1
  | .x2 => a2
  | .x3 => a3
  | .x4 => a4
  | .x5 => a5
  | .x6 => a6
  | .x7 => a7
  | .x8 => a8
  | .x9 => a9
  | .x10 => a10
  | .x11 => a11
  | .x12 => a12
  | .x13 => a13
  | .x14 => a14
  | .x15 => a15
  | .x16 => a16
  | .x17 => a17
  | .x18 => a18
  | .x19 => a19
  | .x20 => a20
  | .x21 => a21
  | .x22 => a22
  | .x23 => a23
  | .x24 => a24
  | .x25 => a25
  | .x26 => a26
  | .x27 => a27
  | .x28 => a28
  | .x29 => a29
  | .x30 => a30
  | .x31 => a31

theorem rf_eta (R : Reg → Word) :
    R = rf (R .x0) (R .x1) (R .x2) (R .x3) (R .x4) (R .x5) (R .x6) (R .x7) (R .x8) (R .x9) (R .x10) (R .x11) (R .x12) (R .x13) (R .x14) (R .x15) (R .x16) (R .x17) (R .x18) (R .x19) (R .x20) (R .x21) (R .x22) (R .x23) (R .x24) (R .x25) (R .x26) (R .x27) (R .x28) (R .x29) (R .x30) (R .x31) := by
  funext r; cases r <;> rfl

open Lean Elab Command in
run_cmd do
  let as : Array Ident := (Array.range 32).map fun i => mkIdent (Name.mkSimple s!"a{i}")
  for k in [0:32] do
    let r : Ident := mkIdent (Name.mkStr `RiscvZkvm.Rv64.Reg s!"x{k}")
    let w := mkIdent `w
    let as' := as.set! k w
    let get := mkIdent (Name.mkSimple s!"rf_get_x{k}")
    let set := mkIdent (Name.mkSimple s!"rf_set_x{k}")
    elabCommand (← `(theorem $get ($as* : Word) : rf $as* $r = $(as[k]!) := rfl))
    elabCommand (← `(theorem $set ($as* $w : Word) : updReg (rf $as*) $r $w = rf $as'* := by
      funext r; cases r <;> rfl))

end Rv64mc.Tactic
