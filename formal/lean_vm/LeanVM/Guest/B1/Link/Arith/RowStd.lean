/-
  LeanVM.Guest.B1.Link.Arith.RowStd

  The Statement's row side at the standard variables, and `JUMP`'s constraints, generic.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Std
public import LeanVM.Guest.B1.Link.Arith.TablesL

/-!
# The row side at the standard variables

`jumpConstraintsG`: `jumpConstraints`, generic; `consX` the tables' constraints over `Ex` (only
`JUMP` has any). `stdRow`: `rowSideG` at the standard variables, the lists in the forms a layout of
`tables()` gives them (`gammaMem`'s third entry `γ_word·Y`), over `tablesL` (`tables()`, its
coefficients words).
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Protocol.Verifier

@[expose] public section

/-- `jump_constraints(columns)` (`jumpConstraints`), generic. -/
def jumpConstraintsG {α : Type} [LOps α] (columns : List α) : List α :=
  let v := fun name ↦ columns.getD (colIndex jumpColumns name) 0
  let flag := v "b"
  let untaken := flag + 1
  [flag + v "v_cond" * v "w",
    v "v_cond" * untaken,
    v "pc_next" + flag * v "v_pc" + untaken * LOps.ofE (gpow 1) * v "pc",
    v "fp_next" + flag * v "v_fp" + untaken * v "fp"]

/-- The tables' constraints over `Ex`. -/
def consX (table : Table) (columns : List Ex) : List Ex :=
  if table.opcode = opJump then jumpConstraintsG columns else []

/-- The Statement's row side at the standard variables, over `tablesL`. -/
def stdRow : RowAcc Ex :=
  rowSideG tablesL stdIn.omega stdIn.act stdIn.eqTau stdIn.corner [stdIn.gs0, stdIn.gs1]
    [stdIn.gm0, stdIn.gm1, stdIn.gm1 * LOps.ofE eY, stdIn.gm3] ((List.range 16).map stdIn.slot)
    ((List.range 4).map stdIn.jump) ((List.range 33).map stdIn.eps) ((List.range 64).map stdIn.eqQ)
    ((List.range 80).map stdIn.sent) (muOf stdIn.chal) stdIn.etaMem stdIn.etaBc stdIn.eqzr stdIn.shz
    stdIn.xBc stdIn.pFp stdIn.yMem stdIn.m1 stdIn.eq0R consX

end

end LeanVM.Guest.B1.Link.Arith
