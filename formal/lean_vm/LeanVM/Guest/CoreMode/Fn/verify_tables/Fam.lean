/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.Fam

  `verify_tables`'s own residual families (`CoreMode/FnReg.lean`): its reads past its table sumcheck, its buffers through its hinted order, its exponent family.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.Gen.Own.«verify_tables»
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`verify_tables`' reads past its table sumcheck's last record's cursor** (`verify_tables.py`'s `vt_st_sub`):
the cell `c` words past the cursor, the value `cursor@5`, `c < 153`, one of its stream's, parameter `stream`'s
`[0, 8192)` (`EndExec.vtStC_inst`). -/
def vtStC (fn : Fn) : CRes → Bool
  | .sub c q => fn.name == name% «verify_tables» && decide (c.bases = [(val% «verify_tables» "cursor@5", 1)]) && decide (c.off < 153) &&
      decide (q = ⟨⟨[(val% «verify_tables» "stream", 1)], 0⟩, 1, .num 0, .num 8192⟩)
  | _ => false

/-- `verify_tables`' rank `r`'s group value from the side's first `v0`, by its sort's template (`B1.Tables.vtRv`). -/
def vtRvC (v0 r : ℕ) : ℕ := if r = 0 then v0 else v0 + 13 + 20 * (r - 1)

/-- **`verify_tables`' sides**: each side's ranks' group values (from `gi@1`, `gi@10`) and the side's groups
`[lo, hi)`. -/
def vtSides : List (List ℕ × ℕ × ℕ) :=
  [((List.range 9).map (vtRvC (val% «verify_tables» "gi@1")), 0, 9),
    ((List.range 6).map (vtRvC (val% «verify_tables» "gi@10")), 18, 24)]

/-- **`verify_tables`' buffers indexed by group, through its hinted order** (`vtPerm`):
a cell `[B]·[v]` at a rank's group value `v` is one of `[B]·g^e` over the side's groups (each rank's group
is one of the side's), and a cell `[B]·g^e` at a group of the side is one of `[B]·[v]` over its ranks' values (the
ranks name every group of the side) (`EndExec.vtPerm_inst`). -/
def vtPerm (fn : Fn) : CRes → Bool
  | .subP c cs => fn.name == name% «verify_tables» && vtSides.any fun p ↦ match c.bases with
      | [(B, 1), (v, 1)] => Nat.beq c.off 0 && p.1.contains v &&
          (List.range' p.2.1 (p.2.2 - p.2.1)).all fun e ↦ cs.contains ⟨[(B, 1)], e⟩
      | [(B, 1)] => Nat.ble p.2.1 c.off && Nat.blt c.off p.2.2 && p.1.all fun v ↦ cs.contains ⟨[(B, 1), (v, 1)], 0⟩
      | _ => false
  | _ => false

/-! ## `verify_tables`' exponent family -/

/-- `verify_tables`' own parameter words as ghost slots: `dims_g[j]`, `j < 7` (`HSig.gw`). -/
def vtGw : List (CCell × ℕ) := (List.range 7).map fun j ↦ (⟨[(val% «verify_tables» "dims_g", 1)], j⟩, j)

/-- **`verify_tables`' exponent family**, its ghost slots its `dims_g` words, at its words' forms (`vtForms`). -/
def vtExp (fn : Fn) (gw : List (CCell × ℕ)) (r : CRes) : Bool :=
  fn.name == name% «verify_tables» && decide (gw = vtGw) && vtExpR (vtFormAt vtForms) [] r

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.verify_tables

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its families**: its reads past its table sumcheck (`vtStC`), its buffers through its hinted order (`vtPerm`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «verify_tables», vtStC), (name% «verify_tables», vtPerm)]

/-- **Its exponent family**, its ghost slots its own `dims_g` words (`vtExp`). -/
noncomputable def gwFams : List (String × (Fn → List (CCell × ℕ) → CRes → Bool)) := [(name% «verify_tables», vtExp)]

end

end LeanVM.Guest.CoreMode.Own.verify_tables
