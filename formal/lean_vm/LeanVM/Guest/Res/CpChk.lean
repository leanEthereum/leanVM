/-
  LeanVM.Guest.Res.CpChk

  The kernel's checks behind `certify_placement`'s residuals: where they sit, its index and the
  cells of the values they name.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Pack.«P51».ModeCert

/-!
# `certify_placement`'s residuals: the checks

Its certificate has two residuals (`cp_res`): the divisor `[141] ≠ 0` at offset `152`, rank `1`'s
key (value `.n 155`), and at offset `275` the run `group_base[0 .. 9)` (cell `124`, value
`.n 137`) inside the cells `group_base · group_order[j]` its ranks wrote (`cpSub`, the hinted
order at cell `123`, value `.n 136`) (`cp_cells`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `certify_placement`'s run of `group_base` inside the cells its hinted order wrote. -/
def cpSub : Mode.Res :=
  .sub ⟨⟨0, 0, [(.fr 124, 1)]⟩, .num 0, .num 9, 1, 0⟩
    ((List.range 9).map fun j ↦ ⟨⟨0, 0, [(.fr 124, 1), (.hp 123 j, 1)]⟩, .num 0, .num 1, 1, 0⟩)

end

public section

theorem cp_res : ∀ i < Fn.«certify_placement».modeCert.code.length,
    ∀ x ∈ (Fn.«certify_placement».modeCert.F.res.get i).getD [],
      (i = 152 ∧ x = .nz 141) ∨ (i = 275 ∧ x = cpSub) := by
  decide +kernel

theorem cp_idx : B2C.idxOf "certify_placement" = some fn_idx% «certify_placement» ∧
    (fnOf fn_idx% «certify_placement»).entryPc = Fn.«certify_placement».modeCert.F.entry := by
  decide +kernel

theorem cp_cells : B2C.cellJ fn_idx% «certify_placement» (.n 155) = 141 ∧
    B2C.cellJ fn_idx% «certify_placement» (.n 136) = 123 ∧
    B2C.cellJ fn_idx% «certify_placement» (.n 137) = 124 ∧ 141 < B2C.fsN fn_idx% «certify_placement» := by
  decide +kernel

end

end LeanVM.Guest.Res
