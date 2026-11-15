/-
  LeanVM.Guest.Res.CpChk

  The kernel's checks behind `certify_placement`'s residuals: each of the shapes its proof takes,
  its index, and the cells of the values they name inside its frame.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Pack.«P51».ModeCert

/-!
# `certify_placement`'s residuals: the checks

Each residual of its certificate (`cp_res`) is one the proof takes (`cpAcc`), wherever the walk
puts it: a divisor, the cell of a rank `r ≥ 1`'s key (value `.n (137 + 18·r)`), or the run
`group_base[0 .. 9)` (value `.n 137`) inside the cells `group_base · group_order[j]` its ranks
wrote (`cpSub`, the hinted order value `.n 136`), at the cells the function's certificate gives
them (`cellJ`), each inside the frame (`cp_cells`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The run of `group_base` (cell `b`) inside the cells its ranks wrote at the hinted order's words
(cell `q`). -/
def cpSub (q b : ℕ) : Mode.Res :=
  .sub ⟨⟨0, 0, [(.fr b, 1)]⟩, .num 0, .num 9, 1, 0⟩
    ((List.range 9).map fun j ↦ ⟨⟨0, 0, [(.fr b, 1), (.hp q j, 1)]⟩, .num 0, .num 1, 1, 0⟩)

/-- The values the residuals name: the ranks' keys, the hinted order, `group_base`. -/
def cpVals : List V := ((List.range 8).map fun r ↦ V.n (137 + 18 * (r + 1))) ++ [.n 136, .n 137]

/-- **A residual `certify_placement`'s proof takes**, at its function's index `j`. -/
noncomputable def cpAcc (j : ℕ) (x : Mode.Res) : Bool :=
  (List.range 8).any (fun r ↦ x == .nz (B2C.cellJ j (.n (137 + 18 * (r + 1))))) ||
    x == cpSub (B2C.cellJ j (.n 136)) (B2C.cellJ j (.n 137))

end

public section

theorem cp_res : ∀ i < Fn.«certify_placement».modeCert.code.length,
    ∀ x ∈ (Fn.«certify_placement».modeCert.F.res.get i).getD [], cpAcc fn_idx% «certify_placement» x = true := by
  decide +kernel

theorem cp_idx : B2C.idxOf "certify_placement" = some fn_idx% «certify_placement» ∧
    (fnOf fn_idx% «certify_placement»).entryPc = Fn.«certify_placement».modeCert.F.entry := by
  decide +kernel

theorem cp_cells : ∀ v ∈ cpVals, 2 ≤ B2C.cellJ fn_idx% «certify_placement» v ∧
    B2C.cellJ fn_idx% «certify_placement» v < B2C.fsN fn_idx% «certify_placement» := by
  decide +kernel

end

end LeanVM.Guest.Res
