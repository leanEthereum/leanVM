/-
  LeanVM.Guest.Res.CldChk

  The kernel's checks behind `claim_list_digest`'s residual: where it sits, the dispatch its
  alignment reaches there, `list_split`'s call site and the cell of its last return.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Pack.«P29».ModeCert

/-!
# `claim_list_digest`'s residual: the checks

Its certificate's only residual is `[[23]·g^5] < 17` at offset `99` (`cld_res`), where its alignment
reaches the dispatch on `rest` past atoms (`cld_al`, `headDispatch`). Cell `23` holds the callee
frame pointer of its call of `list_split` (`cld_site`), whose last return `.n 30` (`ls_ret`,
`retLast`) is at cell `5` (`ls_cell`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A dispatch past atoms. -/
def headDispatch : List Stmt → Bool
  | .atom _ :: ss => headDispatch ss
  | .dispatch .. :: _ => true
  | _ => false

/-- The returns of a body of atoms then a `ret`. -/
def retLast : List Stmt → Option (List V)
  | [.ret vs] => some vs
  | .atom _ :: ss => retLast ss
  | _ => none

/-- `claim_list_digest`'s residual. -/
abbrev cldRes : Mode.Res := .lt (.ex (.hp 23 5) 0) (.num 17)

/-- `claim_list_digest`'s call of `list_split`. -/
abbrev cldSplit : Call := ⟨"list_split", [.n 1], [.n 12, .n 13, .n 14], true⟩

end

public section

theorem cld_res : ∀ i < Fn.«claim_list_digest».modeCert.code.length,
    ∀ x ∈ (Fn.«claim_list_digest».modeCert.F.res.get i).getD [], i = 99 ∧ x = cldRes := by
  decide +kernel

theorem cld_idx : B2C.idxOf "claim_list_digest" = some fn_idx% «claim_list_digest» ∧
    (fnOf fn_idx% «claim_list_digest»).entryPc = Fn.«claim_list_digest».modeCert.F.entry ∧
    Bridge.entOf Bridge.alignA "claim_list_digest" = Fn.«claim_list_digest».modeCert.F.entry := by
  decide +kernel

theorem cld_al : (Bridge.alOf Bridge.alignA "claim_list_digest" 99).map headDispatch = some true := by
  decide +kernel

theorem cld_site : (B2C.siteOf fn_idx% «claim_list_digest» cldSplit).map (·.q) = some 23 ∧
    23 < B2C.fsN fn_idx% «claim_list_digest» := by
  decide +kernel

theorem ls_cell : B2C.idxOf "list_split" = some fn_idx% «list_split» ∧
    B2C.cellJ fn_idx% «list_split» (.n 30) = 5 ∧ 5 < B2C.fsN fn_idx% «list_split» := by
  decide +kernel

theorem ls_ret : retLast (coreOf fn_idx% «list_split»).body = some [.n 28, .n 29, .n 30] := by
  decide +kernel

end

end LeanVM.Guest.Res
