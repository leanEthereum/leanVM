/-
  LeanVM.Guest.Bridge.ChkLit

  `alloc_chk%` and `align_chk%`: the kernel's checks `scripts/bridge-cert/alloc.py` and `align.py`
  write for each function, written once here so that the generated modules state them in one line.
-/

module

public meta import Lean.Elab.Command

/-!
# A function's bridge checks in one line

`alloc_chk% «k» [«c₀», …]` is `k`'s four allocation checks (`allocShapeOk`, `curBodyOk`, `frOk`
with its callees `c₀, …` by index, `allocOk`), each `… = true` by the kernel. `align_chk% «k»` is its
alignment checks (`alignCellsOk`, `alignOk`). Unhygienic: each expands to the text the generators
wrote before, its names resolved where it is written (in `namespace LeanVM.Guest`), so its
elaboration is the same.
-/

public section

namespace LeanVM.Guest.ChkLit

open Lean

/-- `Fn.«k».s`. -/
meta def fnDot (k : TSyntax `ident) (s : Name) : TSyntax `ident := mkIdent (`Fn ++ k.getId ++ s)

set_option hygiene false in
/-- `alloc_chk% «k» [«c₀», …]`: `k`'s allocation hints pass the check. -/
macro "alloc_chk% " k:ident "[" cs:ident,* "]" : command => do
  let idx := cs.getElems.map (fnDot · `idx)
  let adv := fnDot k `advice
  `(theorem $(fnDot k `allocShapeOk) : Bridge.allocShape core.body = true := by decide +kernel
    theorem $(fnDot k `curBodyOk) : Bridge.curBody alignCtx plumb core.body code.code $adv = true := by decide +kernel
    theorem $(fnDot k `frOk) : Bridge.frChk alignCtx fs [$idx,*] core.params core.body $adv = true := by decide +kernel
    theorem $(fnDot k `allocOk) :
        Bridge.allocRest alignCtx fs core.loop plumb core.body code.code $adv = true := by decide +kernel)

set_option hygiene false in
/-- `align_chk% «k»`: `k`'s plumbing cells are fresh and its code aligns with its body. -/
macro "align_chk% " k:ident : command =>
  `(theorem $(fnDot k `alignCellsOk) : Bridge.cellsFresh cert.locs (Bridge.plumbCells plumb) [] = true := by
      decide +kernel
    theorem $(fnDot k `alignOk) : Bridge.alignOk alignCtx core.body code.code $(fnDot k `advice) = true := by
      decide +kernel)

end LeanVM.Guest.ChkLit

end
