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
with its callees `c₀, …` by index, `allocOk`, the last over the code's jumps listed once,
`Bridge.allocRest_of_fast`), each `… = true` by the kernel. `align_chk% «k»` is its
plumbing cells' freshness (`alignCellsOk`; its alignment follows from its pairing, `CoreMode.alignOk_of_pairOk`). Unhygienic: names resolve where the macro is
written (in `namespace LeanVM.Guest`). `align_chk%`, `allocShapeOk` and `curBodyOk` are each a
plain `decide +kernel` of the check; `frOk` and `allocOk` decide fast forms (`Bridge.frChkS`, and the
check over the jump list) and conclude through `Bridge.frChk_of_fast` and `Bridge.allocRest_of_fast`.
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
    theorem $(fnDot k `frOk) : Bridge.frChk alignCtx fs [$idx,*] core.params core.body $adv = true :=
      Bridge.frChk_of_fast (by decide +kernel)
    theorem $(fnDot k `allocOk) :
        Bridge.allocRest alignCtx fs core.loop plumb core.body code.code $adv = true :=
      Bridge.allocRest_of_fast (by decide +kernel))

set_option hygiene false in
/-- `align_chk% «k»`: `k`'s plumbing cells are fresh. -/
macro "align_chk% " k:ident : command =>
  `(theorem $(fnDot k `alignCellsOk) : Bridge.cellsFresh cert.locs (Bridge.plumbCells plumb) [] = true := by
      decide +kernel)

end LeanVM.Guest.ChkLit

end
