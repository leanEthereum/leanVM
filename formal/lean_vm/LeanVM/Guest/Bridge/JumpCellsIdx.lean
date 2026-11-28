/-
  LeanVM.Guest.Bridge.JumpCellsIdx

  The jump cells' data check of a compiled function, by index.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsDefs
public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.Defs

/-!
# The jump cells' check by index

`jcData j`: `jcDataD` on compiled function `j`'s plumbing, frame size, certificate, hint-only cells (`extraOf`), core IR, code and whether it is `main`; `Bridge/JumpCells/All.lean` proves it of every function from the checks of each function's own data, by `jcData_of` and the link modules'
equations.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.B2C

@[expose] public section

/-- The jump cells' facts of function `j`'s data. -/
noncomputable def jcData (j : ℕ) : Bool :=
  jcDataD (plumbOf j) (fsN j) (certOf j) (extraOf j) (coreOf j) (fnOf j).code (j == 1)

end

public section

/-- **A function's jump cells' check from its pack's**, by its code, core IR, certificate, plumbing, tables and
frame size. -/
theorem jcData_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert} {P : Plumb} {n : ℕ}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : plumbOf j = P)
    (hn : fsN j = n) (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d))
    (h : jcDataD P n (C.withPows Data.powTree) ex cf f.code (j == 1) = true) : jcData j = true := by
  have hx : extraOf j = ex := congrArg Prod.fst ht
  rw [jcData, hf, hcf, hC, hP, hn, hx]
  exact h

end

end LeanVM.Guest.Bridge
