/-
  LeanVM.Guest.B1.VerifySub.C.Flat

  `verify_sub`'s body for its completeness: kernel facts of its statements and its evaluation list.
-/

module

public import LeanVM.Guest.B1.VerifySub.Body
public import LeanVM.Guest.B1.Tables.FlatLift

/-!
# `verify_sub`, flat

`vsCPre`: `verify_sub`'s statements before its final `ret []` (`vsT_splitPre`). They are flat
(`vs_cflat`: atoms, calls, `callIf`s and one fused `match` of calls, no `ite`), place no address
by a frame cell (`vs_caddrs`), and `verify_sub` is no loop. `vsEvL`: the evaluation list (each
`assertNe` read as the product it checks); the checker accepts it from the `6` parameters
(`vs_chk`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables

@[expose] public section

/-- `verify_sub`'s statements before its `ret`. -/
def vsCPre : List Stmt := vsT.dropLast

theorem vsT_splitPre : vsT = vsCPre ++ [.ret []] := stmtsEqb_sound (by decide +kernel)

theorem vs_cflat : vsCPre.all Stmt.flat = true := by decide +kernel

theorem vs_caddrs : vsCPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem vs_not_loop : coreProgram.loop "verify_sub" = false := by decide +kernel

/-- **`verify_sub`'s evaluation list.** -/
def vsEvL : List Stmt := (flatIte vsCPre).map fixNe

end
end LeanVM.Guest.B1.VerifySub
