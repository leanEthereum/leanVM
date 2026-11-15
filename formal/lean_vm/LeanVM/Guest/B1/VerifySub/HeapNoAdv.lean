/-
  LeanVM.Guest.B1.VerifySub.HeapNoAdv

  No advised buffer below `verify_tables`' callees, nor below `verify_sub`'s but `verify_tables`, which
  `verify_sub` calls at most once, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree
public import LeanVM.Guest.Memory.CallCount
public import LeanVM.Guest.CoreRef

/-!
# `verify_sub`'s callees without advised buffers

`vt_noAdvBut`: every callee of `verify_tables` passes `NoAdvG`; `vs_advFreeBut`: every callee of `verify_sub` but
`verify_tables` is in `AdvFree`; `vs_vtBound`: a path of `verify_sub` calls `verify_tables` at most once.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

theorem vt_name : (coreProgram[idx% «verify_tables»]?).map Fn.name = some "verify_tables" := by decide +kernel
theorem vs_name : (coreProgram[idx% «verify_sub»]?).map Fn.name = some "verify_sub" := by decide +kernel

theorem vt_noAdvBut : noAdvBut 16 idx% «verify_tables» [] = true := by decide +kernel
theorem vs_advFreeBut : advFreeBut idx% «verify_sub» ["verify_tables"] = true := by decide +kernel

theorem vs_vtBound : Stmt.blockBound "verify_tables" (fn% «verify_sub»).body = 1 := by decide +kernel

end

end LeanVM.Guest.B1.VerifySub
