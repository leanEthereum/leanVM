module

public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmArm.Code.Vm.FoldRow.Names
public import NativeRustcVmArm.Code.Vm.LanesOf.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Code.Vm.RowsRow.Names
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Iter

/-!
# `each_row` with `final_level`'s closure meets its contract

`eachRowFinal_spec`: placed anywhere in the program, given its callees' contracts
(`subspace_table`, `memcpy`, `Rows::row`, `lanes_of`, `fold_row`, `subspace_at_table`,
`novel_eval`), from its entry in a state satisfying `EachRowFinalPre rows op` it returns with X0 =
`okWord (finalOk …)`, memory changed in its stack only, the callee-saved registers and SP restored
(`EachRowFinalPost rows`). The run: the table and its copy (`entry_a`), into the loop
(`start_step`), the loop by induction on the rows left (`iter_step`), the exits (`exit_step`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfFinalLevel

open NativeRustcArm NativeVm.Model NativeRustcVmArm.Vm.EachRowOfFinalLevel

public section

variable [Host] {k : Nat}

/-- **`each_row` with `final_level`'s closure meets its contract.** -/
theorem eachRowFinal_spec (hp : Placed code k)
    (htab : Spec (label NativeRustcVmArm.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hlanes : Spec (label NativeRustcVmArm.Vm.LanesOf.entryLabel) LanesOfPre LanesOfPost)
    (hfold : Spec (label NativeRustcVmArm.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost)
    (hsat : Spec (label NativeRustcVmArm.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hnov : Spec (label NativeRustcVmArm.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (rows : Array (Array UInt64)) (op : BitVec 64)
    (hrow : Spec (label NativeRustcVmArm.Vm.RowsRow.entryLabel) (RowsRowPre op rows) (RowsRowPost op rows)) :
    Spec (label NativeRustcVmArm.Vm.EachRowOfFinalLevel.entryLabel) (EachRowFinalPre rows op) (EachRowFinalPost rows) := by
  intro m0 hpre
  rw [show label NativeRustcVmArm.Vm.EachRowOfFinalLevel.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b0Offset) from hp.label NativeRustcVmArm.Vm.EachRowOfFinalLevel.entry_at]
  have loop : ∀ n j m, rows.size - j = n → Inv rows m0 j m →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b5Offset)⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j m hn h
      exact iter_step hp hrow hlanes hfold hsat hnov hpre h fun m' h' ↦
        ih (rows.size - (j + 1)) (by have := h.hj; omega) (j + 1) m' rfl h'
  exact entry_a hp htab hmemcpy hpre fun m h3 ↦
    start_step hp hpre h3 fun m' h0 ↦ loop _ 0 m' rfl h0

end

end NativeRustcVmArm.Whir.EachRowOfFinalLevel
