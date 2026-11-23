module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.IterD
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmX64.Code.Vm.FoldRow.Names
public import NativeRustcVmX64.Code.Vm.LanesOf.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.NovelEval.Names
public import NativeRustcVmX64.Code.Vm.RowsRow.Names
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmX64.Code.Vm.SubspaceTable.Names

/-!
# `each_row` with `final_level`'s closure meets its contract (x86-64)

`eachRowFinal_spec`: placed anywhere in the program, given its callees' contracts
(`subspace_table`, `memcpy`, `Rows::row`, `lanes_of`, `fold_row`, `subspace_at_table`,
`novel_eval`), from its entry in a state satisfying `EachRowFinalPre rows op` it returns with AL
the outcome `finalOk …`, memory changed in its stack only, the callee-saved registers and RSP
restored (`EachRowFinalPost rows`). The run: the table and its copy (`entry_a`), into the loop
(`start_step`), the loop by induction on the rows left (`iter_a` to `iter_d`), the exits.
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeVm.Model NativeRustcVmX64.Vm.EachRowOfFinalLevel

public section

variable [Host] {k : Nat}

/-- **`each_row` with `final_level`'s closure meets its contract.** -/
theorem eachRowFinal_spec (hp : Placed code k)
    (htab : Spec (label NativeRustcVmX64.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hlanes : Spec (label NativeRustcVmX64.Vm.LanesOf.entryLabel) LanesOfPre LanesOfPost)
    (hfold : Spec (label NativeRustcVmX64.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost)
    (hsat : Spec (label NativeRustcVmX64.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hnov : Spec (label NativeRustcVmX64.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (rows : Array (Array UInt64)) (op : BitVec 64)
    (hrow : Spec (label NativeRustcVmX64.Vm.RowsRow.entryLabel) (RowsRowPre op rows) (RowsRowPost op rows)) :
    Spec (label NativeRustcVmX64.Vm.EachRowOfFinalLevel.entryLabel) (EachRowFinalPre rows op) (EachRowFinalPost rows) := by
  intro m0 hpre
  rw [show label NativeRustcVmX64.Vm.EachRowOfFinalLevel.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b0Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.entry_at]
  have loop : ∀ n j m, rows.size - j = n → Inv rows m0 j m →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b5Offset)⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j m hn h
      exact iter_a hp hpre h fun m1 h1 ↦ iter_b hp hrow hlanes hpre h1 fun m2 h2 ↦
        iter_c hp hfold hsat hpre h2 fun m3 h3 ↦ iter_d hp hnov hpre h3 fun m4 h4 ↦
          ih (rows.size - (j + 1)) (by have := h.hj; omega) (j + 1) m4 rfl h4
  exact entry_a hp htab hmemcpy hpre fun m h3 ↦
    start_step hp hpre h3 fun m' h0 ↦ loop _ 0 m' rfl h0

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
