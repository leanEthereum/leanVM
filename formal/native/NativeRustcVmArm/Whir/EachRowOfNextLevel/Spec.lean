module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmArm.Code.Vm.FoldRow.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.LanesOf.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Code.Vm.RowsRow.Names
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.IterA

/-!
# `each_row` with `next_level`'s closure meets its contract

`eachRowNext_spec`: placed anywhere in the program, given its callees' contracts
(`subspace_table`, `memcpy`, `Rows::row`, `lanes_of`, `fold_row`, `subspace_at_table`,
`novel_eval`, `kmul`, `EW::mul`), from its entry in a state satisfying `EachRowNextPre rows op` it
returns `1` with the batched value `batchedOf …` at `&mut batched`, memory changed in its stack and
the batched value only, the callee-saved registers and SP restored (`EachRowNextPost rows`). The
run: the table and its copy (`entry_a`), into the loop (`start_step`), the loop by induction on the
rows left (`iter_step`), the exit (`exit_step`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeVm.Model NativeRustcVmArm.Vm.EachRowOfNextLevel

public section

variable [Host] {k : Nat}

/-- **`each_row` with `next_level`'s closure meets its contract.** -/
theorem eachRowNext_spec (hp : Placed code k)
    (htab : Spec (label NativeRustcVmArm.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hlanes : Spec (label NativeRustcVmArm.Vm.LanesOf.entryLabel) LanesOfPre LanesOfPost)
    (hfold : Spec (label NativeRustcVmArm.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost)
    (hsat : Spec (label NativeRustcVmArm.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hnov : Spec (label NativeRustcVmArm.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (rows : Array (Array UInt64)) (op : BitVec 64)
    (hrow : Spec (label NativeRustcVmArm.Vm.RowsRow.entryLabel) (RowsRowPre op rows) (RowsRowPost op rows)) :
    Spec (label NativeRustcVmArm.Vm.EachRowOfNextLevel.entryLabel) (EachRowNextPre rows op) (EachRowNextPost rows) := by
  intro m0 hpre
  rw [show label NativeRustcVmArm.Vm.EachRowOfNextLevel.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b0Offset) from hp.label NativeRustcVmArm.Vm.EachRowOfNextLevel.entry_at]
  have loop : ∀ n j m, rows.size - j = n → Inv rows m0 j m →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b8Offset)⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j m hn h
      exact iter_step hp hrow hlanes hfold hsat hnov hkmul hmul hpre h fun m' h' ↦
        ih (rows.size - (j + 1)) (by have := h.hj; omega) (j + 1) m' rfl h'
  exact entry_a hp htab hmemcpy hpre fun m h3 ↦
    start_step hp hpre h3 fun m' h0 ↦ loop _ 0 m' rfl h0

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
