module

public import NativeRustcVmX64.Whir.InducedWeight.Acc
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.InducedWeight.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmX64.Code.Vm.SubspaceTable.Names

/-!
# `induced_weight` on x86-64

The entry handles the unsupported dimension and empty query cases. The outer loop decreases
the number of remaining queries; each product and sum transition preserves its full frame.
-/

namespace NativeRustcVmX64.Whir.InducedWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InducedWeight

public section

variable [Host] {k : Nat}

/-- `induced_weight`'s contract, using its callees' contracts. -/
theorem inducedWeight_spec (hp : Placed code k)
    (htab : Spec (Labels.label NativeRustcVmX64.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    (hsat : Spec (Labels.label NativeRustcVmX64.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.InducedWeight.entryLabel) InducedWeightPre InducedWeightPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.InducedWeight.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b0Offset) from hp.label NativeRustcVmX64.Vm.InducedWeight.entry_at]
  refine entry_a hp htab hpre fun st1 hpc1 hA ↦ ?_
  refine entry_b hp hmemcpy hpre hpc1 hA fun st2 hpc2 hI ↦ ?_
  refine Sym.loop (fun n st ↦ ∃ j, n = cntOf m0 - j ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b7Offset) ∧
    OInv m0 j st.data) (fun n st ⟨j, hn, hpc, hI⟩ ↦ ?_) ⟨0, rfl, hpc2, hI⟩
  have hj := hI.hj
  refine (outer_step hp hsat hkmul hmul hpre hpc hI).bind fun st3 ⟨hpc3, hA⟩ ↦ ?_
  refine (accumulate hp hpre hpc3 hA).bind fun st4 h ↦ ?_
  rcases h with ⟨hpc4, hI4⟩ | ⟨hpc4, hD⟩
  · exact .done _ (.inr ⟨cntOf m0 - (j + 1), by omega, j + 1, rfl, hpc4, hI4⟩)
  · exact (finish hp hpre hpc4 hD).mono fun _ h ↦ .inl h

end

end NativeRustcVmX64.Whir.InducedWeight
