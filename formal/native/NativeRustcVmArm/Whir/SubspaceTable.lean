module

public import NativeRustcVmArm.Code.Vm.Kinv.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.SubspaceTable.Entry
public import NativeRustcVmArm.Whir.SubspaceTable.Start
public import NativeRustcVmArm.Whir.SubspaceTable.Finish

/-!
# `subspace_table`

`Entry.entry` initializes the layer (`2^(i+1)` for `i < μ`) or leaves for `μ > 31`
(`finish_big`); `Start.start` pushes `(1, kinv 1)`; the turns (`Outer.outer_step`, by
`Sym.loop`) square and shift the layer by the last root and push the next root with its inverse,
until the table is done (`finish_done`: tag `1`, the table copied out) or would get a 32nd root
(`finish_full`, `μ = 31`: tag `0`). The table is `subspaceTable μ`
(`NativeRustcVm.Whir.subspaceTable_toList`).
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm

public section

variable [Host] {k : Nat}

/-- **The turns**, from `OInv 0`. -/
theorem turns (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hkinv : Spec (label NativeRustcVmArm.Vm.Kinv.entryLabel) KinvPre KinvPost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) {st : MachineData} (hO : OInv m0 0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ SubspaceTablePost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset)⟩ := by
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ (Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b21Offset)) ∨
      (Full m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b23Offset)))
    (fun n s ↦ ∃ t, n = muOf m0 - t ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset) ∧ OInv m0 t s.data)
    (fun n s ⟨t, hn, hpc, hO⟩ ↦ by
      obtain ⟨d, pc⟩ := s
      simp only at hpc
      subst hpc
      refine (outer_step hp hkmul hkinv hpre.1 hO).mono fun s' h ↦ ?_
      rcases h with ⟨hO', hpc', hlt⟩ | h
      · exact .inr ⟨muOf m0 - (t + 1), by omega, t + 1, rfl, hpc', hO'⟩
      · exact .inl h)
    (n := muOf m0 - 0) (s := ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset)⟩) ⟨0, rfl, rfl, hO⟩
  refine hloop.bind fun s h ↦ ?_
  obtain ⟨d, pc⟩ := s
  rcases h with ⟨hD, hpc⟩ | ⟨hF, hpc⟩
  · simp only at hpc
    subst hpc
    exact finish_done hp hmemcpy hpre hD
  · simp only at hpc
    subst hpc
    exact finish_full hp hpre hF

/-- **`subspace_table`'s contract.** -/
theorem subspaceTable_spec (hp : Placed code k)
    (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hkinv : Spec (label NativeRustcVmArm.Vm.Kinv.entryLabel) KinvPre KinvPost)
    (hmemset : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (label NativeRustcVmArm.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.SubspaceTable.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b0Offset) from hp.label NativeRustcVmArm.Vm.SubspaceTable.entry_at]
  refine (entry hp hmemset hpre).bind fun s h ↦ ?_
  obtain ⟨d, pc⟩ := s
  rcases h with ⟨hI, hpc⟩ | ⟨hfr, hx19, hbig, hpc⟩
  · simp only at hpc
    subst hpc
    refine (start hp hkinv hpre.1 hI).bind fun s h ↦ ?_
    obtain ⟨d', pc'⟩ := s
    rcases h with ⟨hO, hpc'⟩ | ⟨hD, hpc'⟩
    · simp only at hpc'
      subst hpc'
      exact turns hp hkmul hkinv hmemcpy hpre hO
    · simp only at hpc'
      subst hpc'
      exact finish_done hp hmemcpy hpre hD
  · simp only at hpc
    subst hpc
    exact finish_big hp hpre hfr hx19 hbig

end

end NativeRustcVmArm.Whir.SubspaceTable

