module

public import NativeRustcVmX64.Bus.BusLayout.Finish
public import NativeRustcVmX64.Code.Vm.BusLayout.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names

/-!
# `bus_layout` (x86-64)

The sizes (`sizes_run`: the framework's, then each block's owner's log-height), the offsets
(`offsets_run`: `stack_offsets`), the placements (`place_run`), the layout copied out
(`finish`): `busLayout_spec`.
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmX64.Vm.BusLayout

public section

variable [Host] {k : Nat}

/-- **`bus_layout` meets its contract.** -/
theorem busLayout_spec (hp : Placed code k)
    (hms : Spec (Labels.label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hso : Spec (Labels.label NativeRustcVmX64.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost)
    {L : LayoutW} {bl : List NativeRustcVm.Data.Block} :
    Spec (Labels.label NativeRustcVmX64.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.BusLayout.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b0Offset) from hp.label NativeRustcVmX64.Vm.BusLayout.entry_at]
  exact Eventually.bind (sizes_run hp hms hpre) fun st hD ↦
    Eventually.bind (offsets_run hp hms hso hpre hD.1 hD.2) fun st2 ⟨hpc2, hI⟩ ↦
      Eventually.bind (place_run hp hpre hpc2 hI) fun st3 ⟨hpc3, hE⟩ ↦
        finish hp hmc hpre hpc3 hE

end

end NativeRustcVmX64.Bus.BusLayout
