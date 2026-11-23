module

public import NativeRustcVmX64.Rodata
public import NativeRustcVmX64.Placed.Basic
public import NativeRustcVmX64.Code.Vm
public import NativeRustcX64.Data

/-!
# The data labels of the program

The read-only data `Vm.rodata` holds exactly the items' labels (`labels_rodata`); their bytes are
read by `NativeRustcX64.dataAt`.
-/

namespace NativeRustcVmX64.Rodata

open NativeRustcVm.Data

set_option Elab.async false

/-- The read-only data's labels are the items', in order. -/
public theorem labels_rodata : Placement.labels Vm.rodata = Item.all.map itemLabel := by
  decide +kernel

end NativeRustcVmX64.Rodata
