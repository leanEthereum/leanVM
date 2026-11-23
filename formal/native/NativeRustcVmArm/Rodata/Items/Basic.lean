module

public import NativeRustcVmArm.Rodata
public import NativeRustcVmArm.Placed.Basic
public import NativeRustcVmArm.Code.Vm
public import NativeRustcArm.Data

/-!
# The data labels of the program

The read-only data `Vm.rodata` holds exactly the items' labels (`labels_rodata`); their bytes are
read by `NativeRustcArm.dataAt`.
-/

namespace NativeRustcVmArm.Rodata

open NativeRustcVm.Data

set_option Elab.async false

/-- The read-only data's labels are the items', in order. -/
public theorem labels_rodata : Placement.labels Vm.rodata = Item.all.map itemLabel := by
  decide +kernel

end NativeRustcVmArm.Rodata
