module

public import NativeRustcVmArm.Rodata.Items.Basic

/-!
# The bytes of the program's data items: Columns

Each item's bytes in `Vm.rodata` are `Item.bytes`, the model's values laid out as rustc lays them.
-/

namespace NativeRustcVmArm.Rodata

open NativeRustcVm.Data
open NativeRustcArm (dataAt)

set_option Elab.async false

public theorem data_keccakSlot :
    dataAt (itemLabel .keccakSlot) Vm.rodata = some (Item.bytes .keccakSlot) := by
  decide +kernel

public theorem data_keccakOutput :
    dataAt (itemLabel .keccakOutput) Vm.rodata = some (Item.bytes .keccakOutput) := by
  decide +kernel

end NativeRustcVmArm.Rodata
