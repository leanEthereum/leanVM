module

public import NativeRustcVmX64.Rodata.Items.Basic

/-!
# The bytes of the program's data items: Bus

Each item's bytes in `Vm.rodata` are `Item.bytes`, the model's values laid out as rustc lays them.
-/

namespace NativeRustcVmX64.Rodata

open NativeRustcVm.Data
open NativeRustcX64 (dataAt)

set_option Elab.async false

public theorem data_tuples :
    dataAt (itemLabel .tuples) Vm.rodata = some (Item.bytes .tuples) := by
  decide +kernel

public theorem data_tables :
    dataAt (itemLabel .tables) Vm.rodata = some (Item.bytes .tables) := by
  decide +kernel

public theorem data_padding :
    dataAt (itemLabel .padding) Vm.rodata = some (Item.bytes .padding) := by
  decide +kernel

public theorem data_pushBlocks :
    dataAt (itemLabel .pushBlocks) Vm.rodata = some (Item.bytes .pushBlocks) := by
  decide +kernel

public theorem data_pullBlocks :
    dataAt (itemLabel .pullBlocks) Vm.rodata = some (Item.bytes .pullBlocks) := by
  decide +kernel

public theorem data_countBlocks :
    dataAt (itemLabel .countBlocks) Vm.rodata = some (Item.bytes .countBlocks) := by
  decide +kernel

end NativeRustcVmX64.Rodata
