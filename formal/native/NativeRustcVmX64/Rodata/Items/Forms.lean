module

public import NativeRustcVmX64.Rodata.Items.Basic

/-!
# The bytes of the program's data items: Forms

Each item's bytes in `Vm.rodata` are `Item.bytes`, the model's values laid out as rustc lays them.
-/

namespace NativeRustcVmX64.Rodata

open NativeRustcVm.Data
open NativeRustcX64 (dataAt)

set_option Elab.async false

public theorem data_forms :
    dataAt (itemLabel .forms) Vm.rodata = some (Item.bytes .forms) := by
  decide +kernel

public theorem data_terms :
    dataAt (itemLabel .terms) Vm.rodata = some (Item.bytes .terms) := by
  decide +kernel

end NativeRustcVmX64.Rodata
