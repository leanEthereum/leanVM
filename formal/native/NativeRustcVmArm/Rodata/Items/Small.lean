module

public import NativeRustcVmArm.Rodata.Items.Basic

/-!
# The bytes of the program's data items: Small

Each item's bytes in `Vm.rodata` are `Item.bytes`, the model's values laid out as rustc lays them.
-/

namespace NativeRustcVmArm.Rodata

open NativeRustcVm.Data
open NativeRustcArm (dataAt)

set_option Elab.async false

public theorem data_rmfeProject :
    dataAt (itemLabel .rmfeProject) Vm.rodata = some (Item.bytes .rmfeProject) := by
  decide +kernel

public theorem data_keccakRC :
    dataAt (itemLabel .keccakRC) Vm.rodata = some (Item.bytes .keccakRC) := by
  decide +kernel

public theorem data_keccakRho :
    dataAt (itemLabel .keccakRho) Vm.rodata = some (Item.bytes .keccakRho) := by
  decide +kernel

public theorem data_one :
    dataAt (itemLabel .one) Vm.rodata = some (Item.bytes .one) := by
  decide +kernel

public theorem data_perChallenge :
    dataAt (itemLabel .perChallenge) Vm.rodata = some (Item.bytes .perChallenge) := by
  decide +kernel

public theorem data_queryTable :
    dataAt (itemLabel .queryTable) Vm.rodata = some (Item.bytes .queryTable) := by
  decide +kernel

public theorem data_queryLevels :
    dataAt (itemLabel .queryLevels) Vm.rodata = some (Item.bytes .queryLevels) := by
  decide +kernel

end NativeRustcVmArm.Rodata
