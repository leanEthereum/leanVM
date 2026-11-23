module

public import NativeRustcVmX64.Rodata.Items.Small
public import NativeRustcVmX64.Rodata.Items.Columns
public import NativeRustcVmX64.Rodata.Items.Bus
public import NativeRustcVmX64.Rodata.Items.Forms

/-!
# The program's read-only data is the items' bytes

`Vm.rodata` defines exactly the items' labels, in order (`labels_rodata`), and the bytes after each
are the item's (`data_eq`): what `RodataAt` asks memory to hold is what the program's data holds.
-/

namespace NativeRustcVmX64.Rodata

open NativeRustcVm.Data
open NativeRustcX64 (dataAt)

/-- **Each item's bytes in the program's data.** -/
public theorem data_eq : ∀ t : Item, dataAt (itemLabel t) Vm.rodata = some t.bytes
  | .rmfeProject => data_rmfeProject
  | .keccakRC => data_keccakRC
  | .keccakRho => data_keccakRho
  | .tuples => data_tuples
  | .tables => data_tables
  | .padding => data_padding
  | .pushBlocks => data_pushBlocks
  | .pullBlocks => data_pullBlocks
  | .countBlocks => data_countBlocks
  | .one => data_one
  | .perChallenge => data_perChallenge
  | .queryTable => data_queryTable
  | .queryLevels => data_queryLevels
  | .forms => data_forms
  | .terms => data_terms
  | .keccakSlot => data_keccakSlot
  | .keccakOutput => data_keccakOutput

end NativeRustcVmX64.Rodata
