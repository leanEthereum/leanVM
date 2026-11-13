import LeanVM.Guest.CoreData
import LeanVMTests.Guest.CoreDataCheck

/-!
# The core IR's data, accessed

`coreProgram` by index, by name and against the compiled functions; `CoreDataCheck.lean` checks
the data against the expansion (`lake exe test-runs`).
-/

namespace LeanVMTests.Guest.CoreData

open Lean LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

/-! ## Access

By index, by name and against the compiled functions, at the first, a middle and the last
function, at the two largest (`__loop2`, the raw leanXMSS loop with `verify_lean_xmss` inlined, and
`sp_wots`) and at `verify_sig_lean_sphincs`, the first function past `sp_wots` (core 20, compiled
function 21). -/

set_option maxRecDepth 100000

example : coreProgram.length = core_count% := coreProgram_length

example : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

example : coreProgram.find? "__loop2" = some Data.core36 :=
  Program.find?_of_indexOf? (j := 36) (by decide +kernel) rfl

example : coreProgram.find? "sp_wots" = some Data.core19 :=
  Program.find?_of_indexOf? (j := 19) (by decide +kernel) rfl

example : coreProgram.find? "verify_sig_lean_sphincs" = some Data.core20 :=
  Program.find?_of_indexOf? (j := 20) (by decide +kernel) rfl

example : coreProgram.find? "squeeze_point_from__L18" = some Data.core635 :=
  Program.find?_of_indexOf? (j := 635) (by decide +kernel) rfl

example : coreProgram.find? "walk_path__L18_L4" = some Data.core1512 :=
  Program.find?_of_indexOf? (j := 1512) (by decide +kernel) rfl

example : Data.core19.name = Data.f20.name := name_eq_compiled (j := 19) rfl rfl

example : Data.core20.name = Data.f21.name := name_eq_compiled (j := 20) rfl rfl

example : Data.core36.name = Data.f37.name := name_eq_compiled (j := 36) rfl rfl

example : coreProgram.find? "walk_path__L12_L8" = some Data.core1563 :=
  Program.find?_of_indexOf? (j := 1563) (by decide +kernel) rfl

example : Data.core1512.name = Data.f1513.name := name_eq_compiled (j := 1512) rfl rfl

example : Data.core1563.name = Data.f1564.name := name_eq_compiled (j := 1563) rfl rfl

end LeanVMTests.Guest.CoreData
