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
function, at the two largest (`__loop2_main`, the raw leanXMSS loop with `verify_lean_xmss` inlined, and
`sp_wots`) and at `verify_sig_lean_sphincs`, the first function past `sp_wots` (core 21, compiled
function 22). -/

set_option maxRecDepth 100000

example : coreProgram.length = core_count% := coreProgram_length

example : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

example : coreProgram.find? "__loop2_main" = some Data.core40 :=
  Program.find?_of_indexOf? (j := 40) (by decide +kernel) rfl

example : coreProgram.find? "sp_wots" = some Data.core20 :=
  Program.find?_of_indexOf? (j := 20) (by decide +kernel) rfl

example : coreProgram.find? "verify_sig_lean_sphincs" = some Data.core21 :=
  Program.find?_of_indexOf? (j := 21) (by decide +kernel) rfl

example : coreProgram.find? "squeeze_point_from__L18" = some Data.core671 :=
  Program.find?_of_indexOf? (j := 671) (by decide +kernel) rfl

example : coreProgram.find? "walk_path__L18_L4" = some Data.core1553 :=
  Program.find?_of_indexOf? (j := 1553) (by decide +kernel) rfl

example : Data.core20.name = Data.f21.name := name_eq_compiled (j := 20) rfl rfl

example : Data.core21.name = Data.f22.name := name_eq_compiled (j := 21) rfl rfl

example : Data.core40.name = Data.f41.name := name_eq_compiled (j := 40) rfl rfl

example : coreProgram.find? "walk_path__L12_L8" = some Data.core1604 :=
  Program.find?_of_indexOf? (j := 1604) (by decide +kernel) rfl

example : Data.core1553.name = Data.f1554.name := name_eq_compiled (j := 1553) rfl rfl

example : Data.core1604.name = Data.f1605.name := name_eq_compiled (j := 1604) rfl rfl

end LeanVMTests.Guest.CoreData
