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
`sp_wots`) and at `verify_sig_lean_sphincs`, the first function past `sp_wots`; each named by its stable
name (`idx%`, `fn_idx%`), so another function's change moves none. -/

set_option maxRecDepth 100000

example : coreProgram.length = core_count% := coreProgram_length

example : coreProgram.find? "main" = some fn% «main» :=
  Program.find?_of_indexOf? (j := idx% «main») (by decide +kernel) rfl

example : coreProgram.find? "__loop2_main" = some fn% «main_loop2» :=
  Program.find?_of_indexOf? (j := idx% «main_loop2») (by decide +kernel) rfl

example : coreProgram.find? "sp_wots" = some fn% «sp_wots» :=
  Program.find?_of_indexOf? (j := idx% «sp_wots») (by decide +kernel) rfl

example : coreProgram.find? "verify_sig_lean_sphincs" = some fn% «verify_sig_lean_sphincs» :=
  Program.find?_of_indexOf? (j := idx% «verify_sig_lean_sphincs») (by decide +kernel) rfl

example : coreProgram.find? "squeeze_point_from__L18" = some fn% «squeeze_point_from__L18» :=
  Program.find?_of_indexOf? (j := idx% «squeeze_point_from__L18») (by decide +kernel) rfl

example : coreProgram.find? "level_residual_sum__L18_L8_L4_L78" = some fn% «level_residual_sum__L18_L8_L4_L78» :=
  Program.find?_of_indexOf? (j := idx% «level_residual_sum__L18_L8_L4_L78») (by decide +kernel) rfl

example : (fn% «sp_wots»).name = (Data.functions[fn_idx% «sp_wots»]'(by decide +kernel)).name :=
  name_eq_compiled (j := idx% «sp_wots») rfl (List.getElem?_eq_getElem _)

example : (fn% «verify_sig_lean_sphincs»).name =
    (Data.functions[fn_idx% «verify_sig_lean_sphincs»]'(by decide +kernel)).name :=
  name_eq_compiled (j := idx% «verify_sig_lean_sphincs») rfl (List.getElem?_eq_getElem _)

example : (fn% «main_loop2»).name = (Data.functions[fn_idx% «main_loop2»]'(by decide +kernel)).name :=
  name_eq_compiled (j := idx% «main_loop2») rfl (List.getElem?_eq_getElem _)

example : coreProgram.find? "residual_query_slow__L20_L4_L300" = some fn% «residual_query_slow__L20_L4_L300» :=
  Program.find?_of_indexOf? (j := idx% «residual_query_slow__L20_L4_L300») (by decide +kernel) rfl

example : (fn% «level_residual_sum__L18_L8_L4_L78»).name = (Data.functions[fn_idx% «level_residual_sum__L18_L8_L4_L78»]'(by decide +kernel)).name :=
  name_eq_compiled (j := idx% «level_residual_sum__L18_L8_L4_L78») rfl (List.getElem?_eq_getElem _)

example : (fn% «residual_query_slow__L20_L4_L300»).name = (Data.functions[fn_idx% «residual_query_slow__L20_L4_L300»]'(by decide +kernel)).name :=
  name_eq_compiled (j := idx% «residual_query_slow__L20_L4_L300») rfl (List.getElem?_eq_getElem _)

end LeanVMTests.Guest.CoreData
