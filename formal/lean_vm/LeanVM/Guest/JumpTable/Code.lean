/-
  LeanVM.Guest.JumpTable.Code

  The kernel's check of `__jump_tables`' code: each instruction sets its slot to the jump table's
  target there.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Guest LeanVM.Guest.Memory

public section

set_option maxRecDepth 100000 in
theorem jtCode : walkOk codeOk 0 Data.f0.code = true := by decide +kernel

end
end LeanVM.Guest.JumpTable
