/-
  LeanVM.Guest.JumpTable.Keys

  The kernel's check of the jump table's keys: each is the slot of an instruction of
  `__jump_tables`.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Guest

public section

set_option maxRecDepth 100000 in
theorem jtKeys : allEntries keysOk Data.jtTrie 1 0 = true := by decide +kernel

end
end LeanVM.Guest.JumpTable
