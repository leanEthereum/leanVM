/-
  LeanVM.Guest.JumpTable.Ok4

  The kernel's checks of subtrees 8 and 9 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_8_ll : allEntries entryOk (Data.jtTrie.right.left.left.left.left.left) 64 64 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_lr : allEntries entryOk (Data.jtTrie.right.left.left.left.left.right) 64 96 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_rl : allEntries entryOk (Data.jtTrie.right.left.left.left.right.left) 64 80 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_rr : allEntries entryOk (Data.jtTrie.right.left.left.left.right.right) 64 112 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8 : allEntries entryOk (Data.jtTrie.right.left.left.left) 16 16 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_8_ll jtOk_8_lr)
    (allEntries_split (by decide +kernel) jtOk_8_rl jtOk_8_rr)

set_option maxRecDepth 100000 in
theorem jtOk_9_ll : allEntries entryOk (Data.jtTrie.right.left.left.right.left.left) 64 72 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_lr : allEntries entryOk (Data.jtTrie.right.left.left.right.left.right) 64 104 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_rl : allEntries entryOk (Data.jtTrie.right.left.left.right.right.left) 64 88 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_rr : allEntries entryOk (Data.jtTrie.right.left.left.right.right.right) 64 120 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9 : allEntries entryOk (Data.jtTrie.right.left.left.right) 16 24 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_9_ll jtOk_9_lr)
    (allEntries_split (by decide +kernel) jtOk_9_rl jtOk_9_rr)

end
end LeanVM.Guest.JumpTable
