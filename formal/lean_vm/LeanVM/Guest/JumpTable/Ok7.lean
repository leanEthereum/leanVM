/-
  LeanVM.Guest.JumpTable.Ok7

  The kernel's checks of subtrees 14 and 15 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_14_ll : allEntries entryOk (Data.jtTrie.right.right.right.left.left.left) 64 70 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_lr : allEntries entryOk (Data.jtTrie.right.right.right.left.left.right) 64 102 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_rl : allEntries entryOk (Data.jtTrie.right.right.right.left.right.left) 64 86 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_rr : allEntries entryOk (Data.jtTrie.right.right.right.left.right.right) 64 118 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14 : allEntries entryOk (Data.jtTrie.right.right.right.left) 16 22 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_14_ll jtOk_14_lr)
    (allEntries_split (by decide +kernel) jtOk_14_rl jtOk_14_rr)

set_option maxRecDepth 100000 in
theorem jtOk_15_ll : allEntries entryOk (Data.jtTrie.right.right.right.right.left.left) 64 78 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_lr : allEntries entryOk (Data.jtTrie.right.right.right.right.left.right) 64 110 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_rl : allEntries entryOk (Data.jtTrie.right.right.right.right.right.left) 64 94 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_rr : allEntries entryOk (Data.jtTrie.right.right.right.right.right.right) 64 126 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15 : allEntries entryOk (Data.jtTrie.right.right.right.right) 16 30 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_15_ll jtOk_15_lr)
    (allEntries_split (by decide +kernel) jtOk_15_rl jtOk_15_rr)

end
end LeanVM.Guest.JumpTable
