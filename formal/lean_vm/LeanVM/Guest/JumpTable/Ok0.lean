/-
  LeanVM.Guest.JumpTable.Ok0

  The kernel's checks of subtrees 0 and 1 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_0_ll : allEntries entryOk (Data.jtTrie.left.left.left.left.left.left) 64 63 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_lr : allEntries entryOk (Data.jtTrie.left.left.left.left.left.right) 64 95 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_rl : allEntries entryOk (Data.jtTrie.left.left.left.left.right.left) 64 79 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_rr : allEntries entryOk (Data.jtTrie.left.left.left.left.right.right) 64 111 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0 : allEntries entryOk (Data.jtTrie.left.left.left.left) 16 15 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_0_ll jtOk_0_lr)
    (allEntries_split (by decide +kernel) jtOk_0_rl jtOk_0_rr)

set_option maxRecDepth 100000 in
theorem jtOk_1_ll : allEntries entryOk (Data.jtTrie.left.left.left.right.left.left) 64 71 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_lr : allEntries entryOk (Data.jtTrie.left.left.left.right.left.right) 64 103 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_rl : allEntries entryOk (Data.jtTrie.left.left.left.right.right.left) 64 87 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_rr : allEntries entryOk (Data.jtTrie.left.left.left.right.right.right) 64 119 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1 : allEntries entryOk (Data.jtTrie.left.left.left.right) 16 23 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_1_ll jtOk_1_lr)
    (allEntries_split (by decide +kernel) jtOk_1_rl jtOk_1_rr)

end
end LeanVM.Guest.JumpTable
