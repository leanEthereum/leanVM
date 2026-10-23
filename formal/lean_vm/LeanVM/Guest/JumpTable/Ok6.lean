/-
  LeanVM.Guest.JumpTable.Ok6

  The kernel's checks of subtrees 12 and 13 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_12_ll : allEntries entryOk (Data.jtTrie.right.right.left.left.left.left) 64 66 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_lr : allEntries entryOk (Data.jtTrie.right.right.left.left.left.right) 64 98 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_rl : allEntries entryOk (Data.jtTrie.right.right.left.left.right.left) 64 82 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_rr : allEntries entryOk (Data.jtTrie.right.right.left.left.right.right) 64 114 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12 : allEntries entryOk (Data.jtTrie.right.right.left.left) 16 18 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_12_ll jtOk_12_lr)
    (allEntries_split (by decide +kernel) jtOk_12_rl jtOk_12_rr)

set_option maxRecDepth 100000 in
theorem jtOk_13_ll : allEntries entryOk (Data.jtTrie.right.right.left.right.left.left) 64 74 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_lr : allEntries entryOk (Data.jtTrie.right.right.left.right.left.right) 64 106 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_rl : allEntries entryOk (Data.jtTrie.right.right.left.right.right.left) 64 90 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_rr : allEntries entryOk (Data.jtTrie.right.right.left.right.right.right) 64 122 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13 : allEntries entryOk (Data.jtTrie.right.right.left.right) 16 26 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_13_ll jtOk_13_lr)
    (allEntries_split (by decide +kernel) jtOk_13_rl jtOk_13_rr)

end
end LeanVM.Guest.JumpTable
