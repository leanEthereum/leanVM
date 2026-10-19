/-
  LeanVM.Guest.JumpTable.Ok1

  The kernel's checks of subtrees 2 and 3 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_2_ll : allEntries entryOk (Data.jtTrie.left.left.right.left.left.left) 64 67 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_lr : allEntries entryOk (Data.jtTrie.left.left.right.left.left.right) 64 99 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_rl : allEntries entryOk (Data.jtTrie.left.left.right.left.right.left) 64 83 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_rr : allEntries entryOk (Data.jtTrie.left.left.right.left.right.right) 64 115 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2 : allEntries entryOk (Data.jtTrie.left.left.right.left) 16 19 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_2_ll jtOk_2_lr)
    (allEntries_split (by decide +kernel) jtOk_2_rl jtOk_2_rr)

set_option maxRecDepth 100000 in
theorem jtOk_3_ll : allEntries entryOk (Data.jtTrie.left.left.right.right.left.left) 64 75 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_lr : allEntries entryOk (Data.jtTrie.left.left.right.right.left.right) 64 107 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_rl : allEntries entryOk (Data.jtTrie.left.left.right.right.right.left) 64 91 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_rr : allEntries entryOk (Data.jtTrie.left.left.right.right.right.right) 64 123 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3 : allEntries entryOk (Data.jtTrie.left.left.right.right) 16 27 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_3_ll jtOk_3_lr)
    (allEntries_split (by decide +kernel) jtOk_3_rl jtOk_3_rr)

end
end LeanVM.Guest.JumpTable
