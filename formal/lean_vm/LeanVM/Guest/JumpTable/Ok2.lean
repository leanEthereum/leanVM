/-
  LeanVM.Guest.JumpTable.Ok2

  The kernel's checks of subtrees 4 and 5 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_4_ll : allEntries entryOk (Data.jtTrie.left.right.left.left.left.left) 64 65 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_lr : allEntries entryOk (Data.jtTrie.left.right.left.left.left.right) 64 97 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_rl : allEntries entryOk (Data.jtTrie.left.right.left.left.right.left) 64 81 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_rr : allEntries entryOk (Data.jtTrie.left.right.left.left.right.right) 64 113 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4 : allEntries entryOk (Data.jtTrie.left.right.left.left) 16 17 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_4_ll jtOk_4_lr)
    (allEntries_split (by decide +kernel) jtOk_4_rl jtOk_4_rr)

set_option maxRecDepth 100000 in
theorem jtOk_5_ll : allEntries entryOk (Data.jtTrie.left.right.left.right.left.left) 64 73 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_lr : allEntries entryOk (Data.jtTrie.left.right.left.right.left.right) 64 105 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_rl : allEntries entryOk (Data.jtTrie.left.right.left.right.right.left) 64 89 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_rr : allEntries entryOk (Data.jtTrie.left.right.left.right.right.right) 64 121 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5 : allEntries entryOk (Data.jtTrie.left.right.left.right) 16 25 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_5_ll jtOk_5_lr)
    (allEntries_split (by decide +kernel) jtOk_5_rl jtOk_5_rr)

end
end LeanVM.Guest.JumpTable
