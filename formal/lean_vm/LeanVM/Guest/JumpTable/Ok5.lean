/-
  LeanVM.Guest.JumpTable.Ok5

  The kernel's checks of subtrees 10 and 11 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_10_ll : allEntries entryOk (Data.jtTrie.right.left.right.left.left.left) 64 68 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_lr : allEntries entryOk (Data.jtTrie.right.left.right.left.left.right) 64 100 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_rl : allEntries entryOk (Data.jtTrie.right.left.right.left.right.left) 64 84 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_rr : allEntries entryOk (Data.jtTrie.right.left.right.left.right.right) 64 116 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10 : allEntries entryOk (Data.jtTrie.right.left.right.left) 16 20 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_10_ll jtOk_10_lr)
    (allEntries_split (by decide +kernel) jtOk_10_rl jtOk_10_rr)

set_option maxRecDepth 100000 in
theorem jtOk_11_ll : allEntries entryOk (Data.jtTrie.right.left.right.right.left.left) 64 76 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_lr : allEntries entryOk (Data.jtTrie.right.left.right.right.left.right) 64 108 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_rl : allEntries entryOk (Data.jtTrie.right.left.right.right.right.left) 64 92 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_rr : allEntries entryOk (Data.jtTrie.right.left.right.right.right.right) 64 124 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11 : allEntries entryOk (Data.jtTrie.right.left.right.right) 16 28 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_11_ll jtOk_11_lr)
    (allEntries_split (by decide +kernel) jtOk_11_rl jtOk_11_rr)

end
end LeanVM.Guest.JumpTable
