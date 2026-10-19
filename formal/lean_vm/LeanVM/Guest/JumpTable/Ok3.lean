/-
  LeanVM.Guest.JumpTable.Ok3

  The kernel's checks of subtrees 6 and 7 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_6_ll : allEntries entryOk (Data.jtTrie.left.right.right.left.left.left) 64 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_lr : allEntries entryOk (Data.jtTrie.left.right.right.left.left.right) 64 101 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_rl : allEntries entryOk (Data.jtTrie.left.right.right.left.right.left) 64 85 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_rr : allEntries entryOk (Data.jtTrie.left.right.right.left.right.right) 64 117 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6 : allEntries entryOk (Data.jtTrie.left.right.right.left) 16 21 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_6_ll jtOk_6_lr)
    (allEntries_split (by decide +kernel) jtOk_6_rl jtOk_6_rr)

set_option maxRecDepth 100000 in
theorem jtOk_7_ll : allEntries entryOk (Data.jtTrie.left.right.right.right.left.left) 64 77 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_lr : allEntries entryOk (Data.jtTrie.left.right.right.right.left.right) 64 109 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_rl : allEntries entryOk (Data.jtTrie.left.right.right.right.right.left) 64 93 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_rr : allEntries entryOk (Data.jtTrie.left.right.right.right.right.right) 64 125 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7 : allEntries entryOk (Data.jtTrie.left.right.right.right) 16 29 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel) jtOk_7_ll jtOk_7_lr)
    (allEntries_split (by decide +kernel) jtOk_7_rl jtOk_7_rr)

end
end LeanVM.Guest.JumpTable
