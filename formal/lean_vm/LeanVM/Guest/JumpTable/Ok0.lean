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
theorem jtOk_0_lll : allEntries entryOk (Data.jtTrie.left.left.left.left.left.left.left) 128 127 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_llr : allEntries entryOk (Data.jtTrie.left.left.left.left.left.left.right) 128 191 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_lrl : allEntries entryOk (Data.jtTrie.left.left.left.left.left.right.left) 128 159 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_lrr : allEntries entryOk (Data.jtTrie.left.left.left.left.left.right.right) 128 223 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_rll : allEntries entryOk (Data.jtTrie.left.left.left.left.right.left.left) 128 143 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_rlr : allEntries entryOk (Data.jtTrie.left.left.left.left.right.left.right) 128 207 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_rrl : allEntries entryOk (Data.jtTrie.left.left.left.left.right.right.left) 128 175 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0_rrr : allEntries entryOk (Data.jtTrie.left.left.left.left.right.right.right) 128 239 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_0 : allEntries entryOk (Data.jtTrie.left.left.left.left) 16 15 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_0_lll
        jtOk_0_llr)
      (allEntries_split (by decide +kernel)
        jtOk_0_lrl
        jtOk_0_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_0_rll
        jtOk_0_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_0_rrl
        jtOk_0_rrr))

set_option maxRecDepth 100000 in
theorem jtOk_1_lll : allEntries entryOk (Data.jtTrie.left.left.left.right.left.left.left) 128 135 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_llr : allEntries entryOk (Data.jtTrie.left.left.left.right.left.left.right) 128 199 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_lrl : allEntries entryOk (Data.jtTrie.left.left.left.right.left.right.left) 128 167 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_lrr : allEntries entryOk (Data.jtTrie.left.left.left.right.left.right.right) 128 231 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_rll : allEntries entryOk (Data.jtTrie.left.left.left.right.right.left.left) 128 151 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_rlr : allEntries entryOk (Data.jtTrie.left.left.left.right.right.left.right) 128 215 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_rrl : allEntries entryOk (Data.jtTrie.left.left.left.right.right.right.left) 128 183 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1_rrr : allEntries entryOk (Data.jtTrie.left.left.left.right.right.right.right) 128 247 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1 : allEntries entryOk (Data.jtTrie.left.left.left.right) 16 23 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_1_lll
        jtOk_1_llr)
      (allEntries_split (by decide +kernel)
        jtOk_1_lrl
        jtOk_1_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_1_rll
        jtOk_1_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_1_rrl
        jtOk_1_rrr))

end
end LeanVM.Guest.JumpTable
