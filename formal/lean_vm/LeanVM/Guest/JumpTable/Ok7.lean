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
theorem jtOk_14_lll : allEntries entryOk (Data.jtTrie.right.right.right.left.left.left.left) 128 134 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_llr : allEntries entryOk (Data.jtTrie.right.right.right.left.left.left.right) 128 198 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_lrl : allEntries entryOk (Data.jtTrie.right.right.right.left.left.right.left) 128 166 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_lrr : allEntries entryOk (Data.jtTrie.right.right.right.left.left.right.right) 128 230 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_rll : allEntries entryOk (Data.jtTrie.right.right.right.left.right.left.left) 128 150 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_rlr : allEntries entryOk (Data.jtTrie.right.right.right.left.right.left.right) 128 214 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_rrl : allEntries entryOk (Data.jtTrie.right.right.right.left.right.right.left) 128 182 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14_rrr : allEntries entryOk (Data.jtTrie.right.right.right.left.right.right.right) 128 246 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14 : allEntries entryOk (Data.jtTrie.right.right.right.left) 16 22 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_14_lll
        jtOk_14_llr)
      (allEntries_split (by decide +kernel)
        jtOk_14_lrl
        jtOk_14_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_14_rll
        jtOk_14_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_14_rrl
        jtOk_14_rrr))

set_option maxRecDepth 100000 in
theorem jtOk_15_lll : allEntries entryOk (Data.jtTrie.right.right.right.right.left.left.left) 128 142 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_llr : allEntries entryOk (Data.jtTrie.right.right.right.right.left.left.right) 128 206 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_lrl : allEntries entryOk (Data.jtTrie.right.right.right.right.left.right.left) 128 174 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_lrr : allEntries entryOk (Data.jtTrie.right.right.right.right.left.right.right) 128 238 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_rll : allEntries entryOk (Data.jtTrie.right.right.right.right.right.left.left) 128 158 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_rlr : allEntries entryOk (Data.jtTrie.right.right.right.right.right.left.right) 128 222 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_rrl : allEntries entryOk (Data.jtTrie.right.right.right.right.right.right.left) 128 190 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15_rrr : allEntries entryOk (Data.jtTrie.right.right.right.right.right.right.right) 128 254 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15 : allEntries entryOk (Data.jtTrie.right.right.right.right) 16 30 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_15_lll
        jtOk_15_llr)
      (allEntries_split (by decide +kernel)
        jtOk_15_lrl
        jtOk_15_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_15_rll
        jtOk_15_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_15_rrl
        jtOk_15_rrr))

end
end LeanVM.Guest.JumpTable
