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
theorem jtOk_8_lll : allEntries entryOk (Data.jtTrie.right.left.left.left.left.left.left) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_llr : allEntries entryOk (Data.jtTrie.right.left.left.left.left.left.right) 128 192 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_lrl : allEntries entryOk (Data.jtTrie.right.left.left.left.left.right.left) 128 160 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_lrr : allEntries entryOk (Data.jtTrie.right.left.left.left.left.right.right) 128 224 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_rll : allEntries entryOk (Data.jtTrie.right.left.left.left.right.left.left) 128 144 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_rlr : allEntries entryOk (Data.jtTrie.right.left.left.left.right.left.right) 128 208 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_rrl : allEntries entryOk (Data.jtTrie.right.left.left.left.right.right.left) 128 176 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8_rrr : allEntries entryOk (Data.jtTrie.right.left.left.left.right.right.right) 128 240 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8 : allEntries entryOk (Data.jtTrie.right.left.left.left) 16 16 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_8_lll
        jtOk_8_llr)
      (allEntries_split (by decide +kernel)
        jtOk_8_lrl
        jtOk_8_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_8_rll
        jtOk_8_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_8_rrl
        jtOk_8_rrr))

set_option maxRecDepth 100000 in
theorem jtOk_9_lll : allEntries entryOk (Data.jtTrie.right.left.left.right.left.left.left) 128 136 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_llr : allEntries entryOk (Data.jtTrie.right.left.left.right.left.left.right) 128 200 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_lrl : allEntries entryOk (Data.jtTrie.right.left.left.right.left.right.left) 128 168 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_lrr : allEntries entryOk (Data.jtTrie.right.left.left.right.left.right.right) 128 232 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_rll : allEntries entryOk (Data.jtTrie.right.left.left.right.right.left.left) 128 152 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_rlr : allEntries entryOk (Data.jtTrie.right.left.left.right.right.left.right) 128 216 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_rrl : allEntries entryOk (Data.jtTrie.right.left.left.right.right.right.left) 128 184 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9_rrr : allEntries entryOk (Data.jtTrie.right.left.left.right.right.right.right) 128 248 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9 : allEntries entryOk (Data.jtTrie.right.left.left.right) 16 24 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_9_lll
        jtOk_9_llr)
      (allEntries_split (by decide +kernel)
        jtOk_9_lrl
        jtOk_9_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_9_rll
        jtOk_9_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_9_rrl
        jtOk_9_rrr))

end
end LeanVM.Guest.JumpTable
