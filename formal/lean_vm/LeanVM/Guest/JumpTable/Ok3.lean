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
theorem jtOk_6_lll : allEntries entryOk (Data.jtTrie.left.right.right.left.left.left.left) 128 133 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_llr : allEntries entryOk (Data.jtTrie.left.right.right.left.left.left.right) 128 197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_lrl : allEntries entryOk (Data.jtTrie.left.right.right.left.left.right.left) 128 165 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_lrr : allEntries entryOk (Data.jtTrie.left.right.right.left.left.right.right) 128 229 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_rll : allEntries entryOk (Data.jtTrie.left.right.right.left.right.left.left) 128 149 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_rlr : allEntries entryOk (Data.jtTrie.left.right.right.left.right.left.right) 128 213 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_rrl : allEntries entryOk (Data.jtTrie.left.right.right.left.right.right.left) 128 181 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6_rrr : allEntries entryOk (Data.jtTrie.left.right.right.left.right.right.right) 128 245 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6 : allEntries entryOk (Data.jtTrie.left.right.right.left) 16 21 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_6_lll
        jtOk_6_llr)
      (allEntries_split (by decide +kernel)
        jtOk_6_lrl
        jtOk_6_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_6_rll
        jtOk_6_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_6_rrl
        jtOk_6_rrr))

set_option maxRecDepth 100000 in
theorem jtOk_7_lll : allEntries entryOk (Data.jtTrie.left.right.right.right.left.left.left) 128 141 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_llr : allEntries entryOk (Data.jtTrie.left.right.right.right.left.left.right) 128 205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_lrl : allEntries entryOk (Data.jtTrie.left.right.right.right.left.right.left) 128 173 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_lrr : allEntries entryOk (Data.jtTrie.left.right.right.right.left.right.right) 128 237 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_rll : allEntries entryOk (Data.jtTrie.left.right.right.right.right.left.left) 128 157 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_rlr : allEntries entryOk (Data.jtTrie.left.right.right.right.right.left.right) 128 221 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_rrl : allEntries entryOk (Data.jtTrie.left.right.right.right.right.right.left) 128 189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7_rrr : allEntries entryOk (Data.jtTrie.left.right.right.right.right.right.right) 128 253 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7 : allEntries entryOk (Data.jtTrie.left.right.right.right) 16 29 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_7_lll
        jtOk_7_llr)
      (allEntries_split (by decide +kernel)
        jtOk_7_lrl
        jtOk_7_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_7_rll
        jtOk_7_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_7_rrl
        jtOk_7_rrr))

end
end LeanVM.Guest.JumpTable
