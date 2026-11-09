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
theorem jtOk_2_lll : allEntries entryOk (Data.jtTrie.left.left.right.left.left.left.left) 128 131 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_llr : allEntries entryOk (Data.jtTrie.left.left.right.left.left.left.right) 128 195 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_lrl : allEntries entryOk (Data.jtTrie.left.left.right.left.left.right.left) 128 163 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_lrr : allEntries entryOk (Data.jtTrie.left.left.right.left.left.right.right) 128 227 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_rll : allEntries entryOk (Data.jtTrie.left.left.right.left.right.left.left) 128 147 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_rlr : allEntries entryOk (Data.jtTrie.left.left.right.left.right.left.right) 128 211 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_rrl : allEntries entryOk (Data.jtTrie.left.left.right.left.right.right.left) 128 179 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2_rrr : allEntries entryOk (Data.jtTrie.left.left.right.left.right.right.right) 128 243 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2 : allEntries entryOk (Data.jtTrie.left.left.right.left) 16 19 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_2_lll
        jtOk_2_llr)
      (allEntries_split (by decide +kernel)
        jtOk_2_lrl
        jtOk_2_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_2_rll
        jtOk_2_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_2_rrl
        jtOk_2_rrr))

set_option maxRecDepth 100000 in
theorem jtOk_3_lll : allEntries entryOk (Data.jtTrie.left.left.right.right.left.left.left) 128 139 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_llr : allEntries entryOk (Data.jtTrie.left.left.right.right.left.left.right) 128 203 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_lrl : allEntries entryOk (Data.jtTrie.left.left.right.right.left.right.left) 128 171 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_lrr : allEntries entryOk (Data.jtTrie.left.left.right.right.left.right.right) 128 235 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_rll : allEntries entryOk (Data.jtTrie.left.left.right.right.right.left.left) 128 155 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_rlr : allEntries entryOk (Data.jtTrie.left.left.right.right.right.left.right) 128 219 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_rrl : allEntries entryOk (Data.jtTrie.left.left.right.right.right.right.left) 128 187 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3_rrr : allEntries entryOk (Data.jtTrie.left.left.right.right.right.right.right) 128 251 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3 : allEntries entryOk (Data.jtTrie.left.left.right.right) 16 27 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_3_lll
        jtOk_3_llr)
      (allEntries_split (by decide +kernel)
        jtOk_3_lrl
        jtOk_3_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_3_rll
        jtOk_3_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_3_rrl
        jtOk_3_rrr))

end
end LeanVM.Guest.JumpTable
