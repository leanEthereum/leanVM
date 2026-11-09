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
theorem jtOk_4_lll : allEntries entryOk (Data.jtTrie.left.right.left.left.left.left.left) 128 129 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_llr : allEntries entryOk (Data.jtTrie.left.right.left.left.left.left.right) 128 193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_lrl : allEntries entryOk (Data.jtTrie.left.right.left.left.left.right.left) 128 161 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_lrr : allEntries entryOk (Data.jtTrie.left.right.left.left.left.right.right) 128 225 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_rll : allEntries entryOk (Data.jtTrie.left.right.left.left.right.left.left) 128 145 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_rlr : allEntries entryOk (Data.jtTrie.left.right.left.left.right.left.right) 128 209 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_rrl : allEntries entryOk (Data.jtTrie.left.right.left.left.right.right.left) 128 177 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4_rrr : allEntries entryOk (Data.jtTrie.left.right.left.left.right.right.right) 128 241 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4 : allEntries entryOk (Data.jtTrie.left.right.left.left) 16 17 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_4_lll
        jtOk_4_llr)
      (allEntries_split (by decide +kernel)
        jtOk_4_lrl
        jtOk_4_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_4_rll
        jtOk_4_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_4_rrl
        jtOk_4_rrr))

set_option maxRecDepth 100000 in
theorem jtOk_5_lll : allEntries entryOk (Data.jtTrie.left.right.left.right.left.left.left) 128 137 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_llr : allEntries entryOk (Data.jtTrie.left.right.left.right.left.left.right) 128 201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_lrl : allEntries entryOk (Data.jtTrie.left.right.left.right.left.right.left) 128 169 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_lrr : allEntries entryOk (Data.jtTrie.left.right.left.right.left.right.right) 128 233 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_rll : allEntries entryOk (Data.jtTrie.left.right.left.right.right.left.left) 128 153 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_rlr : allEntries entryOk (Data.jtTrie.left.right.left.right.right.left.right) 128 217 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_rrl : allEntries entryOk (Data.jtTrie.left.right.left.right.right.right.left) 128 185 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5_rrr : allEntries entryOk (Data.jtTrie.left.right.left.right.right.right.right) 128 249 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5 : allEntries entryOk (Data.jtTrie.left.right.left.right) 16 25 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_5_lll
        jtOk_5_llr)
      (allEntries_split (by decide +kernel)
        jtOk_5_lrl
        jtOk_5_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_5_rll
        jtOk_5_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_5_rrl
        jtOk_5_rrr))

end
end LeanVM.Guest.JumpTable
