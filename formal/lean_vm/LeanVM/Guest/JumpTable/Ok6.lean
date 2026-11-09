/-
  LeanVM.Guest.JumpTable.Ok6

  The kernel's checks of subtrees 12 and 13 of the jump table.
-/

module

public import LeanVM.Guest.JumpTable.Entries

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk_12_lll : allEntries entryOk (Data.jtTrie.right.right.left.left.left.left.left) 128 130 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_llr : allEntries entryOk (Data.jtTrie.right.right.left.left.left.left.right) 128 194 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_lrl : allEntries entryOk (Data.jtTrie.right.right.left.left.left.right.left) 128 162 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_lrr : allEntries entryOk (Data.jtTrie.right.right.left.left.left.right.right) 128 226 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_rll : allEntries entryOk (Data.jtTrie.right.right.left.left.right.left.left) 128 146 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_rlr : allEntries entryOk (Data.jtTrie.right.right.left.left.right.left.right) 128 210 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_rrl : allEntries entryOk (Data.jtTrie.right.right.left.left.right.right.left) 128 178 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12_rrr : allEntries entryOk (Data.jtTrie.right.right.left.left.right.right.right) 128 242 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12 : allEntries entryOk (Data.jtTrie.right.right.left.left) 16 18 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_12_lll
        jtOk_12_llr)
      (allEntries_split (by decide +kernel)
        jtOk_12_lrl
        jtOk_12_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_12_rll
        jtOk_12_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_12_rrl
        jtOk_12_rrr))

set_option maxRecDepth 100000 in
theorem jtOk_13_lll : allEntries entryOk (Data.jtTrie.right.right.left.right.left.left.left) 128 138 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_llr : allEntries entryOk (Data.jtTrie.right.right.left.right.left.left.right) 128 202 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_lrl : allEntries entryOk (Data.jtTrie.right.right.left.right.left.right.left) 128 170 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_lrr : allEntries entryOk (Data.jtTrie.right.right.left.right.left.right.right) 128 234 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_rll : allEntries entryOk (Data.jtTrie.right.right.left.right.right.left.left) 128 154 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_rlr : allEntries entryOk (Data.jtTrie.right.right.left.right.right.left.right) 128 218 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_rrl : allEntries entryOk (Data.jtTrie.right.right.left.right.right.right.left) 128 186 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13_rrr : allEntries entryOk (Data.jtTrie.right.right.left.right.right.right.right) 128 250 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13 : allEntries entryOk (Data.jtTrie.right.right.left.right) 16 26 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_13_lll
        jtOk_13_llr)
      (allEntries_split (by decide +kernel)
        jtOk_13_lrl
        jtOk_13_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_13_rll
        jtOk_13_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_13_rrl
        jtOk_13_rrr))

end
end LeanVM.Guest.JumpTable
