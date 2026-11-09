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
theorem jtOk_10_lll : allEntries entryOk (Data.jtTrie.right.left.right.left.left.left.left) 128 132 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_llr : allEntries entryOk (Data.jtTrie.right.left.right.left.left.left.right) 128 196 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_lrl : allEntries entryOk (Data.jtTrie.right.left.right.left.left.right.left) 128 164 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_lrr : allEntries entryOk (Data.jtTrie.right.left.right.left.left.right.right) 128 228 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_rll : allEntries entryOk (Data.jtTrie.right.left.right.left.right.left.left) 128 148 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_rlr : allEntries entryOk (Data.jtTrie.right.left.right.left.right.left.right) 128 212 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_rrl : allEntries entryOk (Data.jtTrie.right.left.right.left.right.right.left) 128 180 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10_rrr : allEntries entryOk (Data.jtTrie.right.left.right.left.right.right.right) 128 244 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10 : allEntries entryOk (Data.jtTrie.right.left.right.left) 16 20 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_10_lll
        jtOk_10_llr)
      (allEntries_split (by decide +kernel)
        jtOk_10_lrl
        jtOk_10_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_10_rll
        jtOk_10_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_10_rrl
        jtOk_10_rrr))

set_option maxRecDepth 100000 in
theorem jtOk_11_lll : allEntries entryOk (Data.jtTrie.right.left.right.right.left.left.left) 128 140 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_llr : allEntries entryOk (Data.jtTrie.right.left.right.right.left.left.right) 128 204 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_lrl : allEntries entryOk (Data.jtTrie.right.left.right.right.left.right.left) 128 172 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_lrr : allEntries entryOk (Data.jtTrie.right.left.right.right.left.right.right) 128 236 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_rll : allEntries entryOk (Data.jtTrie.right.left.right.right.right.left.left) 128 156 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_rlr : allEntries entryOk (Data.jtTrie.right.left.right.right.right.left.right) 128 220 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_rrl : allEntries entryOk (Data.jtTrie.right.left.right.right.right.right.left) 128 188 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11_rrr : allEntries entryOk (Data.jtTrie.right.left.right.right.right.right.right) 128 252 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11 : allEntries entryOk (Data.jtTrie.right.left.right.right) 16 28 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_11_lll
        jtOk_11_llr)
      (allEntries_split (by decide +kernel)
        jtOk_11_lrl
        jtOk_11_lrr))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        jtOk_11_rll
        jtOk_11_rlr)
      (allEntries_split (by decide +kernel)
        jtOk_11_rrl
        jtOk_11_rrr))

end
end LeanVM.Guest.JumpTable
