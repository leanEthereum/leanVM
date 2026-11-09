/-
  LeanVM.Guest.B1.Sig.SpWotsData1

  `sp_wots` in the guest's core IR agrees with the template `spBody` on digit groups 11 to 21, the checks and the leaf (statements 72 on).
-/

module

public import LeanVM.Guest.Data.Core04
public import LeanVM.Guest.B1.Sig.SpWotsLayout
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.Value.Tower
import LeanVM.Guest.Value.FieldBits

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

open scoped Dec in
theorem spBody_slice_72 : (Data.core19.body.drop 72).take 5 = (spBody.drop 72).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_77 : (Data.core19.body.drop 77).take 5 = (spBody.drop 77).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_82 : (Data.core19.body.drop 82).take 5 = (spBody.drop 82).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_87 : (Data.core19.body.drop 87).take 5 = (spBody.drop 87).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_92 : (Data.core19.body.drop 92).take 5 = (spBody.drop 92).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_97 : (Data.core19.body.drop 97).take 5 = (spBody.drop 97).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_102 : (Data.core19.body.drop 102).take 5 = (spBody.drop 102).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_107 : (Data.core19.body.drop 107).take 5 = (spBody.drop 107).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_112 : (Data.core19.body.drop 112).take 5 = (spBody.drop 112).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_117 : (Data.core19.body.drop 117).take 5 = (spBody.drop 117).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_122 : (Data.core19.body.drop 122).take 5 = (spBody.drop 122).take 5 := by
  decide +kernel

/-! ## The tail

The leaf's message ends in a cell holding both padding bytes, `0x01` at byte 1072 and `0x80` at
byte 1087, which the template sums (`kXorByte`); the kernel does not evaluate a sum of words, so the
cell's constant is written out (`spPadCell`) and the rest checked. -/

/-- The leaf's message cells, the padding cell's constant `e`. -/
def spLeafCs (e : E) : List KC := spLeafCells.map KC.cell ++ [.const e]

/-- The leaf's `keccak_cells`, the padding cell's constant `e`. -/
def spLeafKOf (e : E) : List Stmt × Nat × Nat :=
  let bl := kBlocks spPad (spLeafCs e) 8 false none 1 8 0 none (spC + 3)
  ([] ++ [] ++ bl.1, bl.2.1, bl.2.2)

set_option maxRecDepth 40000 in
theorem spLeafK_of : spLeafK = spLeafKOf (byteWord 1072 1 + byteWord 1087 0x80) := by
  unfold spLeafK kMsg spLeafKOf
  rfl

theorem spPadCell : byteWord 1072 1 + byteWord 1087 0x80 = word 1 (2 ^ 63) 0 := by
  have e1 : byteWord 1072 1 = word 1 0 0 := rfl
  have e2 : byteWord 1087 0x80 = word 0 (2 ^ 63) 0 := rfl
  rw [e1, e2]
  simp only [word, Value.ofLimbs_add, Value.ofBits_zero, add_zero, zero_add]

theorem spHeadT_length : spHeadT.length = 127 := by decide +kernel

theorem spBody_drop_eq : spBody.drop 127 = Stmt.renameList spRen (spTailOf (spLeafKOf (word 1 (2 ^ 63) 0))) := by
  rw [spBody, spBodyT_split, renameList_append, List.drop_left' (by rw [renameList_length, spHeadT_length]),
    spLeafK_of, spPadCell]

open scoped Dec in
theorem spBody_tail : Data.core19.body.drop 127 =
    Stmt.renameList spRen (spTailOf (spLeafKOf (word 1 (2 ^ 63) 0))) := by
  decide +kernel

theorem spBody_drop_127 : Data.core19.body.drop 127 = spBody.drop 127 := by
  rw [spBody_tail, spBody_drop_eq]

end
end LeanVM.Guest.B1.Sig
