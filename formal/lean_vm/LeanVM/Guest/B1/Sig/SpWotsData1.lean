/-
  LeanVM.Guest.B1.Sig.SpWotsData1

  `sp_wots` in the guest's core IR agrees with the template `spBody` on digit groups 11 to 21, the checks and the leaf (statements 72 on).
-/

module

public import LeanVM.Guest.Pack.sp_wots.Core
public import LeanVM.Guest.B1.Sig.SpWotsLayout
import LeanVM.Guest.B1.Sig.Decide
public import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.Value.Tower
import LeanVM.Guest.Value.FieldBits

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! Digit groups 11 to 21, the checks and the leaf's head (statements 72 to 126),
compared by `stmtsEqb` in runs, each its own kernel evaluation to bound its memory. -/

set_option maxRecDepth 100000 in
theorem spBody_run_72 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 72).take 8) ((spBody.drop 72).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_80 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 80).take 8) ((spBody.drop 80).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_88 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 88).take 8) ((spBody.drop 88).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_96 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 96).take 8) ((spBody.drop 96).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_104 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 104).take 8) ((spBody.drop 104).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_112 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 112).take 8) ((spBody.drop 112).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_120 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 120).take 7) ((spBody.drop 120).take 7) = true := by
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

theorem spPadCell : byteWord 1072 1 + byteWord 1087 0x80 = word 1 (2 ^ 63) := by
  have e1 : byteWord 1072 1 = word 1 0 := rfl
  have e2 : byteWord 1087 0x80 = word 0 (2 ^ 63) := rfl
  rw [e1, e2]
  simp only [word, Value.ofLimbs_add, Value.ofBits_zero, add_zero, zero_add]

theorem spHeadT_length : spHeadT.length = 127 := by decide +kernel

theorem spBody_drop_eq : spBody.drop 127 = Stmt.renameList spRen (spTailOf (spLeafKOf (word 1 (2 ^ 63)))) := by
  rw [spBody, spBodyT_split, renameList_append, List.drop_left' (by rw [renameList_length, spHeadT_length]),
    spLeafK_of, spPadCell]

set_option maxRecDepth 100000 in
theorem spBody_tail : (Fn.«sp_wots».core).body.drop 127 =
    Stmt.renameList spRen (spTailOf (spLeafKOf (word 1 (2 ^ 63)))) :=
  stmtsEqb_sound (by decide +kernel)

theorem spBody_drop_127 : (Fn.«sp_wots».core).body.drop 127 = spBody.drop 127 := by
  rw [spBody_tail, spBody_drop_eq]

end
end LeanVM.Guest.B1.Sig
