/-
  LeanVM.Guest.B1.Sig.SpWotsData1

  `sp_wots` in the guest's core IR agrees with the template `spBody` on dispatches 11 to 21, the checks and the leaf (statements 95 on).
-/

module

public import LeanVM.Guest.Pack.sp_wots.Core
public import LeanVM.Guest.B1.Sig.SpWotsLayout
import LeanVM.Guest.B1.Sig.Decide
public import LeanVM.Guest.B1.Common.Basic
import LeanVM.Core.Value.Tower
import LeanVM.Core.Value.FieldBits

namespace LeanVM.Guest.B1.Sig

open LeanVM.Core LeanVM.Parameters

@[expose] public section

/-! Dispatches 11 to 21 (statements 95 to 105), one a run, compared by `stmtsEqb`, each its own
kernel evaluation to bound its memory. -/

set_option maxRecDepth 100000 in
theorem spBody_run_95 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 95).take 1) ((spBody.drop 95).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_96 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 96).take 1) ((spBody.drop 96).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_97 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 97).take 1) ((spBody.drop 97).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_98 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 98).take 1) ((spBody.drop 98).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_99 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 99).take 1) ((spBody.drop 99).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_100 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 100).take 1) ((spBody.drop 100).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_101 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 101).take 1) ((spBody.drop 101).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_102 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 102).take 1) ((spBody.drop 102).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_103 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 103).take 1) ((spBody.drop 103).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_104 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 104).take 1) ((spBody.drop 104).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_105 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 105).take 1) ((spBody.drop 105).take 1) = true := by
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

theorem spHeadT_length : spHeadT.length = 106 := by decide +kernel

theorem spBody_drop_eq : spBody.drop 106 = Stmt.renameList spRen (spTailOf (spLeafKOf (word 1 (2 ^ 63)))) := by
  rw [spBody, spBodyT_split, renameList_append, List.drop_left' (by rw [renameList_length, spHeadT_length]),
    spLeafK_of, spPadCell]

set_option maxRecDepth 100000 in
theorem spBody_tail : (Fn.«sp_wots».core).body.drop 106 =
    Stmt.renameList spRen (spTailOf (spLeafKOf (word 1 (2 ^ 63)))) :=
  stmtsEqb_sound (by decide +kernel)

theorem spBody_drop_106 : (Fn.«sp_wots».core).body.drop 106 = spBody.drop 106 := by
  rw [spBody_tail, spBody_drop_eq]

end
end LeanVM.Guest.B1.Sig
