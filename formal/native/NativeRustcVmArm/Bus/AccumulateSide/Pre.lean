module

public import NativeRustcVmArm.Bus.AccumulateSide.Common

/-!
# `accumulate_side`: its precondition by name, its arguments as the model's

`Pre`: `AccumulateSidePre`'s conjuncts by name (`pre_of`). The model's arguments: `nA` the
fingerprints' count, `fpsA`, `wA`, `betaA`, `ptA`, `treeA`, the blocks `BA`.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm.Transcript (off)

public section

section
variable (m0 : MachineData)

/-- The fingerprints' count. -/
abbrev nA : Nat := (stackArg m0 0).toNat
/-- The fingerprints. -/
abbrev fpsA : Array EW := (NativeRustcVm.ewsOf m0.dmem m0.regs.X7.toBitVec (nA m0)).toArray
/-- The weights. -/
abbrev wA : Array EW := slice m0 (stackArg m0 8) (stackArg m0 16)
/-- `side_beta`. -/
abbrev betaA : EW := ⟨stackArg m0 24, stackArg m0 32⟩
/-- The point. -/
abbrev ptA : Array EW := slice m0 (stackArg m0 40) (stackArg m0 48)
/-- The tree's value. -/
abbrev treeA : EW := ⟨stackArg m0 56, stackArg m0 64⟩

end

/-- The side's blocks at the layout's heights and rows. -/
abbrev BA (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block) : Array BusBlockW :=
  (bl.map (blockW L.tableLogHeights rows)).toArray

section
variable [Labels]

/-- `AccumulateSidePre`'s conjuncts. -/
structure Pre (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (Fm : Array (Array FormW)) (SL : BusLayoutW) (m0 : MachineData) : Prop where
  stack : StackOk m0 N
  rodata : RodataAt m0 N
  args : Readable m0 m0.regs.SP.toBitVec 72
  side : m0.regs.X2.toNat < 3
  forms : FormsAt m0.dmem m0.regs.X1.toBitVec Fm
  formsOk : InOk m0 m0.regs.X1.toBitVec formsBytes N
  formsRo : RodataApart m0.regs.X1.toBitVec formsBytes
  blen : 1 ≤ bl.length
  x4 : m0.regs.X4.toNat = bl.length
  bown : ∀ x ∈ bl, x.owner < nTables ∧ x.tuple < NativeRustcVm.Data.tuples.length
  blocks : NativeRustcVm.BytesAt m0.dmem m0.regs.X3.toBitVec
    (bl.flatMap NativeRustcVm.Data.Block.bytes)
  blocksOk : InOk m0 m0.regs.X3.toBitVec (16 * bl.length) N
  lay : LayoutWAt m0.dmem m0.regs.X5.toBitVec L
  rows_size : rows.size = nTables
  rowsW : NativeRustcVm.WordsAt m0.dmem (off m0.regs.X5.toBitVec 72) (rows.toList.map Nat.toUInt64)
  layOk : InOk m0 m0.regs.X5.toBitVec layoutBytes N
  sl : BusLayoutWAt m0.dmem m0.regs.X6.toBitVec SL
  sl_size : SL.tables.size = bl.length
  slOk : InOk m0 m0.regs.X6.toBitVec busLayoutBytes N
  fp : 0 < nA m0 → InOk m0 m0.regs.X7.toBitVec (16 * nA m0) N
  w : SliceOk m0 (stackArg m0 8) (stackArg m0 16) N
  pn : (stackArg m0 48).toNat < 64
  pt : SliceOk m0 (stackArg m0 40) (stackArg m0 48) N
  fits : SideFits Fm m0.regs.X2.toNat (BA L rows bl) SL (fpsA m0) (wA m0) (betaA m0) (ptA m0)
    (treeA m0)
  out : InOk m0 m0.regs.X0.toBitVec 24 N
  outRo : RodataApart m0.regs.X0.toBitVec 24
  outF : Apart m0.regs.X0.toBitVec 24 m0.regs.X1.toBitVec formsBytes
  fB : Apart m0.regs.X1.toBitVec formsBytes m0.regs.X3.toBitVec (16 * bl.length)
  fL : Apart m0.regs.X1.toBitVec formsBytes m0.regs.X5.toBitVec layoutBytes
  fSL : Apart m0.regs.X1.toBitVec formsBytes m0.regs.X6.toBitVec busLayoutBytes
  fFp : 0 < nA m0 → Apart m0.regs.X1.toBitVec formsBytes m0.regs.X7.toBitVec (16 * nA m0)
  fW : Apart m0.regs.X1.toBitVec formsBytes (stackArg m0 8).toBitVec
    (16 * (stackArg m0 16).toNat)
  fPt : Apart m0.regs.X1.toBitVec formsBytes (stackArg m0 40).toBitVec
    (16 * (stackArg m0 48).toNat)
  fArgs : Apart m0.regs.X1.toBitVec formsBytes m0.regs.SP.toBitVec 72
  slArgs : Apart m0.regs.X6.toBitVec busLayoutBytes m0.regs.SP.toBitVec 72
  slFp : 0 < nA m0 → Apart m0.regs.X6.toBitVec busLayoutBytes m0.regs.X7.toBitVec (16 * nA m0)

theorem pre_of {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
    {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}
    (h : AccumulateSidePre L rows bl Fm SL m0) : Pre L rows bl Fm SL m0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36⟩

end

end

end NativeRustcVmArm.Bus.AccumulateSide
