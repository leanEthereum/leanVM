module

public import NativeRustcVmArm.Ring.Loc
public import NativeRustcVmArm.Ring.Coeff.Exec
public import NativeRustcVmArm.Spec.Ring
public import NativeRustcVm.Ring.Math
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `ring_coefficients`: its frame, its values, its states

From the entry state `m0` (`f` at X0, `g` at X1, `out` at X2): the frame (`CFr`: 176 bytes, X19 to
X30 saved from byte `80`), the loop's model state after `p` turns (`rc m0 p`, `rcAt` of `f`'s and
`g`'s elements as read at the entry), `G`'s element `b` (`gG`) and where the loop keeps it
(`gLoc b`: two words of the frame or callee-saved registers; `gv`). The states: at the loop head
(`Head`), after the product of `f_p` and `G_b` (`MulD`), after the Frobenius image of `G_b`
(`SqD`); in each, `out` holds the coefficients so far (`EWsAt` at `out`).
-/

namespace NativeRustcVmArm.Ring.Coeff

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (Nat × XReg) :=
  [(80, .X29), (88, .X30), (96, .X28), (104, .X27), (112, .X26), (120, .X25), (128, .X24),
    (136, .X23), (144, .X22), (152, .X21), (160, .X20), (168, .X19)]

/-- `f`'s address. -/
def fA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- `g`'s address. -/
def gA (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- `out`'s address. -/
def oA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec

/-- The frame. -/
abbrev CFr (m0 m : MachineData) : Prop :=
  Fr m0 176 ringCoefficientsStack slots [] (InRange (oA m0) 1024) m

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 176

/-- `f`'s elements. -/
def fl (m0 : MachineData) : List EW := NativeRustcVm.ewsOf m0.dmem (fA m0) 8
/-- `g`'s elements. -/
def gl (m0 : MachineData) : List EW := NativeRustcVm.ewsOf m0.dmem (gA m0) 8

/-- `f_p`. -/
def fE (m0 : MachineData) (p : Nat) : EW :=
  NativeRustcVm.ewOf m0.dmem (fA m0 + BitVec.ofNat 64 (16 * p))

/-- The loop's model state after `p` turns. -/
def rc (m0 : MachineData) (p : Nat) : Array EW × Array EW := rcAt (fl m0) (gl m0).toArray p

/-- `G_b` after `p` turns. -/
def gG (m0 : MachineData) (p b : Nat) : EW := (rc m0 p).2.getD b 0

/-- Where the loop keeps `G_b`. -/
def gLoc : Nat → Sym × Sym
  | 0 => (.load 0 40 8, .load 0 48 8)
  | 1 => (.load 0 56 8, .load 0 64 8)
  | 2 => (.load 0 32 8, .load 0 72 8)
  | 3 => (.load 0 16 8, .load 0 24 8)
  | 4 => (.reg .X21, .load 0 8 8)
  | 5 => (.reg .X19, .reg .X29)
  | 6 => (.reg .X20, .reg .X23)
  | _ => (.reg .X22, .reg .X28)

/-- The value the loop keeps for `G_b` in `m`. -/
def gv [Labels] (m0 m : MachineData) (b : Nat) : EW :=
  ⟨locVal (fb m0) 176 m (gLoc b).1, locVal (fb m0) 176 m (gLoc b).2⟩

/-- The counter's slot. -/
def cntLoc : Sym := .load 0 0 8

/-- The products of the turn: `f_p · G_b'` for `b' < b`. -/
def prods (m0 : MachineData) (p b : Nat) : List EW :=
  (List.range b).map fun b' ↦ fE m0 p * gG m0 p b'

/-- The row of `out` turn `p` writes. -/
def rowA (m0 : MachineData) (p : Nat) : BitVec 64 := oA m0 + BitVec.ofNat 64 (128 * p)

/-- In the loop: the frame, the row (`X26 − 64`), `f_p` (`X27 − 8`). -/
abbrev envB (m0 : MachineData) (p : Nat) (m : MachineData) : Env :=
  Env.ofMachine m [(fb m0, 176), (rowA m0 p, 128), (fA m0 + BitVec.ofNat 64 (16 * p), 16)]

section
variable [Labels]

/-- What every state of turn `p` keeps. -/
structure Body (m0 : MachineData) (p : Nat) (m : MachineData) : Prop where
  fr : CFr m0 m
  lt : p < 8
  x26 : (m.regs.getXReg .X26).toBitVec = rowA m0 p + BitVec.ofNat 64 64
  x27 : (m.regs.getXReg .X27).toBitVec = fA m0 + BitVec.ofNat 64 (16 * p) + BitVec.ofNat 64 8

/-- **The loop head** of turn `p`. -/
structure Head (m0 : MachineData) (p : Nat) (m : MachineData) : Prop extends Body m0 p m where
  x10 : m.regs.getXReg .X10 = (8 - p : Nat).toUInt64
  g : ∀ b < 8, gv m0 m b = gG m0 p b
  out : NativeRustcVm.EWsAt m.dmem (oA m0) (rc m0 p).1.toList

/-- In turn `p`: the counter, `f_p` in X24, X25. -/
structure Turn (m0 : MachineData) (p : Nat) (m : MachineData) : Prop extends Body m0 p m where
  cnt : locVal (fb m0) 176 m cntLoc = (8 - p : Nat).toUInt64
  x24 : m.regs.getXReg .X24 = (fE m0 p).c0
  x25 : m.regs.getXReg .X25 = (fE m0 p).c1

/-- **After the product** `f_p · G_b`. -/
structure MulD (m0 : MachineData) (p b : Nat) (m : MachineData) : Prop extends Turn m0 p m where
  g : ∀ b' < 8, gv m0 m b' = gG m0 p b'
  x0 : m.regs.getXReg .X0 = (fE m0 p * gG m0 p b).c0
  x1 : m.regs.getXReg .X1 = (fE m0 p * gG m0 p b).c1
  out : NativeRustcVm.EWsAt m.dmem (oA m0) ((rc m0 p).1.toList ++ prods m0 p b)

/-- **After the Frobenius image** of `G_b`. -/
structure SqD (m0 : MachineData) (p b : Nat) (m : MachineData) : Prop extends Turn m0 p m where
  g : ∀ b' < 8, gv m0 m b' = if b' < b then frobenius8 (gG m0 p b') 1 else gG m0 p b'
  x0 : m.regs.getXReg .X0 = (frobenius8 (gG m0 p b) 1).c0
  x1 : m.regs.getXReg .X1 = (frobenius8 (gG m0 p b) 1).c1
  out : NativeRustcVm.EWsAt m.dmem (oA m0) (rc m0 (p + 1)).1.toList

end

/-! ## The blocks' checks -/

/-- The writes: in the frame below the slots, or in the row's bytes `lo` to `hi`. -/
def wrOk (lo hi : Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 80)) ||
    (w.r == 1 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi))

/-- The block stored X0, X1 at bytes `o`, `o + 8` of the row. -/
def rowSet (o : Nat) (S : SState) : Bool :=
  (List.range 8).all fun i ↦
    findWrite 1 (o + i) S.mem == some (.reg .X0, i) && findWrite 1 (o + 8 + i) S.mem == some (.reg .X1, i)

/-- The block kept the loop's registers and SP. -/
def ptrsOk (S : SState) : Bool :=
  S.reg .X26 == some (.ptr 1 64) && S.reg .X27 == some (.ptr 2 8) && S.sp == .ptr 0 0

/-- The block kept `G_b'` for `b' ≠ skip`. -/
def gKeep (skip : Nat) (S : SState) : Bool :=
  (List.range 8).all fun b ↦ b == skip || (locKeep 176 S (gLoc b).1 && locKeep 176 S (gLoc b).2)

/-- **A product block** (`b ≥ 1`): stores the last product at row byte `16 (b − 1)`, multiplies
`f_p` (X24, X25) by `G_b`. -/
def mulOk (b : Nat) (S : SState) : Bool :=
  S.reg .X0 == some (.reg .X24) && S.reg .X1 == some (.reg .X25) &&
    S.reg .X2 == some (gLoc b).1 && S.reg .X3 == some (gLoc b).2 &&
    S.reg .X24 == some (.reg .X24) && S.reg .X25 == some (.reg .X25) && ptrsOk S &&
    gKeep 8 S && locKeep 176 S cntLoc && rowSet (16 * (b - 1)) S && wrOk (16 * (b - 1)) (16 * b) S

/-- **A Frobenius block** (`b ≥ 1`): stores `G_(b−1)`'s image, squares `G_b` eight times. -/
def sqOk (b : Nat) (S : SState) : Bool :=
  S.reg .X0 == some (.lit 8) && S.reg .X1 == some (gLoc b).1 && S.reg .X2 == some (gLoc b).2 &&
    locSet 176 S (.reg .X0) (gLoc (b - 1)).1 && locSet 176 S (.reg .X1) (gLoc (b - 1)).2 &&
    S.reg .X24 == some (.reg .X24) && S.reg .X25 == some (.reg .X25) && ptrsOk S &&
    gKeep (b - 1) S && locKeep 176 S cntLoc && wrOk 128 128 S

end

end NativeRustcVmArm.Ring.Coeff
