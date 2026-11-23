module

public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVmArm.Ring.Psi.Exec
public import NativeRustcVmArm.Spec.Ring
public import NativeRustcVm.Ring.Math
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `ring_psi`: its frame and its states

From the entry state `m0` (`value` in X0, X1, `g` at X2): the frame (`PFr`: 48 bytes, X19 to X23
and X30 saved), `g`'s elements as read at the entry (`gE`), the loop's state after `j` elements
(`ps`). Between the calls, X19 holds `g` (`Mid`); after the call of block `2j` the product `g_j ·
v^(2^j)` is in X0, X1 (`Odd`), after the next squaring the power `v^(2^(j+1))` (`Even`).
-/

namespace NativeRustcVmArm.Ring.Psi

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (Nat × XReg) :=
  [(0, .X30), (8, .X23), (16, .X22), (24, .X21), (32, .X20), (40, .X19)]

/-- The callee-saved registers the prologue does not save. -/
def keep : List XReg := [.X24, .X25, .X26, .X27, .X28, .X29]

/-- The frame. -/
abbrev PFr (m0 m : MachineData) : Prop := Fr m0 48 ringPsiStack slots keep (fun _ ↦ False) m

/-- `g`'s address. -/
def gA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec

/-- `g`'s elements as read at the entry. -/
def gl (m0 : MachineData) : List EW := NativeRustcVm.ewsOf m0.dmem (gA m0) 8

/-- Element `j` of `g`. -/
def gE (m0 : MachineData) (j : Nat) : EW :=
  NativeRustcVm.ewOf m0.dmem (gA m0 + BitVec.ofNat 64 (16 * j))

/-- The value. -/
def vOf (m0 : MachineData) : EW := ⟨m0.regs.X0, m0.regs.X1⟩

/-- The loop's state after `j` elements: the sum and the power. -/
def ps (m0 : MachineData) (j : Nat) : EW × EW := ((gl m0).take j).foldl psiStep (0, vOf m0)

/-- Between calls: the frame, `g` in X19. -/
structure Mid (m0 m : MachineData) : Prop where
  fr : PFr m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X2

/-- After the squaring of turn `j - 1`: the power in X0, X1, the sum in X22, X23. -/
structure Even (m0 : MachineData) (j : Nat) (m : MachineData) : Prop extends Mid m0 m where
  x0 : m.regs.getXReg .X0 = (ps m0 j).2.c0
  x1 : m.regs.getXReg .X1 = (ps m0 j).2.c1
  x22 : m.regs.getXReg .X22 = (ps m0 j).1.c0
  x23 : m.regs.getXReg .X23 = (ps m0 j).1.c1

/-- After the product of turn `j`: it in X0, X1, the power in X20, X21, the sum in X22, X23. -/
structure Odd (m0 : MachineData) (j : Nat) (m : MachineData) : Prop extends Mid m0 m where
  x0 : m.regs.getXReg .X0 = (EW.mul (gE m0 j) (ps m0 j).2).c0
  x1 : m.regs.getXReg .X1 = (EW.mul (gE m0 j) (ps m0 j).2).c1
  x20 : m.regs.getXReg .X20 = (ps m0 j).2.c0
  x21 : m.regs.getXReg .X21 = (ps m0 j).2.c1
  x22 : m.regs.getXReg .X22 = (ps m0 j).1.c0
  x23 : m.regs.getXReg .X23 = (ps m0 j).1.c1

/-- The registers a block sets: each `(r, v)`, `r` holds `v`. -/
def regsAre (S : SState) (l : List (XReg × Sym)) : Bool := l.all fun p ↦ decide (S.reg p.1 = some p.2)

/-- The registers the blocks keep. -/
def keepRegs : List (XReg × Sym) := keep.map fun r ↦ (r, .reg r)

/-- What block `2j` (`j ≥ 1`) sets: `g_j` in X0, X1, the power (X0, X1) in X2, X3 and X20, X21. -/
def evenRegs (j : Nat) : List (XReg × Sym) :=
  [(.X0, .load 0 (16 * j) 8), (.X1, .load 0 (16 * j + 8) 8), (.X2, .reg .X0), (.X3, .reg .X1),
    (.X19, .ptr 0 0), (.X20, .reg .X0), (.X21, .reg .X1), (.X22, .reg .X22), (.X23, .reg .X23)] ++
    keepRegs

/-- What block `2j + 1` sets: the sum plus the product in X22, X23, the power squared's arguments
in X0 to X3. -/
def oddRegs : List (XReg × Sym) :=
  [(.X0, .reg .X20), (.X1, .reg .X21), (.X2, .reg .X20), (.X3, .reg .X21), (.X19, .ptr 0 0),
    (.X22, .bin .eor .W64 (.reg .X0) (.reg .X22)), (.X23, .bin .eor .W64 (.reg .X1) (.reg .X23))] ++
    keepRegs

end

end NativeRustcVmArm.Ring.Psi
