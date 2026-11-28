module

public import NativeRustcVmX64.Bus.AccumulateSide.Common

/-!
# `accumulate_side`: the values its body keeps (x86-64)

The table `Vt SL m0 lp`: below `32` the values fixed for the call (`sv`: the arguments, the
known part, the ones over the framework, …), from `32` a loop's values (`lp`): the known part's
(`lpK`), the framework ones' (`lpO`). The descriptions: which locations keep which of them at
each program point (`DE` at the entry, `D0` after the prologue, `DK` the known part's head, `D6`
the ones', `DO` their loop's head, `D12` after them).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-! ## The values -/

section
variable (SL : BusLayoutW) (m0 : MachineData)

/-- The framework blocks the known part reads: `min` of the fingerprints' count and theirs. -/
abbrev cA : Nat := min (nA m0) SL.framework.size

/-- The known part. -/
abbrev knA (i : Nat) : EW := knownN SL (ptA m0) (fpsA m0) (betaA m0) i

/-- Framework placement `i`. -/
abbrev fpl (i : Nat) : LeanVM.Protocol.Verifier.Placement := SL.framework.getD i default

/-- Table placement `j`. -/
abbrev tpl (j : Nat) : LeanVM.Protocol.Verifier.Placement := SL.tables.getD j default

/-- `eq_above(p, point)`'s arguments: the rest's count, the selector, the rest's address. -/
def eqN (p : LeanVM.Protocol.Verifier.Placement) : UInt64 :=
  ((stackArg m0 8).toNat - p.variableCount).toUInt64
def eqS (p : LeanVM.Protocol.Verifier.Placement) : UInt64 :=
  (p.index >>> p.variableCount).toUInt64
def eqP (p : LeanVM.Protocol.Verifier.Placement) : UInt64 :=
  .ofBitVec (if (stackArg m0 8).toNat < p.variableCount then 8#64
    else stackArg m0 7 + BitVec.ofNat 64 (16 * p.variableCount))

/-- **The fixed values.** -/
def sv : Nat → UInt64
  | 0 => .ofBitVec (reg m0 .rdi)
  | 1 => .ofBitVec (reg m0 .rsi)
  | 2 => .ofBitVec (reg m0 .rdx)
  | 3 => .ofBitVec (reg m0 .rcx)
  | 4 => .ofBitVec (reg m0 .r8)
  | 5 => .ofBitVec (reg m0 .r9)
  | 6 => .ofBitVec (stackArg m0 0)
  | 7 => .ofBitVec (stackArg m0 1)
  | 8 => .ofBitVec (stackArg m0 2)
  | 9 => .ofBitVec (stackArg m0 3)
  | 10 => .ofBitVec (stackArg m0 4)
  | 11 => .ofBitVec (stackArg m0 5)
  | 12 => .ofBitVec (stackArg m0 6)
  | 13 => .ofBitVec (stackArg m0 7)
  | 14 => .ofBitVec (stackArg m0 8)
  | 15 => .ofBitVec (stackArg m0 9)
  | 16 => .ofBitVec (stackArg m0 10)
  | 17 => SL.framework.size.toUInt64
  | 18 => .ofBitVec (stackArg m0 0 + 16#64)
  | 19 => (16 * cA SL m0).toUInt64
  | 20 => (treeA m0 + knA SL m0 (cA SL m0)).c0
  | 21 => (treeA m0 + knA SL m0 (cA SL m0)).c1
  | 22 => (onesF SL (ptA m0) SL.framework.size).c0
  | 23 => (onesF SL (ptA m0) SL.framework.size).c1
  | 24 => .ofBitVec (reg m0 .rdx * 5928#64 + reg m0 .rsi)
  | 25 => (16 * (reg m0 .r8).toNat).toUInt64
  | 26 => 8
  | 27 => 0
  | 28 => (cA SL m0).toUInt64
  | 29 => .ofBitVec (stackArg m0 0 + 16#64 + BitVec.ofNat 64 (16 * SL.framework.size))
  | 30 => SL.tables.size.toUInt64
  | _ => 0

/-- The known part's values at turn `i`. -/
def lpK (i : Nat) : Nat → UInt64
  | 0 => (16 * i).toUInt64
  | 1 => (knA SL m0 i).c0
  | 2 => (knA SL m0 i).c1
  | 3 => eqN m0 (fpl SL i)
  | 4 => eqS (fpl SL i)
  | 5 => eqP m0 (fpl SL i)
  | 6 => (betaA m0 + (fpsA m0).getD i 0).c0
  | 7 => (betaA m0 + (fpsA m0).getD i 0).c1
  | 8 => (fsel SL (ptA m0) i).c0
  | 9 => (fsel SL (ptA m0) i).c1
  | 10 => (fsel SL (ptA m0) i * (betaA m0 + (fpsA m0).getD i 0)).c0
  | 11 => (fsel SL (ptA m0) i * (betaA m0 + (fpsA m0).getD i 0)).c1
  | _ => 0

/-- The framework ones' values at turn `k`. -/
def lpO (k : Nat) : Nat → UInt64
  | 0 => .ofBitVec (stackArg m0 0 + 16#64 + BitVec.ofNat 64 (16 * k))
  | 1 => (onesF SL (ptA m0) k).c0
  | 2 => (onesF SL (ptA m0) k).c1
  | 3 => (fsel SL (ptA m0) k).c0
  | 4 => (fsel SL (ptA m0) k).c1
  | _ => 0

end

/-- **The table**: the fixed values below `32`, a loop's from `32`. -/
def Vt (SL : BusLayoutW) (m0 : MachineData) (lp : Nat → UInt64) (i : Nat) : UInt64 :=
  if i < 32 then sv SL m0 i else lp (i - 32)

/-! ## The descriptions -/

/-- A frame word. -/
abbrev Lw (o : Nat) : Sym := .load 0 o 8
/-- A register. -/
abbrev Rg (r : Reg64) : Sym := .reg r

/-- The literals `8` and `0`. -/
def Dl : List (Sym × Nat) := [(.lit 8, 26), (.lit 0, 27)]

/-- The eleven stack arguments, region `1`'s words. -/
def DA : List (Sym × Nat) :=
  [(.load 1 0 8, 6), (.load 1 8 8, 7), (.load 1 16 8, 8), (.load 1 24 8, 9), (.load 1 32 8, 10),
    (.load 1 40 8, 11), (.load 1 48 8, 12), (.load 1 56 8, 13), (.load 1 64 8, 14),
    (.load 1 72 8, 15), (.load 1 80 8, 16)]

/-- At the entry: the register arguments, the stack arguments. -/
def DE : List (Sym × Nat) :=
  [(Rg .rdi, 0), (Rg .rsi, 1), (Rg .rdx, 2), (Rg .rcx, 3), (Rg .r8, 4), (Rg .r9, 5)] ++ DA ++ Dl

/-- The frame's words throughout: the output, the forms, the blocks, the layout. -/
def FWc : List (Sym × Nat) := [(Lw 80, 0), (Lw 88, 1), (Lw 96, 3), (Lw 104, 5)]
/-- … the side and the blocks' count, and the tree's value before the known part is added. -/
def FWa : List (Sym × Nat) := FWc ++ [(Lw 16, 2), (Lw 40, 4), (Lw 64, 15), (Lw 72, 16)]
/-- … after. -/
def FWb : List (Sym × Nat) := FWc ++ [(Lw 16, 2), (Lw 40, 4), (Lw 64, 20), (Lw 72, 21)]

/-- After the prologue. -/
def D0 : List (Sym × Nat) :=
  [(Rg .rax, 11), (Rg .rdi, 13), (Rg .r8, 12), (Rg .rbp, 14), (Rg .r9, 26)] ++ FWa ++ Dl

/-- The known part's frame words. -/
def FK : List (Sym × Nat) := FWa ++ [(Lw 56, 17), (Lw 24, 19)] ++ Dl
/-- The known part's head, but its loop values. -/
def DKf : List (Sym × Nat) :=
  [(Rg .rax, 11), (Rg .rdi, 13), (Rg .r8, 12), (Rg .r9, 26), (Rg .r12, 18)] ++ FK
/-- The known part's loop values: the offset, the sum. -/
def LK : List (Sym × Nat) := [(Rg .rbp, 32), (Rg .r15, 33), (Rg .r13, 34)]
/-- The known part's head. -/
def DK : List (Sym × Nat) := DKf ++ LK
/-- After `b2a`, but `eq_above`'s arguments. -/
def D2 : List (Sym × Nat) :=
  [(Rg .rax, 11), (Rg .r8, 12), (Rg .r12, 18), (Rg .rcx, 7)] ++ LK ++ FK
/-- `eq_above`'s arguments. -/
def E2 : List (Sym × Nat) := [(Rg .rdi, 35), (Rg .rsi, 36), (Rg .rdx, 37)]
/-- At `b2b`'s call. -/
def DKc : List (Sym × Nat) :=
  [(Rg .r12, 18)] ++ LK ++ FK ++ [(Rg .rbx, 38), (Rg .r14, 39)]

/-- The ones' head (from `b6`). -/
def D6 : List (Sym × Nat) := [(Rg .rdi, 13), (Rg .r12, 18), (Rg .rbp, 14), (Rg .r13, 17)] ++ FWb ++ Dl
/-- The framework ones' loop, but its loop values. -/
def DOf : List (Sym × Nat) := [(Rg .rdi, 13), (Rg .rbp, 14), (Rg .rbx, 27), (Rg .r13, 29)] ++ FWb ++ Dl
/-- The ones' loop values: the placement's address, the sum. -/
def LO : List (Sym × Nat) := [(Rg .r12, 32), (Rg .r14, 33), (Rg .r15, 34)]
/-- The framework ones' loop head. -/
def DO : List (Sym × Nat) := DOf ++ LO
/-- At `b8`'s call. -/
def DOc : List (Sym × Nat) := [(Rg .rbp, 14), (Rg .rbx, 27), (Rg .r13, 29)] ++ FWb ++ Dl ++ LO

/-- What `b7` keeps. -/
def D7 : List (Sym × Nat) := [(Rg .rdi, 13), (Rg .rbp, 14), (Rg .r12, 18)] ++ FWb ++ Dl
/-- What `b11` keeps. -/
def D11 : List (Sym × Nat) := [(Rg .rdi, 13), (Rg .rbp, 14)] ++ FWb ++ Dl

/-- After the ones (`b12`). -/
def D12 : List (Sym × Nat) := [(Rg .rdi, 13), (Rg .rbp, 14), (Rg .r14, 22), (Rg .r15, 23)] ++ FWb ++ Dl
/-- At `memcpy`'s call and after it. -/
def D14 : List (Sym × Nat) := [(Rg .rbp, 14), (Rg .r14, 22), (Rg .r15, 23)] ++ FWb ++ Dl
/-- After `b15`: and the blocks' count in RCX. -/
def D15 : List (Sym × Nat) := D14 ++ [(Rg .rcx, 4)]
/-- The table loop's frame words. -/
def FT : List (Sym × Nat) :=
  [(Lw 40, 25), (Lw 88, 24), (Lw 96, 3), (Lw 104, 5), (Lw 80, 0), (Lw 64, 20), (Lw 72, 21)] ++ Dl
/-- The table loop's head, but its loop values. -/
def DTf : List (Sym × Nat) := [(Rg .rdi, 13), (Rg .rbp, 14), (Rg .r8, 27), (Rg .r9, 26)] ++ FT
/-- The table loop's values: the offset, the padding rows, the ones. -/
def LT : List (Sym × Nat) := [(Rg .r12, 32), (Rg .rsi, 33), (Rg .rdx, 34), (Rg .r14, 35), (Rg .r15, 36)]
/-- The table loop's head. -/
def DT : List (Sym × Nat) := DTf ++ LT

end

public section

theorem Vt_lt {SL : BusLayoutW} {m0 : MachineData} {lp lp' : Nat → UInt64} {i : Nat} (hi : i < 32) :
    Vt SL m0 lp i = Vt SL m0 lp' i := by
  simp [Vt, hi]

theorem Vt_lp {SL : BusLayoutW} {m0 : MachineData} {lp : Nat → UInt64} (k : Nat) :
    Vt SL m0 lp (32 + k) = lp k := by
  simp [Vt]

theorem Vt_sv {SL : BusLayoutW} {m0 : MachineData} {lp : Nat → UInt64} {i : Nat} (hi : i < 32) :
    Vt SL m0 lp i = sv SL m0 i := by
  simp [Vt, hi]

end

public section
variable {SL : BusLayoutW} {m0 : MachineData} {lp : Nat → UInt64}

theorem Vt32 : Vt SL m0 lp 32 = lp 0 := rfl
theorem Vt33 : Vt SL m0 lp 33 = lp 1 := rfl
theorem Vt34 : Vt SL m0 lp 34 = lp 2 := rfl
theorem Vt35 : Vt SL m0 lp 35 = lp 3 := rfl
theorem Vt36 : Vt SL m0 lp 36 = lp 4 := rfl
theorem Vt15 : Vt SL m0 lp 15 = (treeA m0).c0 := rfl
theorem Vt16 : Vt SL m0 lp 16 = (treeA m0).c1 := rfl
theorem Vt20 : Vt SL m0 lp 20 = (treeA m0 + knA SL m0 (cA SL m0)).c0 := rfl
theorem Vt21 : Vt SL m0 lp 21 = (treeA m0 + knA SL m0 (cA SL m0)).c1 := rfl
theorem Vt22 : Vt SL m0 lp 22 = (onesF SL (ptA m0) SL.framework.size).c0 := rfl
theorem Vt23 : Vt SL m0 lp 23 = (onesF SL (ptA m0) SL.framework.size).c1 := rfl
theorem lpK1 (i : Nat) : lpK SL m0 i 1 = (knA SL m0 i).c0 := rfl
theorem lpK2 (i : Nat) : lpK SL m0 i 2 = (knA SL m0 i).c1 := rfl

end

end NativeRustcVmX64.Bus.AccumulateSide
