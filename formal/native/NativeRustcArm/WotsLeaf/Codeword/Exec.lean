module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.WotsLeaf.Steps
public import NativeRustcArm.Code.Xmss.WotsLeaf
public meta import NativeRustcArm.Code.Xmss.WotsLeaf
public meta import NativeRustcArm.WotsLeaf.FrameS

/-!
# The codeword's blocks, run by the symbolic executor

`b6`, `b7`, `b8`, `b10` in the frame (`frameS []`); `b11` (the tag `0` stored at `out`) with
`out` as region 1 (`s11`). The digits' loop `b9` (`.LWotsLeaf_3`) runs from `s9 j`, its turn
`j < 14` (X11 the frame's byte `381 + 4 j`, X12 `6 + 8 j`, literals): each turn stores the
digits `4 j .. 4 j + 3` (`digitSym`) and the checks `ok9` hold for every turn (`run_b9`, `ok9_all`,
decided by the kernel).
-/

namespace NativeRustcArm.WotsLeafProof.Codeword

open NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf

@[expose] public section

/-- At `b11`: `out` (region 1) at X19. -/
def s11 : SState := init [(2752, true), (75, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- At turn `j` of the digits' loop. -/
def s9 (j : Nat) : SState := frameS [(.X11, .ptr 0 (381 + 4 * j)), (.X12, .lit (6 + 8 * j))]

/-- Digit `d`'s symbolic value: bits `2 d, 2 d + 1` of the 128-bit digest `X8:X9` (`X10` is
`X8 << 1`), as the loop computes them. -/
def digitSym (d : Nat) : Sym :=
  if 2 * d < 64 then
    .bin .and .W32 (.bin .orr .W64 (.bin .lslv .W64 (.reg .X10) (.lit (4294967295 - 2 * d)))
      (.bin .lsrv .W64 (.reg .X9) (.lit (2 * d)))) (.lit 3)
  else .bin .and .W32 (.bin .lsrv .W64 (.reg .X8) (.lit (2 * d))) (.lit 3)

/-- The four digits a turn stores. -/
def coversDigits (ws : List Write) (j : Nat) : Bool :=
  (List.range 4).all fun t ↦ (List.range 1).all fun i ↦
    findWrite 0 (380 + 4 * j + t + i) ws == some (digitSym (4 * j + t), i)

/-- What a turn of the loop does (decided on the literal state): its digits stored, its other
writes none, SP, X29 and the registers it does not set kept, X11 and X12 the next turn's, the
exit back to the loop head but after the last turn. -/
def ok9 (j : Nat) : Bool :=
  match exec b9 (s9 j) with
  | some (S, x) =>
    coversDigits S.mem j && S.mem.length == 4 &&
      S.mem.all (fun w ↦ w.r == 0 && decide (380 + 4 * j ≤ w.off) && decide (w.off + w.n ≤ 384 + 4 * j)) &&
      S.sp == .ptr 0 0 && S.reg .X29 == some (.ptr 0 2656) && blockOK S &&
      Run.noWriteIn S 0 (380 + 4 * j) && Run.noWriteIn S 1776 32 &&
      S.reg .X11 == some (.ptr 0 (381 + 4 * (j + 1))) && S.reg .X12 == some (.lit (6 + 8 * (j + 1))) &&
      [XReg.X8, .X9, .X10, .X19, .X20, .X22].all (fun y ↦ S.reg y == some (.reg y)) &&
      x == .cond (.lit (j != 13)) NativeRustcArm.Xmss.WotsLeaf.label_3
  | none => false

end

set_option Elab.async false

sym_block run_b6 := exec b6 (frameS [])
sym_block run_b7 := exec b7 (frameS [])
sym_block run_b8 := exec b8 (frameS [])
sym_block run_b10 := exec b10 (frameS [])
sym_block run_b11 := exec b11 s11

public theorem ok9_all : ∀ j < 14, ok9 j = true := by decide +kernel

end NativeRustcArm.WotsLeafProof.Codeword
