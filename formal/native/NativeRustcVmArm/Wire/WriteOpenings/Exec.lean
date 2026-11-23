module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.WriteOpenings
public meta import NativeRustcVmArm.Code.Vm.WriteOpenings

/-!
# `write_openings`' blocks, run by the symbolic executor

Region 0 is the frame below SP throughout: its 176 bytes, or 192 with the two stack arguments
above it (`entryS`, `argS`). The other regions are the bytes a block reads or writes, named by an
alias of the register (or the address) that points there.

- `entryS`: the prologue (`b0`), region 1 the phase's three head words at the loaded `out`.
- `argS`: `b1`, reading the sibling counts' address above the frame.
- `frS`: the blocks without memory but the frame's.
- `qS2`, `qS25`, `qS39`: the query's word (region 1, X2) and the opening's first word (region 2).
- `pS3`, `pS26`, `pS40`: a position's word (region 1).
- `vS9`, `vS32`: four leaf words (region 1) to the opening (region 2).
- `sS12`, `sS35`: one leaf word (region 1) to the opening (region 2).
- `dS15`: a level's four digest words (region 1, X20 minus 24).
- `cS16`: a level's sibling count (region 1).
- `nS20`: the found node (region 1).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- `[xb, xi]` (no shift) for `xi = xa * xm`. -/
def mulAddr (xb xa xm : XReg) : Sym :=
  .bin .add .W64 (.reg xb) (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.bin .mul .W64 (.reg xa) (.reg xm)))

/-- `[xb, xi, lsl #3]`. -/
def idxAddr (xb xi : XReg) : Sym :=
  .bin .add .W64 (.reg xb) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg xi))

/-- The node `b20` loads: `40 * X1 + X23 + X28`. -/
def nodeAddr : Sym :=
  .bin .add .W64 (.bin .add .W64 (.bin .mul .W64 (.reg .X1) (.lit 40)) (.reg .X23)) (.reg .X28)

/-- At the entry: the frame and the arguments (region 0), SP at the frame's end; the head words
(region 1). -/
def entryS : SState := init [(192, true), (24, false)] (.ptr 0 176) [] [] [] [(.load 0 184 8, 1, 0)]

/-- The frame and the arguments (region 0, SP). -/
def argS : SState := init [(192, true)] (.ptr 0 0)

/-- The frame (region 0, SP). -/
def frS : SState := init [(176, true)] (.ptr 0 0)

/-- A query's word at X2 (region 1), the opening's first word (region 2). -/
def qS (a : Sym) : SState :=
  init [(176, true), (8, false), (8, false)] (.ptr 0 0) [] [] [] [(.reg .X2, 1, 0), (a, 2, 0)]

/-- A word (region 1) at `a`. -/
def pS (a : Sym) : SState := init [(176, true), (8, false)] (.ptr 0 0) [] [] [] [(a, 1, 0)]

/-- `n` bytes at `xs` minus `os` (region 1) to `n` bytes at `xd` minus `od` (region 2). -/
def cpS (n : Nat) (xs : XReg) (os : Int) (xd : XReg) (od : Int) : SState :=
  init [(176, true), (n, false), (n, false)] (.ptr 0 0) [] [] []
    [(.reg xs, 1, os), (.reg xd, 2, od)]

/-- A level's four digest words (region 1) from X20 minus 24. -/
def dS : SState := init [(176, true), (32, false)] (.ptr 0 0) [] [] [] [(.reg .X20, 1, 24)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 argS
sym_block run_b2 := exec b2 (qS (mulAddr .X3 .X9 .X11))
sym_block run_b3 := exec b3 (pS (idxAddr .X19 .X10))
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 (cpS 32 .X9 16 .X10 24)
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 (cpS 8 .X8 0 .X9 0)
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 dS
sym_block run_b16 := exec b16 (pS (idxAddr .X29 .X27))
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 frS
sym_block run_b20 :=
  exec b20 (init [(176, true), (40, false)] (.ptr 0 0) [] [] [] [(nodeAddr, 1, 0)])
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 frS
sym_block run_b24 := exec b24 frS
sym_block run_b25 := exec b25 (qS (mulAddr .X3 .X11 .X12))
sym_block run_b26 := exec b26 (pS (idxAddr .X19 .X15))
sym_block run_b27 := exec b27 frS
sym_block run_b28 := exec b28 frS
sym_block run_b29 := exec b29 frS
sym_block run_b30 := exec b30 frS
sym_block run_b31 := exec b31 frS
sym_block run_b32 := exec b32 (cpS 32 .X14 16 .X15 24)
sym_block run_b33 := exec b33 frS
sym_block run_b34 := exec b34 frS
sym_block run_b35 := exec b35 (cpS 8 .X13 0 .X14 0)
sym_block run_b36 := exec b36 frS
sym_block run_b37 := exec b37 frS
sym_block run_b38 := exec b38 frS
sym_block run_b39 := exec b39 (qS (mulAddr .X3 .X9 .X8))
sym_block run_b40 := exec b40 (pS (idxAddr .X19 .X10))
sym_block run_b41 := exec b41 frS
sym_block run_b42 := exec b42 frS
sym_block run_b43 := exec b43 frS
sym_block run_b44 := exec b44 frS
sym_block run_b45 := exec b45 frS
sym_block run_b46 := exec b46 frS

end NativeRustcVmArm.Wire.WriteOpenings
