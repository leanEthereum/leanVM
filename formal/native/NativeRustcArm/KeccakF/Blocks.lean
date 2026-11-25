module

public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Common.KeccakF
public import NativeRustcArm.Spec.Keccak
public meta import NativeRustcArm.Code.Common.KeccakF
public meta import NativeRustcArm.Spec.Keccak

/-!
# `keccak_f`'s blocks, run by the symbolic executor

The three blocks of `keccak_f` (`NativeRustcArm.Common.KeccakF`), each run from a symbolic state
whose region 0 is the 192-byte stack frame:

- the prologue `b0` (`prologue`), from the entry: SP the frame's top, X0 the state (region 1, 200
  bytes); it saves the callee-saved registers, loads the lanes and computes the column parities;
- the round loop's body `b1` (`body`), from its head: SP the frame's base, the round counter X17 the
  variable 0 (below 185), the round constants at their label (region 1);
- the epilogue `b2` (`epilogue`), from the loop's exit: SP the frame's base, the state pointer the
  frame's slot 8 holds the base of region 1 (the state).
-/

namespace NativeRustcArm.KeccakF

open NativeRustcArm.Sym

set_option Elab.async false

@[expose] public section

/-- The prologue's start: region 0 the frame below SP, region 1 the state X0 points to. -/
def startPro : SState := init [(192, true), (200, false)] (.ptr 0 192) [(.X0, .ptr 1 0)]

/-- The loop head's: region 0 the frame from SP, region 1 the round constants, X17 the variable
0, below 185. -/
def startBody : SState :=
  init [(192, true), (192, false)] (.ptr 0 0) [(.X17, .var 0)] [(NativeRustcArm.roundConstantsLabel, 1)] [(.var 0, 185)]

/-- The loop exit's: region 0 the frame from SP, region 1 the state, whose address the frame's
slot 8 holds. -/
def startEpi : SState := init [(192, true), (200, false)] (.ptr 0 0) [] [] [] [(.load 0 8 8, 1, 0)]

end

sym_block prologue := exec Common.KeccakF.b0 startPro

sym_block body := exec Common.KeccakF.b1 startBody

sym_block epilogue := exec Common.KeccakF.b2 startEpi

end NativeRustcArm.KeccakF
