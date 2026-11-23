module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.KeccakF
public import NativeRustcVmArm.Spec.Keccak
public meta import NativeRustcVmArm.Code.Vm.KeccakF
public meta import NativeRustcVmArm.Spec.Keccak

/-!
# `keccak_f`'s blocks, run by the symbolic executor

The four blocks of the leanVM crate's `keccak_f` (`NativeRustcVmArm.Vm.KeccakF`), each run from a
symbolic state whose region 0 is the 400-byte stack frame:

- `b0` (`entry`), from the entry: SP the frame's top, X0 the state (region 1, 200 bytes); it saves
  the callee-saved registers and calls `memcpy` to copy the round constants into the frame;
- `b1` (`load`), after `memcpy`: SP the frame's base, X19 the state; it loads the lanes;
- the round loop's body `b2` (`body`), from its head: SP the frame's base, the round counter X9 the
  variable 0 (below 201);
- the epilogue `b3` (`epilogue`): the state pointer the frame's slot 16 holds the base of region 1.
-/

namespace NativeRustcVmArm.KeccakF

open NativeRustcArm NativeRustcArm.Sym

set_option Elab.async false

@[expose] public section

/-- The entry's start: region 0 the frame below SP, region 1 the state X0 points to. -/
def startEntry : SState := init [(400, true), (200, false)] (.ptr 0 400) [(.X0, .ptr 1 0)]

/-- After `memcpy`: region 0 the frame from SP, region 1 the state X19 points to. -/
def startLoad : SState := init [(400, true), (200, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- The loop head's: region 0 the frame from SP, X9 the variable 0, below 201. -/
def startBody : SState := init [(400, true)] (.ptr 0 0) [(.X9, .var 0)] [] [(.var 0, 201)]

/-- The loop exit's: region 0 the frame from SP, region 1 the state, whose address the frame's
slot 16 holds. -/
def startEpi : SState := init [(400, true), (200, false)] (.ptr 0 0) [] [] [] [(.load 0 16 8, 1, 0)]

end

sym_block entry := exec Vm.KeccakF.b0 startEntry

sym_block load := exec Vm.KeccakF.b1 startLoad

sym_block body := exec Vm.KeccakF.b2 startBody

sym_block epilogue := exec Vm.KeccakF.b3 startEpi

end NativeRustcVmArm.KeccakF
