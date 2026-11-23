module

public import NativeRustcX64.Sym
public import NativeRustcVmX64.Code.Vm.KeccakF
public import NativeRustcVmX64.Spec.Keccak
public meta import NativeRustcVmX64.Code.Vm.KeccakF
public meta import NativeRustcVmX64.Spec.Keccak

/-!
# `keccak_f`'s blocks, run by the symbolic executor (x86-64)

The four blocks of the leanVM crate's x86-64 `keccak_f` (`NativeRustcVmX64.Vm.KeccakF`), each run
from a symbolic state whose region 0 is the frame: the 488 bytes from 480 below the entry's RSP
(`memcpy`'s return address at 0, the 424-byte frame from 8, the six pushed registers from 432, the
return address at 480):

- `b0` (`entry`), from the entry: RSP the frame's offset 480, RDI the state (region 1, 200 bytes);
  it pushes the callee-saved registers and calls `memcpy` to copy the round constants to the
  frame's offset 240;
- `b1` (`load`), after `memcpy`: RSP the frame's offset 8, RBX the state; it loads the lanes and
  sets the counter RAX to 2;
- the round loop's body `b2` (`body`), from its head: RSP the frame's offset 8, the counter RAX the
  variable 0 (below 26);
- the epilogue `b3` (`epilogue`): the state pointer the frame's offset 184 holds the base of
  region 1.
-/

namespace NativeRustcVmX64.KeccakF

open NativeRustcX64 NativeRustcX64.Sym

set_option Elab.async false

@[expose] public section

/-- The entry's start: region 0 the frame, RSP at its offset 480, region 1 the state RDI points
to. -/
def startEntry : SState :=
  (init [488, 200, 8] [(.rsp, .ptr 0 480), (.rdi, .ptr 1 0)] [] []
    [(.gotSlot "memcpy", 2, 0)]).withKnownBytes 2 0 8 (.label "memcpy")

/-- After `memcpy`: RSP at the frame's offset 8, region 1 the state RBX points to. -/
def startLoad : SState := init [488, 200] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- The loop head's: RSP at the frame's offset 8, RAX the variable 0, below 26. -/
def startBody : SState := init [488] [(.rsp, .ptr 0 8), (.rax, .var 0)] [] [(.var 0, 26)]

/-- The loop exit's: RSP at the frame's offset 8, region 1 the state, whose address the frame's
offset 184 holds. -/
def startEpi : SState := init [488, 200] [(.rsp, .ptr 0 8)] [] [] [(.load 0 184 8, 1, 0)]

end

sym_block entry := exec Vm.KeccakF.b0 startEntry

sym_block load := exec Vm.KeccakF.b1 startLoad

sym_block body := exec Vm.KeccakF.b2 startBody

sym_block epilogue := exec Vm.KeccakF.b3 startEpi

end NativeRustcVmX64.KeccakF
