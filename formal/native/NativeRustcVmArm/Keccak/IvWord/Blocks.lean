module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.IvWord
public meta import NativeRustcVmArm.Code.Vm.IvWord
public meta import NativeRustcArm.Sym

/-!
# `iv_word`'s blocks, run by the symbolic executor

`iv_word` uses no stack. Its blocks without memory access run from `start` (no region); the two
loads from the bytecode run with region 0 the word they read: `loadTop` (`b3`, the top byte of
word `k - 2`, at X0 plus X8 words) and `loadWord` (`b7`, word `k - 1`, at X0 plus X9 words).
-/

namespace NativeRustcVmArm.IvWordRun

open NativeRustcArm NativeRustcArm.Sym Vm.IvWord

set_option Elab.async false

@[expose] public section

/-- No region. -/
def start : SState := init []

/-- The address of word X8 of the bytecode at X0. -/
def addrX8 : Sym := .bin .add .W64 (.reg .X0) (.un (.shift .LSL 3) .W64 (.reg .X8))

/-- The address of word X9 of the bytecode at X0. -/
def addrX9 : Sym := .bin .add .W64 (.reg .X0) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X9))

/-- Region 0 the word at X0 plus X8 words. -/
def startTop : SState := init [(8, false)] .sp [] [] [] [(addrX8, 0, 0)]

/-- Region 0 the word at X0 plus X9 words. -/
def startWord : SState := init [(8, false)] .sp [] [] [] [(addrX9, 0, 0)]

end

sym_block zero := exec b0 start
sym_block one := exec b1 start
sym_block two := exec b2 start
sym_block loadTop := exec b3 startTop
sym_block jmp4 := exec b4 start
sym_block tag := exec b5 start
sym_block first := exec b6 start
sym_block loadWord := exec b7 startWord
sym_block ret8 := exec b8 start
sym_block none9 := exec b9 start
sym_block jmp10 := exec b10 start

end NativeRustcVmArm.IvWordRun
