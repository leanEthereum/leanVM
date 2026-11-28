module

public import NativeRustcX64.Sym
public import NativeRustcX64.Mem.Common
public import NativeRustcVmX64.Code.Vm.IvWord
public meta import NativeRustcVmX64.Code.Vm.IvWord
public meta import NativeRustcX64.Mem.Common

/-!
# `iv_word`'s blocks, run by the symbolic executor (x86-64)

`iv_word` uses no stack but its return address. Its blocks without memory access run from `start`
(no region); the two loads from the bytecode run with region 0 the word they read, through the
address RDI plus 8 RDX (`addrX`, the `k`th word's): `loadTop` (`b3`, the top byte of word `k - 2`,
16 bytes below) and `loadWord` (`b7`, word `k - 1`, 8 bytes below); the two returns run from
`sRet`, region 0 the return address at RSP (`tag`, `b5`, and `ret8`, `b8`).
-/

namespace NativeRustcVmX64.IvWordRun

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem Vm.IvWord

set_option Elab.async false

@[expose] public section

/-- No region. -/
def start : SState := init []

/-- RDI plus 8 RDX: the address of word RDX of the bytecode at RDI. -/
def addrX : Sym := .bin .add .W64 (.reg .rdi) (.bin .mul .W64 (.reg .rdx) (.lit 8))

/-- Region 0 the word 16 bytes below `addrX`. -/
def startTop : SState := init [8] [] [] [] [(addrX, 0, 16)]

/-- Region 0 the word 8 bytes below `addrX`. -/
def startWord : SState := init [8] [] [] [] [(addrX, 0, 8)]

end

sym_block zero := exec b0 start
sym_block one := exec b1 start
sym_block two := exec b2 start
sym_block loadTop := exec b3 startTop
sym_block jmp4 := exec b4 start
sym_block tag := exec b5 sRet
sym_block first := exec b6 start
sym_block loadWord := exec b7 startWord
sym_block ret8 := exec b8 sRet
sym_block none9 := exec b9 start
sym_block jmp10 := exec b10 start

end NativeRustcVmX64.IvWordRun
