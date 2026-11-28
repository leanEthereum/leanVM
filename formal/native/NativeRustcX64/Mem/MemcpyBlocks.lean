module

public import NativeRustcX64.Mem.Common
meta import NativeRustcX64.Mem.Common
public import NativeRustcX64.Code.Common.Memcpy
meta import NativeRustcX64.Code.Common.Memcpy

/-!
# `memcpy`'s blocks, run by the symbolic executor

Each block of `NativeRustcX64.Common.Memcpy` from the symbolic state its proof starts it in: the
blocks without memory accesses from `init []`; the byte loop's body with the byte it reads (at
`rsi + rcx`) and writes (at `rax + rcx`) as regions reached by aliases, the word loop's body
likewise with 8 bytes; the `retq` block from `sRet`.
-/

namespace NativeRustcX64.Mem.Memcpy

open NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcX64.Common.Memcpy

@[expose] public section

set_option Elab.async false

/-- No regions, every register its atom. -/
def sNone : SState := init []

/-- The byte loop's head: the byte at `rax + rcx` (region 0) and at `rsi + rcx` (region 1). -/
def sByte : SState := init [1, 1] [] [] [] [(ix .rax .rcx, (0, 0)), (ix .rsi .rcx, (1, 0))]

/-- The word loop's head: the 8 bytes at `rax + rcx` (region 0) and at `rsi + rcx` (region 1). -/
def sWord : SState := init [8, 8] [] [] [] [(ix .rax .rcx, (0, 0)), (ix .rsi .rcx, (1, 0))]

sym_block e0 := exec b0 sNone
sym_block e1 := exec b1 sNone
sym_block e2 := exec b2 sNone
sym_block e3 := exec b3 sByte
sym_block e4 := exec b4 sNone
sym_block e5 := exec b5 sNone
sym_block e6 := exec b6 sNone
sym_block e7 := exec b7 sWord
sym_block e8 := exec b8 sRet

end

end NativeRustcX64.Mem.Memcpy
