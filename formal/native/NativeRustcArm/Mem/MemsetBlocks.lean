module

public import NativeRustcArm.Mem.Common
meta import NativeRustcArm.Mem.Common
public import NativeRustcArm.Code.Common.Memset
meta import NativeRustcArm.Code.Common.Memset

/-!
# `memset`'s blocks, run by the symbolic executor

Each block of `NativeRustcArm.Common.Memset` from the symbolic state its proof starts it in: the
blocks without memory accesses from `init [] .sp`; the word loop's body with the 8 bytes it writes
(at `x0 + x9`) as a region reached by an alias; the byte loop's body with the byte it writes (at
`x8`) as a region.
-/

namespace NativeRustcArm.Mem.Memset

open NativeRustcArm.Sym NativeRustcArm.Mem NativeRustcArm.Common.Memset

@[expose] public section

set_option Elab.async false

/-- No regions, every register its atom. -/
def sNone : SState := init [] .sp

/-- The word loop's head: the 8 bytes at `x0 + x9` (region 0). -/
def sWord : SState := init [(8, false)] .sp [] [] [] [(idx .X0 .X9, (0, 0))]

/-- The byte loop's head: the byte at `x8` (region 0). -/
def sByte : SState := init [(1, false)] .sp [(.X8, .ptr 0 0)]

sym_block e0 := exec b0 sNone
sym_block e1 := exec b1 sNone
sym_block e2 := exec b2 sNone
sym_block e3 := exec b3 sByte
sym_block e4 := exec b4 sNone
sym_block e5 := exec b5 sNone
sym_block e6 := exec b6 sNone
sym_block e7 := exec b7 sWord
sym_block e8 := exec b8 sNone

end

end NativeRustcArm.Mem.Memset
