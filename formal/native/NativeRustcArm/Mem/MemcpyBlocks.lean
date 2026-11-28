module

public import NativeRustcArm.Mem.Common
meta import NativeRustcArm.Mem.Common
public import NativeRustcArm.Code.Common.Memcpy
meta import NativeRustcArm.Code.Common.Memcpy

/-!
# `memcpy`'s blocks, run by the symbolic executor

Each block of `NativeRustcArm.Common.Memcpy` from the symbolic state its proof starts it in: the
blocks without memory accesses from `init [] .sp`; the word loop's body with the 8 bytes it reads
(at `x1 + x8`) and writes (at `x0 + x8`) as regions reached by aliases; the byte loop's body with the
byte it reads (at `x1`) and writes (at `x8`) as regions.
-/

namespace NativeRustcArm.Mem.Memcpy

open NativeRustcArm.Sym NativeRustcArm.Mem NativeRustcArm.Common.Memcpy

@[expose] public section

set_option Elab.async false

/-- No regions, every register its atom. -/
def sNone : SState := init [] .sp

/-- The word loop's head: the 8 bytes at `x0 + x8` (region 0) and at `x1 + x8` (region 1). -/
def sWord : SState :=
  init [(8, false), (8, false)] .sp [] [] [] [(idx .X0 .X8, (0, 0)), (idx .X1 .X8, (1, 0))]

/-- The byte loop's head: the byte at `x8` (region 0) and at `x1` (region 1). -/
def sByte : SState := init [(1, false), (1, false)] .sp [(.X8, .ptr 0 0), (.X1, .ptr 1 0)]

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

end NativeRustcArm.Mem.Memcpy
