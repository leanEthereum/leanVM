module

public import NativeRustcX64.Sym
public import NativeRustcX64.Mem.Common
public import NativeRustcVmX64.Code.Vm.ReaderLe
public meta import NativeRustcVmX64.Code.Vm.ReaderLe
public meta import NativeRustcX64.Sym
public meta import NativeRustcX64.Mem.Common

/-!
# `Reader::le`'s blocks, run by the symbolic executor (x86-64)

- `failS`: region 0 the reader (RDI); the read does not fit: `b0` (a carry), or `b0`, `b1`.
- `okS n` (`n` is `4` or `8`, in RSI): region 0 the reader, region 1 the `n` bytes read (the
  bytes' address plus the cursor, `cursorSym`, an alias, RSI plus it another); `b0`, `b1`, `b2`,
  then `b3` to `b6` for `n = 8`.
- `sRet`: the final `retq` (`b7`), region 0 the return address.
-/

namespace NativeRustcVmX64.Wire.ReaderLe

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVmX64.Vm.ReaderLe

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- The read does not fit. -/
def failS : SState := init [24] [(.rdi, .ptr 0 0)]

/-- The bytes' address plus the cursor, as `b2` computes it. -/
def cursorSym : Sym := .bin .add .W64 (.load 0 0 8) (.load 0 16 8)

/-- The read of `n` bytes fits: the reader and the bytes read. -/
def okS (n : Nat) : SState :=
  init [24, n] [(.rdi, .ptr 0 0), (.rsi, .lit n)] [] []
    [(.bin .add .W64 (.lit n) cursorSym, 1, n), (cursorSym, 1, 0)]

end

set_option Elab.async false

sym_block run_f0 := exec b0 failS
sym_block run_f1 := exec b1 (after b0 failS)
sym_block run_a0 := exec b0 (okS 4)
sym_block run_a1 := exec b1 (after b0 (okS 4))
sym_block run_a2 := exec b2 (after b1 (after b0 (okS 4)))
sym_block run_b0 := exec b0 (okS 8)
sym_block run_b1 := exec b1 (after b0 (okS 8))
sym_block run_b2 := exec b2 (after b1 (after b0 (okS 8)))
sym_block run_b3 := exec b3 (after b2 (after b1 (after b0 (okS 8))))
sym_block run_b4 := exec b4 (after b3 (after b2 (after b1 (after b0 (okS 8)))))
sym_block run_b5 := exec b5 (after b4 (after b3 (after b2 (after b1 (after b0 (okS 8))))))
sym_block run_b6 :=
  exec b6 (after b5 (after b4 (after b3 (after b2 (after b1 (after b0 (okS 8)))))))
sym_block run_ret := exec b7 sRet

end NativeRustcVmX64.Wire.ReaderLe
