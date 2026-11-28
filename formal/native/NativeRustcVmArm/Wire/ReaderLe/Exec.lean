module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.ReaderLe
public meta import NativeRustcVmArm.Code.Vm.ReaderLe

/-!
# `Reader::le`'s blocks, run by the symbolic executor

- `failS`: region 0 the reader (X0); the read does not fit: `b0`, `b1`.
- `okS n` (`n` is `4` or `8`): region 0 the reader, region 1 the `n` bytes read (from the bytes'
  address plus the cursor, the alias of `ldr`'s address plus the cursor); `b0`, `b2`, then `b3` for
  `n = 4`, `b4`, `b6`, `b8`, `b10` for `n = 8`.
-/

namespace NativeRustcVmArm.Wire.ReaderLe

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReaderLe

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- The read does not fit. -/
def failS : SState := init [(24, false)] .sp [(.X0, .ptr 0 0)]

/-- The read of `n` bytes fits: the reader and the bytes read. -/
def okS (n : Nat) : SState :=
  init [(24, false), (n, false)] .sp [(.X0, .ptr 0 0), (.X1, .lit n)] [] []
    [(.bin .add .W64 (.load 0 0 8) (.load 0 16 8), 1, 0)]

end

set_option Elab.async false

sym_block run_f0 := exec b0 failS
sym_block run_f1 := exec b1 (after b0 failS)
sym_block run_a0 := exec b0 (okS 4)
sym_block run_a2 := exec b2 (after b0 (okS 4))
sym_block run_a3 := exec b3 (after b2 (after b0 (okS 4)))
sym_block run_b0 := exec b0 (okS 8)
sym_block run_b2 := exec b2 (after b0 (okS 8))
sym_block run_b4 := exec b4 (after b2 (after b0 (okS 8)))
sym_block run_b6 := exec b6 (after b4 (after b2 (after b0 (okS 8))))
sym_block run_b8 := exec b8 (after b6 (after b4 (after b2 (after b0 (okS 8)))))
sym_block run_b10 := exec b10 (after b8 (after b6 (after b4 (after b2 (after b0 (okS 8))))))

end NativeRustcVmArm.Wire.ReaderLe
