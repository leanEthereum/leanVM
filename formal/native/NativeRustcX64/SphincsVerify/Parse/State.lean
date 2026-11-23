module

public import NativeRustcX64.SphincsVerify.Frame

/-!
# The parse's symbolic states (x86-64)

`fS k b`: region 0 the frame with the return address (RSP its base), region 1 the 16 bytes below
it (the slots `call` writes, aliased), the registers `k` known, the bounds `b`; `fS3 k`: the input
as region 2 too; `turnS`: a word loop's turn, its source and destination aliased into regions 0
and 1.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustcX64.Sym

@[expose] public section

/-- The symbolic frame state: RSP the frame's base, the registers `k`, the bounds `b`, the slots
below the frame aliased, and the memcpy and memset GOT slots seeded in regions 2 and 3. -/
def fS (k : List (Reg64 × Sym)) (b : List (Sym × Nat) := []) : SState :=
  Run.frameState k [] b

/-- The symbolic frame state with the input at region 2 and GOT slots at regions 3 and 4. -/
def fS3 (k : List (Reg64 × Sym)) : SState :=
  init [29408, 16, 7816, 8, 8] ((.rsp, .ptr 0 0) :: k) [] [] Run.frameAliases

/-- A word loop's turn: the source `RBX + i + so` and the destination `RSP + i + d0` aliased into
regions 0 and 1, `i` the counter. -/
def turnS (i : Reg64) (n : Nat) (so d0 : Int) : SState :=
  init [n, n] [] [] [] [(.bin .add .W64 (.reg .rbx) (.reg i), 0, so), (.bin .add .W64 (.reg .rsp) (.reg i), 1, d0)]

/-- A frame copy loop's turn: region 0 the frame's bytes from the source to the destination,
`RSP + i` aliased `d0` into it, `i` the counter. -/
def spanS (i : Reg64) (n : Nat) (d0 : Int) : SState :=
  init [n] [] [] [] [(.bin .add .W64 (.reg .rsp) (.reg i), 0, d0)]

/-- `b3`, `b5`, `b7`: the frame and the input, RBX the context. -/
abbrev ctxS : SState := fS3 [(.rbx, .ptr 2 (-1024))]

end

end NativeRustcX64.SphincsVerifyProof.Parse
