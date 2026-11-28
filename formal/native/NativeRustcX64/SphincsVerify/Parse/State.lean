module

public import NativeRustcX64.SphincsVerify.Frame

/-!
# The parse's symbolic states (x86-64)

- `fS k b`: region 0 the frame with the return address (`21632`, RSP its base), region 1 the 16
  bytes below it, regions 2 and 3 the memcpy and memset GOT slots, the registers `k` known.
- `entryS`: at `b0`, with region 4 the 32-byte public key (`RDI` its base, `RSP` `21624`).
- `fSig k`: `fS` plus region 4 the 7740-byte raw signature (`RBX` its base).
- `openS`: at `b1`, with region 4 the 176-byte FORS opening (`RBX + R12` aliased at `+160`).
- `sigTurnS i off`: a chain-value copy loop's turn (`b7`, `b15`, `b23`), copying 32 bytes from
  `RBX + i + off` (region 0) to `RSP + i + 12780` (region 1).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustcX64.Sym

@[expose] public section

/-- The symbolic frame state: RSP the frame's base, the registers `k`, the bounds `b`, the slots
below the frame aliased, and the memcpy and memset GOT slots seeded in regions 2 and 3. -/
def fS (k : List (Reg64 × Sym)) (b : List (Sym × Nat) := []) : SState :=
  Run.frameState k [] b

/-- At `b0` (entry): frame + below + GOT slots + 32-byte public key at region 4 (`RDI`). -/
def entryS : SState :=
  ((init [21632, 16, 8, 8, 32] [(.rsp, .ptr 0 21624), (.rdi, .ptr 4 0)] [] []
    (Run.frameAliases ++ [(.gotSlot "memcpy", 2, 0), (.gotSlot "memset", 3, 0)])).withKnownBytes
      2 0 8 (.label "memcpy")).withKnownBytes 3 0 8 (.label "memset")

/-- The frame state plus region 4 the 7740-byte raw signature (`RBX` its base). -/
def fSig (k : List (Reg64 × Sym)) : SState :=
  ((init [21632, 16, 8, 8, 7740] ((.rsp, .ptr 0 0) :: (.rbx, .ptr 4 0) :: k) [] []
    (Run.frameAliases ++ [(.gotSlot "memcpy", 2, 0), (.gotSlot "memset", 3, 0)])).withKnownBytes
      2 0 8 (.label "memcpy")).withKnownBytes 3 0 8 (.label "memset")

/-- At `b1` (FORS opening turn): frame + below + GOT + 176-byte opening at region 4,
`RBX + R12` aliased to offset `160` in region 4. -/
def openS : SState :=
  ((init [21632, 16, 8, 8, 176]
    [(.rsp, .ptr 0 0), (.r15, .ptr 0 576), (.r14, .ptr 0 12780), (.r13, .ptr 0 560),
      (.rbp, .label "memcpy")] [] []
    (Run.frameAliases ++ [(.gotSlot "memcpy", 2, 0), (.gotSlot "memset", 3, 0),
      (.bin .add .W64 (.reg .rbx) (.reg .r12), 4, 160)])).withKnownBytes
      2 0 8 (.label "memcpy")).withKnownBytes 3 0 8 (.label "memset")

/-- A layer chain-value copy turn (`b7`, `b15`, `b23`): 32 bytes from `RBX + i + off` (region 0)
to `RSP + i + 12780` (region 1). -/
def sigTurnS (i : Reg64) (off : Nat) : SState :=
  init [32, 32] [] [] []
    [(.bin .add .W64 (.reg .rbx) (.reg i), 0, -(off : Int)),
     (.bin .add .W64 (.reg .rsp) (.reg i), 1, -12780)]

end

end NativeRustcX64.SphincsVerifyProof.Parse
