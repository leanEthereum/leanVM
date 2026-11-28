module

public import NativeRustcX64.Sym

/-!
# The frame's symbolic state

`frameS k`: the frame with the return address and the stack arguments (region 0, 2784 bytes from
the base), the 8 bytes below it where a call pushes its return address (region 1, reached by the
alias `ptr 0 (-8)`), the `memcpy`/`memset` GOT slots (regions 2/3), RSP the base,
and the registers `k` known. GOT contents are seeded separately from writes.
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustcX64.Sym

@[expose] public section

/-- The frame (region 0), call return slot (region 1), and resolved GOT slots (regions 2/3).
RSP is the base; `extra` regions start at 4. `k`, bounds, and aliases add block-specific facts. -/
def frameS (k : List (Reg64 × Sym)) (extra : List Nat := []) (bounds : List (Sym × Nat) := [])
    (aliases : List (Sym × Nat × Int) := []) : SState :=
  ((init (2784 :: 8 :: 8 :: 8 :: extra) ((.rsp, .ptr 0 0) :: k) [] bounds
    ((.ptr 0 (-8), (1, 0)) :: (.gotSlot "memcpy", 2, 0) ::
      (.gotSlot "memset", 3, 0) :: aliases)).withKnownBytes 2 0 8 (.label "memcpy")).withKnownBytes
    3 0 8 (.label "memset")

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

end

end NativeRustcX64.WotsLeafProof
