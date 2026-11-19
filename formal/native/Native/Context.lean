module

public import Native.QM
public import Native.Keccak

/-!
# A verifier's context

A verifier takes one argument, in `rdi`: a context of `ctxWords` 64-bit words, 8-byte aligned,
which holds its input and all its working memory:

| bytes from `rdi` | holds |
|---|---|
| `[0, 672)` | `Keccak.hash`'s scratch area (`Keccak.scratchWords` words) |
| `[704, 752)` | the callee-saved registers `rbx`, `rbp`, `r12`, `r13`, `r14`, `r15`, in that order |
| `[1024, 9216)` | the input: the public key, the message and the signature (`inputOff`) |
| `[9216, 25600)` | the verifier's own working memory (`workOff`) |

It returns `1` in `rax` when the signature verifies and `0` when it does not, and preserves the
callee-saved registers.
-/

@[expose] public section

namespace Native.Context

/-- The save area. -/
def saveOff : Int64 := 704
/-- The input area. -/
def inputOff : Nat := 1024
/-- The working area. -/
def workOff : Nat := 9216
/-- The context's words. -/
def ctxWords : Nat := 3200

/-- The callee-saved registers, in the save area's order. -/
def calleeSaved : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The context at `base`: aligned, inside the address space, every word in memory. -/
structure At (mem : UInt64 → Option UInt64) (base : UInt64) : Prop where
  aligned : base.toNat % 8 = 0
  fits : base.toNat + 8 * ctxWords ≤ 2 ^ 64
  words : ∀ k < ctxWords, (mem (base + (8 * k).toUInt64)).isSome

/-- The input area holds the words `input i`, `i < n`. -/
def InputAt (mem : UInt64 → Option UInt64) (base : UInt64) (n : Nat) (input : Nat → UInt64) :
    Prop :=
  ∀ i < n, mem (base + (inputOff + 8 * i).toUInt64) = some (input i)

end Native.Context
