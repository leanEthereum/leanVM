module

public import NativeRustcVm.Mem
public import NativeVm.Entry

/-!
# `leanvm_verify`'s caller, arch-independent

What `leanvm_verify(ctx)` needs of its caller beyond `NativeVm.Entry.EntryPre`, on the byte memory:
the checks it makes (`Aligned`: the decoded and the working areas nonzero and 8-aligned, the
bytecode 8-aligned when nonempty, the wire nonzero when nonempty; rustc's slices require them), and
the caller's areas (`entryRegions`: the context, the wire, the bytecode, the decoded and the
working areas, in bytes) apart from the verifier's stack and read-only data (`ApartFrom`).

The working area as the crate uses it: `WORK_WORDS = 61944` words (`workAreaWords`), `Work`'s or
`DecodeWork`'s, in turn; `NativeVm.Entry.workWords n`, which `EntryPre` provides, is at least that.
-/

namespace NativeRustcVm.Top

open NativeVm NativeVm.Entry
open NativeVm.Transcript (ctxEnd)

@[expose] public section

/-- `WORK_WORDS`: the working area's words the crate uses (`size_of::<Work>() / 8`). -/
def workAreaWords : Nat := 61944

/-- The working area's bytes the crate uses (`size_of::<Work>()`). -/
def workAreaBytes : Nat := 8 * workAreaWords

/-- The caller's areas in bytes: the context's `ctxEnd` words, the wire's `wireWords L`, the
bytecode's `n`, the decoded area's `decodedWords L`, the working area's `workWords n`. -/
def entryRegions (ctx : UInt64) (a : Areas) (L n : Nat) : List Region :=
  [⟨ctx.toBitVec, 8 * ctxEnd⟩, ⟨a.wire.toBitVec, 8 * wireWords L⟩, ⟨a.bytecode.toBitVec, 8 * n⟩,
    ⟨a.decoded.toBitVec, 8 * decodedWords L⟩, ⟨a.work.toBitVec, 8 * workWords n⟩]

/-- Every region of positive size is apart from the `n` bytes from `b`. -/
def ApartFrom (rs : List Region) (b : BitVec 64) (n : Nat) : Prop :=
  ∀ r ∈ rs, 0 < r.size → Apart r.addr r.size b n

/-- **The alignment `leanvm_verify` checks**: the decoded and the working areas nonzero and
8-aligned, the bytecode 8-aligned (and nonzero) when nonempty, the wire nonzero when nonempty. -/
structure Aligned (a : Areas) (L n : Nat) : Prop where
  dec : a.decoded ≠ 0 ∧ a.decoded.toNat % 8 = 0
  work : a.work ≠ 0 ∧ a.work.toNat % 8 = 0
  bytecode : 0 < n → a.bytecode ≠ 0 ∧ a.bytecode.toNat % 8 = 0
  wire : 0 < L → a.wire ≠ 0

theorem workAreaWords_le (n : Nat) : workAreaWords ≤ workWords n := by
  unfold workWords
  rw [dataEnd_val]
  unfold workAreaWords
  omega

end

end NativeRustcVm.Top
