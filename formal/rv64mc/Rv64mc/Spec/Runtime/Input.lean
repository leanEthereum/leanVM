/-
  Rv64mc.Spec.Runtime.Input

  The contract of the guest's `Input::word` (`guest/src/main.rs`): the reader at `a0` (`Input`, a slice of the
  input words) gives its first word in `a0` and moves past it; on an empty slice it halts (`halt(2)`), which the
  contract, partial, leaves out. The reader lives in a caller's frame, at or above the stack's limit.
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- Where the reader at `a` keeps its slice's pointer and length. -/
def inputPtrAt (a : Word) : Word := a + BitVec.ofNat 64 (Layouts.Input.f0 + Layouts.SliceE.ptr)
def inputLenAt (a : Word) : Word := a + BitVec.ofNat 64 (Layouts.Input.f0 + Layouts.SliceE.len)

/-- `Input::word`'s precondition: the reader lies in a caller's frame. -/
def WordPre (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  env.stackLimit.toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + Layouts.Input.byteSize < 2 ^ 64

/-- `Input::word`'s postcondition: the slice was not empty, its first word is returned, and the reader holds the
    rest. -/
def WordPost (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  let q := m.getMem (inputPtrAt (regs .x10))
  let l := m.getMem (inputLenAt (regs .x10))
  l ≠ 0 ∧ r' .x10 = m.getMem q ∧ m'.getMem (inputPtrAt (regs .x10)) = q + 8 ∧
    m'.getMem (inputLenAt (regs .x10)) = l - 1

/-- `Input::word` writes the reader. -/
def WordOut (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  b = inputPtrAt (regs .x10) ∨ b = inputLenAt (regs .x10)

/-- **The contract of `Input::word`.** -/
def InputWordSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (WordPre env) WordPost WordOut

/-! ## `Input::digest(sret, self)` -/

/-- `Input::digest`'s precondition: the reader (at `a1`) and the 32-byte result (at `a0`) lie in a caller's frame,
    apart, and the four words the reader gives lie below the stack. -/
def DigestPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.stackLimit.toNat ≤ (regs .x11).toNat ∧ (regs .x11).toNat + Layouts.Input.byteSize < 2 ^ 64 ∧
    (regs .x2).toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + Layouts.Digest.byteSize < 2 ^ 64 ∧
    (∀ b, InRange (regs .x11) Layouts.Input.byteSize b →
      ¬ InRange (alignToDword (regs .x10)) (Layouts.Digest.byteSize + (regs .x10).toNat % 8) b) ∧
    (m.getMem (inputPtrAt (regs .x11))).toNat + 32 ≤ env.stackLimit.toNat

/-- `Input::digest`'s postcondition: the reader held at least four words; byte `k` of the result is byte `k % 8`
    of word `k / 8` (little-endian); the reader holds the rest; no other byte changed. -/
def DigestPost (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  let q := m.getMem (inputPtrAt (regs .x11))
  let l := m.getMem (inputLenAt (regs .x11))
  4 ≤ l.toNat ∧
    (∀ k, k < Layouts.Digest.byteSize → m'.getByte (regs .x10 + BitVec.ofNat 64 k) =
      extractByte (m.getMem (q + BitVec.ofNat 64 (8 * (k / 8)))) (k % 8)) ∧
    m'.getMem (inputPtrAt (regs .x11)) = q + 32#64 ∧ m'.getMem (inputLenAt (regs .x11)) = l - 4#64 ∧
    ∀ b, ¬ InRange (regs .x10) Layouts.Digest.byteSize b → ¬ InRange (regs .x11) Layouts.Input.byteSize b →
      m'.getByte b = m.getByte b

/-- `Input::digest` writes the result's doublewords and the reader. -/
def DigestOut (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (alignToDword (regs .x10)) (Layouts.Digest.byteSize + (regs .x10).toNat % 8) b ∨
    b = inputPtrAt (regs .x11) ∨ b = inputLenAt (regs .x11)

/-- **The contract of `Input::digest`.** -/
def InputDigestSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (DigestPre env) DigestPost DigestOut

end Rv64mc.Spec.Runtime
