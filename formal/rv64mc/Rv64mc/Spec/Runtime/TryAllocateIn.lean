/-
  Rv64mc.Spec.Runtime.TryAllocateIn

  The contract of `RawVecInner::try_allocate_in(capacity, init, alloc, elem_layout)` as the image has it: the
  result `Result<RawVecInner, TryReserveError>` written at `sret` (`a0`), the capacity in `a1`, `init` in `a2`
  (zero: uninitialized, else zeroed), the element's alignment and size in `a3`, `a4`. On `Ok` (tag `0`) the buffer
  is empty (capacity `0`) when it holds no bytes, and otherwise a `Fresh` block of `capacity * size` bytes, zeroed
  when asked; on `Err` it promises nothing (its callers hand the error to `handle_error`, which does not return).

  The result's layout is not among `Gen/Layouts.lean`'s (`-Zprint-type-sizes` does not print it): a tag word, then
  the `RawVecInner` (`Layouts.RawVecInner`) at `tryAllocInner`, as the code stores it.
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The bytes of `Result<RawVecInner, TryReserveError>`, and where its `Ok`'s `RawVecInner` starts. -/
abbrev tryAllocBytes : Nat := 24
abbrev tryAllocInner : Nat := 8

def taTagAt (a : Word) : Word := a
def taCapAt (a : Word) : Word := a + BitVec.ofNat 64 (tryAllocInner + Layouts.RawVecInner.cap)
def taPtrAt (a : Word) : Word := a + BitVec.ofNat 64 (tryAllocInner + Layouts.RawVecInner.ptr)

/-- `try_allocate_in`'s precondition: the result slot is the caller's, the alignment a `Layout`'s. -/
def TryAllocPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) tryAllocBytes ∧ 0 < (regs .x13).toNat ∧ (regs .x13).toNat < 2 ^ 63

/-- `try_allocate_in`'s postcondition: on `Ok`, an empty buffer for no bytes, else a fresh block of the capacity
    asked for, zeroed when `init` is nonzero. -/
def TryAllocPost (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  m'.getMem (taTagAt (regs .x10)) = 0#64 →
    ((regs .x11).toNat * (regs .x14).toNat = 0 ∧ m'.getMem (taCapAt (regs .x10)) = 0#64) ∨
    ((regs .x11).toNat * (regs .x14).toNat ≠ 0 ∧ m'.getMem (taCapAt (regs .x10)) = regs .x11 ∧
      env.Fresh m m' (m'.getMem (taPtrAt (regs .x10))) ((regs .x11).toNat * (regs .x14).toNat) ∧
      (regs .x12 ≠ 0#64 → ∀ k, k < (regs .x11).toNat * (regs .x14).toNat →
        m'.getByte (m'.getMem (taPtrAt (regs .x10)) + BitVec.ofNat 64 k) = 0#8))

/-- What `try_allocate_in` writes: its result. -/
def TryAllocOut (regs : Reg → Word) (_m : MachineState) : Word → Prop := InRange (regs .x10) tryAllocBytes

/-- **The contract of `try_allocate_in`.** -/
def TryAllocSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (TryAllocPre env) (TryAllocPost env) TryAllocOut

end Rv64mc.Spec.Runtime
