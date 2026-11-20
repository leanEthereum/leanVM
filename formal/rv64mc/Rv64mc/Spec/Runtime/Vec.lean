/-
  Rv64mc.Spec.Runtime.Vec

  The contracts of the `Vec` builders the verification path calls, as the image has them. LLVM specializes both
  `from_elem::<E>` and `<Vec<E> as Clone>::clone` on their callers: `from_elem` takes the element's low limb in
  `a1` (every caller's element has `c1 = 0`) and the count in `a2`; `clone` takes the source slice as a pointer
  and a length (`a1`, `a2`) instead of `&Vec`. Each writes the new `Vec` header at `sret` (`a0`), its buffer
  fresh (or dangling when empty).
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- What a builder writes: the header at `sret`. -/
def SretVecOut (regs : Reg → Word) (_m : MachineState) : Word → Prop := InRange (regs .x10) Layouts.Vec.byteSize

/-- A builder's `sret` is a caller's. -/
def SretPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize

/-- **The `Vec<E>` at `sret` holds `xs`**, in a buffer that is new: empty, or fresh. -/
def NewVecE (env : Env) (m m' : MachineState) (sret : Word) (xs : List (Word × Word)) : Prop :=
  ∃ q, VecAt EListAt m' sret q xs.length xs ∧ (xs.length = 0 ∨ env.Fresh m m' q (Layouts.E.byteSize * xs.length))

/-- **The contract of `from_elem::<E>`** (`vec![E::new(c0, 0); n]`). -/
def FromElemESpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (SretPre env)
    (fun regs m _ m' => NewVecE env m m' (regs .x10) (List.replicate (regs .x12).toNat (regs .x11, 0#64)))
    SretVecOut

/-- **The contract of `<Vec<E> as Clone>::clone`** on the source slice `(a1, a2)`: the copy holds the source's
    elements. The source lies below `NEXT` or in a caller's frame (`Owned`), so apart from the new buffer. -/
def CloneESpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need
    (fun regs m => SretPre env regs m ∧ env.Owned m (regs .x2) (regs .x11) (Layouts.E.byteSize * (regs .x12).toNat))
    (fun regs m _ m' => ∀ xs, EListAt m (regs .x11) xs → regs .x12 = BitVec.ofNat 64 xs.length →
      NewVecE env m m' (regs .x10) xs)
    SretVecOut

end Rv64mc.Spec.Runtime
