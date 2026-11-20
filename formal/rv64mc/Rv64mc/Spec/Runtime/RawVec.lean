/-
  Rv64mc.Spec.Runtime.RawVec

  The contracts of `RawVecInner::grow_amortized` and of `RawVec<T>::grow_one` (one per `T`, the same code with
  `T`'s alignment and size), on the buffer header `RawVecInner` at `a0` (its capacity and pointer). After a grow
  that succeeds, the header names a block that is `Fresh` (allocated by the call, apart from everything before it),
  of at least the capacity asked for, whose first bytes are the old buffer's (`Grown`). A grow that fails returns
  an error (`grow_amortized`) or never returns (`grow_one`, through `handle_error`).
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The addresses of the capacity and the pointer of the `RawVecInner` at `a`. -/
def rvCapAt (a : Word) : Word := a + BitVec.ofNat 64 Layouts.RawVecInner.cap
def rvPtrAt (a : Word) : Word := a + BitVec.ofNat 64 Layouts.RawVecInner.ptr

/-- **The buffer at `a` grew** from `m` to `m'`, for elements of `size` bytes: its new capacity is at least
    `need`, its new block is fresh, and holds the old block's bytes first. -/
def Grown (env : Env) (m m' : MachineState) (a : Word) (need size : Nat) : Prop :=
  need ≤ (m'.getMem (rvCapAt a)).toNat ∧
    env.Fresh m m' (m'.getMem (rvPtrAt a)) ((m'.getMem (rvCapAt a)).toNat * size) ∧
    ∀ k, k < (m.getMem (rvCapAt a)).toNat * size →
      m'.getByte (m'.getMem (rvPtrAt a) + BitVec.ofNat 64 k) = m.getByte (m.getMem (rvPtrAt a) + BitVec.ofNat 64 k)

/-- What a grow writes: the header. -/
def GrowOut (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  b = rvCapAt (regs .x10) ∨ b = rvPtrAt (regs .x10)

/-- A buffer header the caller owns, for elements of `size` bytes and alignment `align`, its block allocated (or
    empty) and its size within `isize`. -/
def GrowPre (env : Env) (align size : Nat) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.RawVecInner.byteSize ∧ 0 < size ∧ 0 < align ∧ align < 2 ^ 63 ∧
    ((m.getMem (rvCapAt (regs .x10))).toNat = 0 ∨
      env.Live m (m.getMem (rvPtrAt (regs .x10))) ((m.getMem (rvCapAt (regs .x10))).toNat * size)) ∧
    (m.getMem (rvCapAt (regs .x10))).toNat * size < 2 ^ 63

/-! ## `grow_amortized(self, len, additional, align, size)` -/

/-- `grow_amortized`'s postcondition: `Ok` (`a0 = -1`, `Layouts.ResultUnitTryReserve`) only if the buffer grew to
    hold `len + additional`. -/
def GrowAmortizedPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  r' .x10 = BitVec.ofNat 64 Layouts.ResultUnitTryReserve.Ok.tag →
    Grown env m m' (regs .x10) ((regs .x11).toNat + (regs .x12).toNat) (regs .x14).toNat

/-- **The contract of `grow_amortized`.** -/
def GrowAmortizedSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun regs m => GrowPre env (regs .x13).toNat (regs .x14).toNat regs m) (GrowAmortizedPost env)
    GrowOut

/-! ## `grow_one(self)` for elements of `size` bytes aligned to `align` -/

/-- `grow_one`'s postcondition: the buffer grew by at least one element. -/
def GrowOnePost (env : Env) (size : Nat) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  Grown env m m' (regs .x10) ((m.getMem (rvCapAt (regs .x10))).toNat + 1) size

/-- **The contract of `RawVec<T>::grow_one`**, `T` of `size` bytes aligned to `align`. -/
def GrowOneSpec (env : Env) (align size : Nat) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (GrowPre env align size) (GrowOnePost env size) GrowOut

end Rv64mc.Spec.Runtime
