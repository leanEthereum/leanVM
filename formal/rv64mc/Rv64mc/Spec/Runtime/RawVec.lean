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

/-! ## `finish_grow(out, cap, ptr, new_cap, align, size)` -/

/-- Where `finish_grow`'s result at `out` keeps its tag and its block's pointer
    (`Result<NonNull<[u8]>, TryReserveError>`, `Layouts.ResultBlockTryReserve`). -/
def fgTagAt (out : Word) : Word := out + BitVec.ofNat 64 Layouts.ResultBlockTryReserve.tagOffset
def fgPtrAt (out : Word) : Word :=
  out + BitVec.ofNat 64 (Layouts.ResultBlockTryReserve.Ok.f0 + Layouts.SliceE.ptr)

/-- `finish_grow`'s precondition: the result slot is the caller's, the alignment a `Layout`'s, the new capacity
    nonzero and not below the old, the old block allocated (or empty) and within `isize`. -/
def FinishGrowPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.ResultBlockTryReserve.byteSize ∧
    0 < (regs .x14).toNat ∧ (regs .x14).toNat < 2 ^ 63 ∧ (regs .x11).toNat ≤ (regs .x13).toNat ∧
    0 < (regs .x13).toNat * (regs .x15).toNat ∧
    ((regs .x11).toNat = 0 ∨ env.Live m (regs .x12) ((regs .x11).toNat * (regs .x15).toNat)) ∧
    (regs .x11).toNat * (regs .x15).toNat < 2 ^ 63

/-- `finish_grow`'s postcondition: on `Ok`, a fresh block of `new_cap * size` bytes holding the old block's
    `cap * size` bytes first; on `Err`, a payload word below `2^63` (an alignment, or zero for an overflow). -/
def FinishGrowPost (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  (m'.getMem (fgTagAt (regs .x10)) = BitVec.ofNat 64 Layouts.ResultBlockTryReserve.Ok.tag →
    env.Fresh m m' (m'.getMem (fgPtrAt (regs .x10))) ((regs .x13).toNat * (regs .x15).toNat) ∧
    ∀ k, k < (regs .x11).toNat * (regs .x15).toNat →
      m'.getByte (m'.getMem (fgPtrAt (regs .x10)) + BitVec.ofNat 64 k) = m.getByte (regs .x12 + BitVec.ofNat 64 k)) ∧
  (m'.getMem (fgTagAt (regs .x10)) ≠ BitVec.ofNat 64 Layouts.ResultBlockTryReserve.Ok.tag →
    (m'.getMem (fgPtrAt (regs .x10))).toNat < 2 ^ 63)

/-- What `finish_grow` writes: its result. -/
def FinishGrowOut (regs : Reg → Word) (_m : MachineState) : Word → Prop :=
  InRange (regs .x10) Layouts.ResultBlockTryReserve.byteSize

/-- **The contract of `finish_grow`.** -/
def FinishGrowSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (FinishGrowPre env) (FinishGrowPost env) FinishGrowOut

/-! ## `do_reserve_and_handle(self, len, additional, align, size)` -/

/-- **The contract of `RawVecInner::reserve::do_reserve_and_handle`**: `grow_amortized`'s arguments; it returns
    only when the buffer grew (else `handle_error`). -/
def DoReserveSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun regs m => GrowPre env (regs .x13).toNat (regs .x14).toNat regs m)
    (fun regs m _ m' => Grown env m m' (regs .x10) ((regs .x11).toNat + (regs .x12).toNat) (regs .x14).toNat)
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
