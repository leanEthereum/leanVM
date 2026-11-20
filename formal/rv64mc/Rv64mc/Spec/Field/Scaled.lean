/-
  Rv64mc.Spec.Field.Scaled

  The contracts of `Scaled::new(r)` and `Scaled::mul(&self, a)` (`Scaled(Vec<E>)`, the tables of the product by a
  fixed `r`). `new` writes at `sret` (`a0`) a `Vec<E>` header (`VecAt`) of `Model.scaledNewE r`'s tables (`r`'s limbs
  in `a1`, `a2`), in a `Fresh` block. `mul` takes the tables as a slice (pointer `a0`, length `a1`; every lookup is
  bounds-checked against it, a failed check does not return) and `a`'s limbs in `a2`, `a3`, and returns
  `Model.scaledMul`'s limbs in `a0`, `a1`. `Model.scaledMulE_eq` makes the pair the product by `r`.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Field

namespace Rv64mc.Spec.Field.Scaled

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-! ## `Scaled::new(r)` -/

/-- The result's slot is the caller's. -/
def NewPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize

/-- The tables of `r = (a1, a2)` in a fresh block, under the header at `sret`. -/
def NewPost (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  ∃ ptr cap, VecAt EListAt m' (regs .x10) ptr cap (Model.scaledNew (regs .x11, regs .x12)) ∧
    env.Fresh m m' ptr (Layouts.E.byteSize * cap)

/-- What `new` writes besides its allocation: the header. -/
def NewOut (regs : Reg → Word) (_m : MachineState) : Word → Prop := InRange (regs .x10) Layouts.Vec.byteSize

/-- **The contract of `Scaled::new`**, function `i` of `p` with `need` bytes of stack. -/
def newSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (NewPre env) (NewPost env) NewOut

/-! ## `Scaled::mul(&self, a)` -/

/-- The tables as a slice in the heap. -/
def MulPre (env : Env) (tabs : List Model.Limbs) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) tabs ∧ env.Live m (regs .x10) (Layouts.E.byteSize * tabs.length)

def MulPost (tabs : List Model.Limbs) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  r' .x10 = (Model.scaledMul tabs (regs .x12, regs .x13)).1 ∧ r' .x11 = (Model.scaledMul tabs (regs .x12, regs .x13)).2

/-- **The contract of `Scaled::mul`**, function `i` of `p` with `need` bytes of stack, for every table. -/
def mulSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ tabs, Holds env p i need (MulPre env tabs) (MulPost tabs)

end Rv64mc.Spec.Field.Scaled
