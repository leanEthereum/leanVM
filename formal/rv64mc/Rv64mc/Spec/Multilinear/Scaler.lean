/-
  Rv64mc.Spec.Multilinear.Scaler

  `Scaler` in memory (`ScalerAt`), and the contracts of `Scaler::new(r, uses)` and `Scaler::mul(&self, value)`.
  `Scaler` is `Table(Scaled)` or `Plain(E)`, 24 bytes: `Plain` is the niche `usize::MAX` in the first word (the
  `Vec`'s capacity, below `2^63` for a `Table`) and `r`'s limbs in the next two; a `Table` is the `Scaled`'s `Vec<E>`
  header. The enum's layout is not among `Gen/Layouts.lean`'s (`-Zprint-type-sizes` does not print it): these are
  the offsets the code reads.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Multilinear

namespace Rv64mc.Spec.Multilinear.Scaler

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The bytes of a `Scaler`. -/
abbrev byteSize : Nat := 24

/-- **The `Scaler` at `a` is `s`.** -/
def ScalerAt (env : Env) (m : MachineState) (a : Word) : Model.Scaler → Prop
  | .plain r => m.getMem a = 0xffffffffffffffff#64 ∧ m.getMem (a + 8#64) = (Model.limbs r).1 ∧
      m.getMem (a + 16#64) = (Model.limbs r).2
  | .table tabs => ∃ ptr cap, VecAt EListAt m a ptr cap tabs ∧ env.Live m ptr (Layouts.E.byteSize * tabs.length)

/-! ## `Scaler::new(r, uses)` -/

/-- The result's slot is the caller's; `r`'s limbs in `a1`, `a2`, `uses` in `a3`. -/
def NewPre (env : Env) (r : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) byteSize ∧ regs .x11 = (Model.limbs r).1 ∧ regs .x12 = (Model.limbs r).2

def NewPost (env : Env) (r : E) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  ScalerAt env m' (regs .x10) (Model.Scaler.new r (regs .x13).toNat)

/-- What `new` writes besides its allocation: the result. -/
def NewOut (regs : Reg → Word) (_m : MachineState) : Word → Prop := InRange (regs .x10) byteSize

/-- **The contract of `Scaler::new`**, function `i` of `p` with `need` bytes of stack (no frame; it tail-calls
    `Scaled::new`), for every `r`. -/
def newSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ r, Holds env p i need (NewPre env r) (NewPost env r) NewOut

/-! ## `Scaler::mul(&self, value)` -/

def MulPre (env : Env) (s : Model.Scaler) (v : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  ScalerAt env m (regs .x10) s ∧ regs .x11 = (Model.limbs v).1 ∧ regs .x12 = (Model.limbs v).2

def MulPost (s : Model.Scaler) (v : E) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word)
    (_m' : MachineState) : Prop :=
  r' .x10 = (Model.limbs (s.mul v)).1 ∧ r' .x11 = (Model.limbs (s.mul v)).2

/-- **The contract of `Scaler::mul`**, function `i` of `p` with `need` bytes of stack (no frame; it tail-calls
    `Scaled::mul` or `E::mul`), for every scaler and value. -/
def mulSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ s v, Holds env p i need (MulPre env s v) (MulPost s v)

end Rv64mc.Spec.Multilinear.Scaler
