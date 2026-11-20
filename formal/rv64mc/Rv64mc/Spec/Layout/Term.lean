/-
  Rv64mc.Spec.Layout.Term

  The contract of `Form::term(monomial: Vec<usize>, coefficient: E) -> Form`, which the compiled code calls with the
  result's slot (`sret`) in `a0`, the monomial's `Vec` header by reference in `a1` (moved: its buffer becomes the
  term's), and the coefficient's limbs in `a2`, `a3`: it allocates the one-term buffer and writes the `Form` with
  that term at `sret`, every buffer in `[lo, NEXT after)` when the monomial's lies in `[lo, NEXT before)` and
  `sret` outside it.
-/

import Rv64mc.Spec.Layout.Repr
import Rv64mc.Spec.Runtime.Alloc

namespace Rv64mc.Spec.Layout.Term

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- Its frame (48 bytes) and `alloc`'s (none). -/
def need : Nat := 48

def Pre (env : Env) (ms : List Nat) (c : E) (lo q : Word) (cap : Nat) (regs : Reg → Word) (m : MachineState) :
    Prop :=
  VecAt UsizesAt m (regs .x11) q cap ms ∧ BufIn lo (env.next m) q cap 8 ∧ lo.toNat ≤ (env.next m).toNat ∧
    regs .x12 = (Model.limbs c).1 ∧ regs .x13 = (Model.limbs c).2 ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.Vec.byteSize ∧ env.Owned m (regs .x2) (regs .x10) Layouts.Form.byteSize ∧
    Apart lo (env.next m) (regs .x10) Layouts.Form.byteSize

def Post (env : Env) (ms : List Nat) (c : E) (lo : Word) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  FormIn lo (env.next m') m' (regs .x10) ⟨[(ms, c)]⟩

/-- It writes the result's slot. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Form.byteSize b

/-- **The contract of `Form::term`**, function `i` of `p`. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ ms c lo q cap, Holds env p i need (Pre env ms c lo q cap) (Post env ms c lo) Out

end Rv64mc.Spec.Layout.Term
