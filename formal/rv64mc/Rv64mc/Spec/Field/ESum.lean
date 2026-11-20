/-
  Rv64mc.Spec.Field.ESum

  The contract of `E::sum` over a slice's elements copied (`E::sum(xs.iter().copied())`): the iterator passed as its
  two pointers, the first element's in `a0` and the end's in `a1`, the elements' limbs in the heap (`EListAt`,
  `Live`); the sum's limbs, `Model.eSum`'s, in `a0`, `a1`. A leaf without a frame.
-/

import Rv64mc.Core.Repr
import Rv64mc.Spec.Field.Basic

namespace Rv64mc.Spec.Field.ESumCopied

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (env : Env) (es : List Model.Limbs) (regs : Reg → Word) (m : MachineState) : Prop :=
  EListAt m (regs .x10) es ∧ regs .x11 = regs .x10 + BitVec.ofNat 64 (16 * es.length) ∧
    env.Live m (regs .x10) (Layouts.E.byteSize * es.length)

def Post (es : List Model.Limbs) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  r' .x10 = (Model.eSum es).1 ∧ r' .x11 = (Model.eSum es).2

/-- **The contract of `E::sum` over a copied slice iterator**, function `i` of `p` with `need` bytes of stack (it
    has no frame), for every slice. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ es, Holds env p i need (Pre env es) (Post es)

end Rv64mc.Spec.Field.ESumCopied
