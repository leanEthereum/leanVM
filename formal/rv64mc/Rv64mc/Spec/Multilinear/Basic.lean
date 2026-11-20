/-
  Rv64mc.Spec.Multilinear.Basic

  What the multilinear contracts that return a `Vec<E>` share: the header at `sret` (`a0`) holds the mirror's
  elements (`VecAt EListAt`) in a block the call allocated (`Fresh`), or an empty buffer (capacity `0`, whose pointer
  is the alignment, not an allocation). The slot is what the call writes besides its allocations
  (`Spec.Whir.SretOut`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Field

namespace Rv64mc.Spec.Multilinear

open RiscvZkvm.Rv64 LeanVM.Parameters

/-- **A fresh `Vec<E>` of `xs` at `a`**, allocated between `m` and `m'`. -/
def FreshVecE (env : Env) (m m' : MachineState) (a : Word) (xs : List E) : Prop :=
  ∃ ptr cap, VecAt EListAt m' a ptr cap (xs.map Model.limbs) ∧
    (cap = 0 ∨ env.Fresh m m' ptr (Layouts.E.byteSize * cap))

end Rv64mc.Spec.Multilinear
