/-
  Rv64mc.Proof.Field.Slice

  An `E` slice in the heap read through a frame without `out` (`Tactic.F`): element `j`'s limbs at the addresses
  `rv_sym` computes for them, `p + 16 j` and `p + 16 j + 8`.
-/

import Rv64mc.Core.Repr
import Rv64mc.Tactic.Frame

namespace Rv64mc

open RiscvZkvm.Rv64

theorem EListAt.load {env : Env} {top : Word} {m M : MachineState} {p : Word} {es : List (Word × Word)} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (h : EListAt m p es)
    (hl : env.Live m p (Layouts.E.byteSize * es.length)) (hj : j < es.length) :
    M.getMem (p + BitVec.ofNat 64 (16 * j)) = es[j].1 ∧ M.getMem (p + BitVec.ofNat 64 (16 * j) + 8#64) = es[j].2 := by
  have h' := (h.keep (Env.Frame.keeps_live hf hnx hl fun _ _ h => h)).2 j hj
  simpa [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize] using h'

end Rv64mc
