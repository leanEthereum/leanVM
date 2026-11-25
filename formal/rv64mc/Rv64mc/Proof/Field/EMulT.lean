/-
  Rv64mc.Proof.Field.EMulT

  `E::mul` is total: it returns `EMul.Post`'s product (`Spec.Field.EMul`), over any program holding its template,
  from the total contracts of `clmul` (`ClmulT`) and `reduce` (`ReduceT`). The partial proof (`EMul.lean`) ported by
  `rv_autoT`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Field.EMul
import Rv64mc.Proof.Field.ClmulT
import Rv64mc.Proof.Field.ReduceT

namespace Rv64mc.Proof.Field.EMulT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.E.AsMul.Mul (Link tmpl)

/-- **The total contract of `E::mul`**: `EMul.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) EMul.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needR : Nat} (hnC : 80 + needC ≤ need) (hnR : 80 + needR ≤ need)
    (hcl : ClmulT.specT env p L.clmul.idx needC) (hrd : ReduceT.specT env p L.reduce.idx needR) :
    specT env p i need := by
  rv_autoT hp with [hL] using [hcl, hrd]
  all_goals simp only [Model.eMul, ← hi128_xor, ← lo128_xor, ← hi128_shl1, ← lo128_shl1]
  all_goals simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, append_hi_lo]

end Rv64mc.Proof.Field.EMulT

/-- info: 'Rv64mc.Proof.Field.EMulT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.EMulT.total
