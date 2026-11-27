/-
  Rv64mc.Proof.Field.BaseMulT

  `base_mul` is total: it returns `BaseMul.Post`'s product (`Spec.Field.BaseMul`), over any program holding its
  template, from the total contracts of `clmul` (`ClmulT`) and `reduce` (`ReduceT`, a tail call). The partial proof
  (`BaseMul.lean`) ported by `rv_autoT`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Field.BaseMul
import Rv64mc.Proof.Field.ClmulT
import Rv64mc.Proof.Field.ReduceT

namespace Rv64mc.Proof.Field.BaseMulT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.BaseMul (Link tmpl)

/-- **The total contract of `base_mul`**: `BaseMul.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) BaseMul.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needR : Nat} (hnC : 16 + needC ≤ need) (hnR : needR ≤ need)
    (hcl : ClmulT.specT env p L.clmul.idx needC) (hrd : ReduceT.specT env p L.reduce.idx needR) :
    specT env p i need := by
  rv_autoT hp with [hL] using [hcl, hrd]
  · exact Nat.le_trans (Nat.add_le_add_left hnR _) hpre_3
  · simp only [Model.baseMul, append_hi_lo]

end Rv64mc.Proof.Field.BaseMulT

/-- info: 'Rv64mc.Proof.Field.BaseMulT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.BaseMulT.total
