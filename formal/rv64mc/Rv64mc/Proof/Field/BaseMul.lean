/-
  Rv64mc.Proof.Field.BaseMul

  `base_mul` keeps its contract (`Spec.Field.BaseMul.spec`), over any program holding its template, from its
  callees' contracts: `clmul`, then a tail call of `reduce` on its two words.
-/

import Rv64mc.Spec.Field.BaseMul
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.BaseMul
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.BaseMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.BaseMul (Link tmpl)

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needR : Nat} (hnC : 16 + needC ≤ need) (hnR : needR ≤ need)
    (hcl : Clmul.spec env p L.clmul.idx needC) (hrd : Reduce.spec env p L.reduce.idx needR) :
    BaseMul.spec env p i need := by
  rv_auto hp with [hL] using [hcl, hrd]
  · exact Nat.le_trans (Nat.add_le_add_left hnR _) hpre_3
  · simp only [Model.baseMul, append_hi_lo]

end Rv64mc.Proof.Field.BaseMul
