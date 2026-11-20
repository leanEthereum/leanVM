/-
  Rv64mc.Proof.Field.ESquare

  `E::square` keeps its contract (`Spec.Field.ESquare.spec`), over any program holding its template, from its
  callees' contracts: each limb spread, the two products folded by `reduce`.
-/

import Rv64mc.Spec.Field.ESquare
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.E.Square
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.ESquare

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.E.Square (Link tmpl)

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needR : Nat} (hnS : 48 + needS ≤ need) (hnR : 48 + needR ≤ need)
    (hsp : Spread.spec env p L.spread.idx needS) (hrd : Reduce.spec env p L.reduce.idx needR) :
    ESquare.spec env p i need := by
  rv_auto hp with [hL] using [hsp, hrd]
  all_goals simp only [Model.eSquare, ← hi128_xor, ← lo128_xor, ← hi128_shl1, ← lo128_shl1, append_hi_lo,
    BitVec.xor_comm]

end Rv64mc.Proof.Field.ESquare
