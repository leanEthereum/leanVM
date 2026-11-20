/-
  Rv64mc.Proof.Layout.Gpow

  `gpow` keeps its contract (`Spec.Layout.Gpow.spec`) from `E::pow`'s: a tail call, `Model.limbs_gpowRust` its
  value.
-/

import Rv64mc.Spec.Layout.Gpow
import Rv64mc.Spec.Field.EPow
import Rv64mc.Model.Extra.Layout
import Rv64mc.Gen.Tmpl.Verifier.Layout.Gpow
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.Gpow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout.Gpow
open Rv64mc.Gen.Verifier.Layout.Gpow (Link tmpl)

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (hpow : Spec.Field.EPow.spec env p L.pow.idx need) : spec env p i need := by
  rv_auto hp with [hL] using [hpow]
  all_goals rw [Model.limbs_gpowRust]

end Rv64mc.Proof.Layout.Gpow
