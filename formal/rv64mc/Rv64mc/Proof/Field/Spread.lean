/-
  Rv64mc.Proof.Field.Spread

  `spread` keeps its contract (`Spec.Field.Spread.spec`), over any program holding its template: each
  word is `Model.Extra.Field`'s form of `spread`'s.
-/

import Rv64mc.Spec.Field.Spread
import Rv64mc.Model.Extra.Field
import Rv64mc.Gen.Tmpl.Verifier.Field.Spread
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.Spread

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Verifier.Field.Spread.Link)
    (hp : p[i]? = some (Gen.Verifier.Field.Spread.tmpl L)) (need : Nat) : Spread.spec env p i need := by
  rv_auto hp
  · exact (Model.lo128_spread _).symm
  · exact (Model.hi128_spread _).symm

end Rv64mc.Proof.Field.Spread
