/-
  Rv64mc.Proof.Field.SpreadT

  `spread` is total: it returns `Spread.Post`'s value (`Spec.Field.Spread`), over any program holding its template.
  A leaf with no memory access; `rv_autoT` leaves the two words, as `rv_auto` does for `Spread.lean`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Spec.Field.Spread
import Rv64mc.Model.Extra.Field
import Rv64mc.Gen.Tmpl.Verifier.Field.Spread
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Field.SpreadT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field

/-- **The total contract of `spread`**: `Spread.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) Spread.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Verifier.Field.Spread.Link)
    (hp : p[i]? = some (Gen.Verifier.Field.Spread.tmpl L)) (need : Nat) : specT env p i need := by
  rv_autoT hp
  · exact (Model.lo128_spread _).symm
  · exact (Model.hi128_spread _).symm

end Rv64mc.Proof.Field.SpreadT

/-- info: 'Rv64mc.Proof.Field.SpreadT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.SpreadT.total
