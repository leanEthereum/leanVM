/-
  Rv64mc.Proof.Layout.GpowT

  `gpow` is total: `Spec.Layout.Gpow`'s postcondition, from `E::pow`'s total contract (`EPowT`): a tail call,
  `Model.limbs_gpowRust` its value. The partial proof (`Gpow.lean`) ported by `rv_autoT`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.Gpow
import Rv64mc.Proof.Field.EPowT

namespace Rv64mc.Proof.Layout.GpowT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout.Gpow
open Rv64mc.Gen.Verifier.Layout.Gpow (Link tmpl)

/-- **The total contract of `gpow`**: `Gpow.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (hpow : Field.EPowT.specT env p L.pow.idx need) : specT env p i need := by
  rv_autoT hp with [hL] using [hpow]
  all_goals rw [Model.limbs_gpowRust]

end Rv64mc.Proof.Layout.GpowT

/-- info: 'Rv64mc.Proof.Layout.GpowT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.GpowT.total
