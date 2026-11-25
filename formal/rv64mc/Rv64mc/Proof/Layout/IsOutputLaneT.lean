/-
  Rv64mc.Proof.Layout.IsOutputLaneT

  `is_output_lane` is total: it returns `IsOutputLane.Post`'s test (`Spec.Layout.IsOutputLane`), over any program
  holding its template. A leaf with no memory access: the partial proof (`IsOutputLane.lean`) ported by `rv_autoT`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.IsOutputLane
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Layout.IsOutputLaneT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout Rv64mc.Proof.Layout.IsOutputLane
open Rv64mc.Gen.Verifier.Layout.IsOutputLane (Link tmpl)

/-- **The total contract of `is_output_lane`**: `IsOutputLane.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) IsOutputLane.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    specT env p i need := by
  rv_autoT hp
  exact ult_eval _

end Rv64mc.Proof.Layout.IsOutputLaneT

/-- info: 'Rv64mc.Proof.Layout.IsOutputLaneT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.IsOutputLaneT.total
