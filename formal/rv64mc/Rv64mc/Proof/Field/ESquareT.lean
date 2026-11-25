/-
  Rv64mc.Proof.Field.ESquareT

  `E::square` is total: it returns `ESquare.Post`'s limbs (`Spec.Field.ESquare`), over any program holding its
  template, from its callees' total contracts (`SpreadT`, `ReduceT`). `rv_autoT` closes what totality adds to
  `ESquare.lean`'s proof: its frame's stores and loads in the stack window and aligned, no code under the stores,
  `Windows` at each call and the code map kept; what is left is the value, closed as there.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Spec.Field.ESquare
import Rv64mc.Proof.Field.U128
import Rv64mc.Proof.Field.ReduceT
import Rv64mc.Proof.Field.SpreadT
import Rv64mc.Gen.Tmpl.Verifier.Field.E.Square

namespace Rv64mc.Proof.Field.ESquareT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.E.Square (Link tmpl)

/-- **The total contract of `E::square`**: `ESquare.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) ESquare.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS needR : Nat} (hnS : 48 + needS ≤ need) (hnR : 48 + needR ≤ need)
    (hsp : SpreadT.specT env p L.spread.idx needS) (hrd : ReduceT.specT env p L.reduce.idx needR) :
    specT env p i need := by
  rv_autoT hp with [hL] using [hsp, hrd]
  all_goals simp only [Model.eSquare, ← hi128_xor, ← lo128_xor, ← hi128_shl1, ← lo128_shl1, append_hi_lo,
    BitVec.xor_comm]

end Rv64mc.Proof.Field.ESquareT

/-- info: 'Rv64mc.Proof.Field.ESquareT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESquareT.total
