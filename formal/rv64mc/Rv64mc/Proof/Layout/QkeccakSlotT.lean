/-
  Rv64mc.Proof.Layout.QkeccakSlotT

  `qkeccak_slot` is total: it returns `QkeccakSlot.Post`'s slot (`Spec.Layout.QkeccakSlot`), over any program holding
  its template. A leaf with no memory access: the partial proof (`QkeccakSlot.lean`) ported by `rv_autoT`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.QkeccakSlot
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Layout.QkeccakSlotT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout Rv64mc.Proof.Layout.QkeccakSlot
open Rv64mc.Gen.Verifier.Layout.QkeccakSlot (Link tmpl)

/-- **The total contract of `qkeccak_slot`**: `QkeccakSlot.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) QkeccakSlot.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    specT env p i need := by
  rv_autoT hp
  · exact spare hc_1 hc
  · exact lane hc
  · exact none_lt hc

end Rv64mc.Proof.Layout.QkeccakSlotT

/-- info: 'Rv64mc.Proof.Layout.QkeccakSlotT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.QkeccakSlotT.total
