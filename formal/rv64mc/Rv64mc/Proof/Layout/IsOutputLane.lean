/-
  Rv64mc.Proof.Layout.IsOutputLane

  `is_output_lane` keeps its contract (`Spec.Layout.IsOutputLane.spec`): one unsigned comparison of `column - 106`
  with `25`, `KECCAK`'s output lanes being the global columns `106..131`.
-/

import Rv64mc.Spec.Layout.IsOutputLane
import Rv64mc.Model.Extra.Layout
import Rv64mc.Gen.Tmpl.Verifier.Layout.IsOutputLane
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.IsOutputLane

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout Rv64mc.Spec.Layout.IsOutputLane
open Rv64mc.Gen.Verifier.Layout.IsOutputLane (Link tmpl)

theorem ult_eval (c : Word) :
    BinOp.ult.eval (c + 18446744073709551510#64) 25#64 = ofBool (Model.isOutputLaneRust c.toNat) := by
  have hc := c.isLt
  have e : BitVec.ult (c + 18446744073709551510#64) 25#64 = decide (106 ≤ c.toNat ∧ c.toNat < 131) := by
    rw [BitVec.ult, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    by_cases h : 106 ≤ c.toNat ∧ c.toNat < 131 <;> simp only [h, decide_false] <;> simp <;> omega
  simp only [BinOp.eval, ofBool, e, Model.isOutputLaneRust_closed]

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) :
    spec env p i := by
  rv_auto hp
  exact ult_eval _

end Rv64mc.Proof.Layout.IsOutputLane
