/-
  Rv64mc.Proof.Layout.ConstantAlT

  `constant`'s second total contract (`specT`), beside `ConstantT.specT`: `Spec.Layout.Constant`'s postcondition and
  the result's buffers 8-byte aligned (`TermAlT.FormAl`), so that the result is a `FormT` (`TermAlT.formT_of`). The
  proof is `ConstantT.total`'s over `Form::term`'s second contract (`TermAlT`): the empty monomial on its stack has
  capacity `0`, so `TermAlT.PreA`'s alignment holds.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.ConstantT
import Rv64mc.Proof.Layout.TermAlT

namespace Rv64mc.Proof.Layout.ConstantAlT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Constant
open Rv64mc.Proof.Layout.ConstantT (SretWin)
open Rv64mc.Proof.Layout.TermAlT (FormAl)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Verifier.Layout.Constant (Link tmpl)

/-- **`constant`'s second total contract**: `Constant.Post` and the result's buffers aligned. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ value, HoldsT env p i need (fun regs m => Pre env value regs m ∧ SretWin env regs m)
    (fun regs m r' m' => Post env (Model.constantRust value) regs m r' m' ∧ FormAl m' (regs .x10)) Term.Out
    AbortStop

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hterm : TermAlT.specT env p L.term.idx) : specT env p i := by
  intro value
  rv_autoT hp with [hL] using [hterm [] value (env.next m) 8#64 0]
  · simpa only [vecCap_eq, vecPtr_eq] using hret1_17
  · simpa only [vecCap_eq, vecPtr_eq, vecLen_eq] using hret1_18

end Rv64mc.Proof.Layout.ConstantAlT

/-- info: 'Rv64mc.Proof.Layout.ConstantAlT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.ConstantAlT.total
