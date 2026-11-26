/-
  Rv64mc.Proof.Layout.ConstantT

  `constant` is total: `Spec.Layout.Constant`'s postcondition, or the run ends with the guest's abort (`AbortStop`)
  where `Form::term` does. From `Form::term`'s total contract (`TermT`): the empty monomial on its stack, `term`'s
  region starting at `NEXT` at entry. The partial proof (`Constant.lean`) ported by `rv_autoT`. The precondition
  adds that the result's slot lies in a window, 8-byte aligned, which `term`'s `TermWin` asks of it.

  ## Main definitions

  * `SretWin`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.Constant
import Rv64mc.Proof.Layout.TermT

namespace Rv64mc.Proof.Layout.ConstantT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Constant
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Layout.Constant (Link tmpl)

/-- The result's slot (`a0`) in a window, 8-byte aligned. -/
def SretWin (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  InWin env (regs .x10) Layouts.Form.byteSize ∧ (regs .x10).toNat % 8 = 0

/-- **The total contract of `constant`**: `Spec.Layout.Constant.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ value, HoldsT env p i need (fun regs m => Pre env value regs m ∧ SretWin env regs m)
    (Post env (Model.constantRust value)) Term.Out AbortStop

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hterm : TermT.specT env p L.term.idx) : specT env p i := by
  intro value
  rv_autoT hp with [hL] using [hterm [] value (env.next m) 8#64 0]

end Rv64mc.Proof.Layout.ConstantT

/-- info: 'Rv64mc.Proof.Layout.ConstantT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.ConstantT.total
