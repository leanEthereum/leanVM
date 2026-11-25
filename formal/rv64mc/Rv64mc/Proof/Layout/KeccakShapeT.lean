/-
  Rv64mc.Proof.Layout.KeccakShapeT

  `keccak_shape` is total: `Spec.Layout.KeccakShape`'s postcondition for every slice of heights, or the run ends
  with the guest's abort (`AbortStop`) on a slice shorter than six, from `panic_bounds_check`'s `Aborts`. The
  partial proof (`KeccakShape.lean`) ported by `rv_autoT`. The precondition adds that the slice, unless empty, lies
  in a window and is 8-byte aligned.

  ## Main definitions

  * `SliceWin`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.KeccakShape
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Layout.KeccakShapeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout.KeccakShape Rv64mc.Proof.Layout.KeccakShape
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Layout.KeccakShape (Link tmpl)

/-- The slice of words `(a0, a1)`, unless empty, in a window and 8-byte aligned. -/
def SliceWin (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  (regs .x11).toNat = 0 ∨ (InWin env (regs .x10) (8 * (regs .x11).toNat) ∧ (regs .x10).toNat % 8 = 0)

/-- **The total contract of `keccak_shape`**, for every slice of heights. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ hs, HoldsT env p i need (fun regs m => Pre hs regs m ∧ SliceWin env regs m) (Post hs) (Stop := AbortStop)

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need : Nat} (hpanic : Aborts env p L.panicBoundsCheck.idx need) : specT env p i need := by
  intro hs
  rv_autoT hp with [hL] using [hpanic]
  exact load_heights hpre_7 hc

end Rv64mc.Proof.Layout.KeccakShapeT

/-- info: 'Rv64mc.Proof.Layout.KeccakShapeT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.KeccakShapeT.total
