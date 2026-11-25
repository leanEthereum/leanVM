/-
  Rv64mc.Proof.Transcript.FinishT

  `Transcript::finish` is total: `Finish.Post`'s verdict (`Spec.Transcript.Finish`), over any program holding its
  template. A safety contract by `rv_autoT` (`safe`) and the partial proof (`Finish.lean`) combined by
  `HoldsT.of_holds_post`. It loads the transcript's proof reference and offsets and the proof's two lengths, so the
  precondition (`PreT`) adds that the transcript and the proof lie in windows, 8-byte aligned.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `safe`, `total`
-/

import Rv64mc.Proof.Transcript.Finish
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Core.HoldsTOfHolds
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Transcript.FinishT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.Finish
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Transcript.Transcript.Finish (Link tmpl)

/-- The total precondition: `Pre`, and the transcript and the proof it reads in windows, 8-byte aligned. -/
def PreT (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env t regs m ∧ InWin env (regs .x10) Layouts.Transcript.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    InWin env (m.getMem (regs .x10 + 0x148#64)) Layouts.Proof.byteSize ∧
    (m.getMem (regs .x10 + 0x148#64)).toNat % 8 = 0

/-- **The total contract of `Transcript::finish`**: `Finish.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, HoldsT env p i need (PreT env t) (Post t)

/-- **`Transcript::finish` is safe and returns**, from `PreT`. -/
theorem safe (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat)
    (t : Model.TState) :
    HoldsT env p i need (PreT env t) (fun _ _ _ _ => True) (fun _ _ _ => True) := by
  rv_autoT hp

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (need : Nat) : specT env p i need := fun t =>
  (safe env p i L hp need t).of_holds_post (Finish.ok env p i L hp hL t) fun _ _ h => h.1

end Rv64mc.Proof.Transcript.FinishT

/-- info: 'Rv64mc.Proof.Transcript.FinishT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.FinishT.total
