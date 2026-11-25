/-
  Rv64mc.Proof.Transcript.NextT

  `Transcript::next` is total: `Next.Post`'s verdict (`Spec.Transcript.Next`), over any program holding its
  template. A safety contract by `rv_autoT` (`safe`) and the partial proof (`Next.lean`) combined by
  `HoldsT.of_holds_post`. It reads the transcript, the proof it points to and the stream's element at the offset, and
  writes the result's slot and the offset, so the precondition (`PreT`) adds that the transcript, the result's slot,
  the proof and, unless empty, the stream's buffer lie in windows, 8-byte aligned.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `safe`, `total`
-/

import Rv64mc.Proof.Transcript.Next
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Core.HoldsTOfHolds
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Transcript.NextT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.Next
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.WinT
open Rv64mc.Gen.Verifier.Transcript.Transcript.Next (Link tmpl)

/-- The stream's buffer of the proof at `q`, unless empty, in a window and 8-byte aligned. -/
def StreamWin (env : Env) (m : MachineState) (q : Word) : Prop :=
  (m.getMem (q + 0x10#64)).toNat = 0 ∨
    (InWin env (m.getMem (q + 8#64)) (16 * (m.getMem (q + 0x10#64)).toNat) ∧ (m.getMem (q + 8#64)).toNat % 8 = 0)

/-- The total precondition: `Pre`, and the transcript, the result's slot, the proof and its stream's buffer in
    windows, 8-byte aligned. -/
def PreT (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env t regs m ∧ InWin env (regs .x11) Layouts.Transcript.byteSize ∧ (regs .x11).toNat % 8 = 0 ∧
    InWin env (regs .x10) Layouts.ResultE.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    InWin env (m.getMem (regs .x11 + 0x148#64)) Layouts.Proof.byteSize ∧
    (m.getMem (regs .x11 + 0x148#64)).toNat % 8 = 0 ∧ StreamWin env m (m.getMem (regs .x11 + 0x148#64))

/-- **The total contract of `Transcript::next`**: `Next.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, HoldsT env p i need (PreT env t) (Post env t) Out

set_option rv_sym.heap true in
/-- **`Transcript::next` is safe and returns**, from `PreT`. -/
theorem safe (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat)
    (t : Model.TState) :
    HoldsT env p i need (PreT env t) (fun _ _ _ _ => True) (fun _ _ _ => True) := by
  rv_autoT hp
  all_goals
    simp only [Layouts.ResultE.byteSize, Layouts.Transcript.byteSize] at hpre_8 hpre_10 hpre_13 hpre_15
    have hW : InWin env (regs .x10) 24 := hpre_15
    have n0 : regs .x10 ≠ env.nextAddr := hW.ne_next (Nat.le_refl _) (by omega)
    have n8 : regs .x10 + 8#64 ≠ env.nextAddr :=
      hW.ne_next (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)
  -- past the stream: `Err` stored
  · exact frame_true_setMem (frame_true_setMem (frame_true rfl hpre_5) n0) n8
  -- within it: the element's two doublewords, then `Ok` and the offset stored
  all_goals
    have hlt : (MachineState.getMem m (regs .x11 + 336#64)).toNat <
        (MachineState.getMem m (MachineState.getMem m (regs .x11 + 328#64) + 16#64)).toNat := by
      rw [BitVec.lt_def] at hc; omega
    obtain ⟨hS, hSa⟩ := hpre_19.resolve_left (by omega)
    have hx := elem_toNat (s := 4) (q := MachineState.getMem m (MachineState.getMem m (regs .x11 + 328#64) + 8#64))
      (o := MachineState.getMem m (regs .x11 + 336#64)) (by unfold InWin at hS; omega)
    have hx8 := (toNat_add_ofNat (k := 8) (by rw [hx]; unfold InWin at hS; omega)).trans
      (congrArg (· + 8) hx)
    have hd0 := hS.dword hpre_21 hSa hx (by omega) (by omega)
    have hd8 := hS.dword hpre_21 hSa (hx8.trans (Nat.add_assoc _ _ _)) (by omega) (by omega)
  · exact hd8.1
  · exact hd8.2
  · exact hd0.1
  · exact hd0.2
  · have hT : InWin env (regs .x11) 360 := hpre_13
    exact frame_true_setMem (frame_true_setMem (frame_true_setMem (frame_true rfl hpre_5)
      (hT.ne_next (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)))
      (hW.ne_next (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega))) n0
      |> fun h => frame_true_setMem h n8

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (need : Nat) : specT env p i need := fun t =>
  (safe env p i L hp need t).of_holds_post (Next.ok env p i L hp hL t) fun _ _ h => h.1

end Rv64mc.Proof.Transcript.NextT

/-- info: 'Rv64mc.Proof.Transcript.NextT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.NextT.total
