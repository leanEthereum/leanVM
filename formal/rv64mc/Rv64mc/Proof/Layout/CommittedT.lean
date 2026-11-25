/-
  Rv64mc.Proof.Layout.CommittedT

  `Layout::committed` is total: `Committed.Post`'s placement (`Spec.Layout.Committed`), over any program holding its
  template. A safety contract by `rv_autoT` (`safe`) and the partial proof (`Committed.lean`) combined by
  `HoldsT.of_holds_post`. It reads one element of the placements' slice and writes the result's slot, so the
  precondition (`PreT`) adds that the slice, unless empty, and the slot lie in windows, 8-byte aligned.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `safe`, `total`
-/

import Rv64mc.Proof.Layout.Committed
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Core.HoldsTOfHolds
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Layout.CommittedT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Committed
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.WinT
open Rv64mc.Gen.Verifier.Layout.Layout.Committed (Link tmpl)

/-- The total precondition: `Pre`, the slice unless empty and the result's slot in windows, 8-byte aligned. -/
def PreT (env : Env) (ps : List (Option Model.PlacementRust)) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env ps regs m ∧
    ((regs .x12).toNat = 0 ∨ (InWin env (regs .x11) (24 * (regs .x12).toNat) ∧ (regs .x11).toNat % 8 = 0)) ∧
    InWin env (regs .x10) Layouts.ResultPlacement.byteSize ∧ (regs .x10).toNat % 8 = 0

/-- **The total contract of `Layout::committed`**: `Committed.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ps, HoldsT env p i need (PreT env ps) (Post ps) Out

/-- Element `x` of a slice of 24-byte elements from `q`, as the code addresses it, as a number. -/
theorem elem_toNat24 {q x : Word} (h : q.toNat + 24 * x.toNat < 2 ^ 64) :
    (q + (x <<< 4 + x <<< 3)).toNat = q.toNat + 24 * x.toNat := by
  rw [Committed.elem_addr, toNat_add_ofNat h]

set_option rv_sym.heap true in
/-- **`Layout::committed` is safe and returns**, from `PreT`. -/
theorem safe (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat)
    (ps : List (Option Model.PlacementRust)) :
    HoldsT env p i need (PreT env ps) (fun _ _ _ _ => True) (fun _ _ _ => True) := by
  rv_autoT hp
  all_goals
    simp only [Layouts.ResultPlacement.byteSize] at hpre_10 hpre_12
    have hW : InWin env (regs .x10) 24 := hpre_12
    have n0 : regs .x10 ≠ env.nextAddr := hW.ne_next (Nat.le_refl _) (by omega)
    have n8 : regs .x10 + 8#64 ≠ env.nextAddr :=
      hW.ne_next (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)
    have n16 : regs .x10 + 16#64 ≠ env.nextAddr :=
      hW.ne_next (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)
  all_goals try ((repeat' apply frame_true_setMem) <;> first | exact frame_true rfl hpre_5 | assumption)
  all_goals
    simp only [Layouts.OptionPlacement.byteSize] at hpre_7
    have hlt : (regs .x13).toNat < ps.length := by
      first
        | (rw [BitVec.lt_def, BitVec.toNat_ofNat] at hc; omega)
        | (rw [BitVec.lt_def, BitVec.toNat_ofNat] at hc_1; omega)
    have hn : (regs .x12).toNat = ps.length := by rw [hpre_6, BitVec.toNat_ofNat]; omega
    obtain ⟨hS, hSa⟩ := hpre_11.resolve_left (by omega)
    have hx := elem_toNat24 (q := regs .x11) (x := regs .x13) (by unfold InWin at hS; omega)
    have hd0 := hS.dword hpre_15 hSa hx (by omega) (by omega)
    have hd8 := hS.dword hpre_15 hSa ((toNat_add_ofNat (k := 8) (by rw [hx]; unfold InWin at hS; omega)).trans
      ((congrArg (· + 8) hx).trans (Nat.add_assoc _ _ _))) (by omega) (by omega)
    have hd16 := hS.dword hpre_15 hSa ((toNat_add_ofNat (k := 16) (by rw [hx]; unfold InWin at hS; omega)).trans
      ((congrArg (· + 16) hx).trans (Nat.add_assoc _ _ _))) (by omega) (by omega)
  · exact hd0.1
  · exact hd0.2
  · exact hd8.1
  · exact hd8.2
  · exact hd16.1
  · exact hd16.2

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) :
    specT env p i 0 := fun ps =>
  (safe env p i L hp 0 ps).of_holds_post (Committed.ok env p i L hp ps) fun _ _ h => h.1

end Rv64mc.Proof.Layout.CommittedT

/-- info: 'Rv64mc.Proof.Layout.CommittedT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.CommittedT.total
