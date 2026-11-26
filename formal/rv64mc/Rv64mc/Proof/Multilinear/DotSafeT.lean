/-
  Rv64mc.Proof.Multilinear.DotSafeT

  `dot`'s safety (`dotSafe`): `DotOwnT.specT` at the elements its slices' bytes hold, so a caller that only needs
  `dot` to return, not its value, states no elements. Callers whose slices are built in their own frames from values
  they do not track (`verify_bus_balance::{closure#2}`) use it.

  ## Main definitions

  * `elemsAt`, `PreS`

  ## Main results

  * `preT_of_preS`, `dotSafe`
-/

import Rv64mc.Proof.Multilinear.DotOwnT
import Rv64mc.Model.Extra.Transcript

namespace Rv64mc.Proof.Multilinear.DotSafeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Runtime.MemsetT (InWin)

/-- The `n` elements at `a` in `m`. -/
def elemsAt (m : MachineState) (a : Word) (n : Nat) : List E :=
  List.ofFn (n := n) fun j => Model.ofLimbsW (m.getMem (a + BitVec.ofNat 64 (16 * j.1)),
    m.getMem (a + BitVec.ofNat 64 (16 * j.1) + 8#64))

/-- `DotOwnT.PreT` without the elements: slices of one length `a1 = a3`, each owned by the caller, and, unless
    empty, in a window and 8-byte aligned. -/
def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  regs .x13 = regs .x11 ∧ env.Owned m (regs .x2) (regs .x10) (16 * (regs .x11).toNat) ∧
    env.Owned m (regs .x2) (regs .x12) (16 * (regs .x11).toNat) ∧
    ((regs .x11).toNat = 0 ∨ (InWin env (regs .x10) (16 * (regs .x11).toNat) ∧ (regs .x10).toNat % 8 = 0 ∧
      InWin env (regs .x12) (16 * (regs .x11).toNat) ∧ (regs .x12).toNat % 8 = 0))

theorem elemsAt_length (m : MachineState) (a : Word) (n : Nat) : (elemsAt m a n).length = n := by
  simp [elemsAt]

/-- The elements at `a` are there. -/
theorem sliceArgs_elemsAt {m : MachineState} {a len : Word} (h : a.toNat + 16 * len.toNat < 2 ^ 64) :
    SliceArgs EListAt m a len ((elemsAt m a len.toNat).map Model.limbs) := by
  refine ⟨by simp [elemsAt], ?_, fun k hk => ?_⟩
  · simpa [elemsAt, Layouts.E.byteSize] using h
  · simp [elemsAt, EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize, Model.limbs_ofLimbsW]

theorem preT_of_preS {env : Env} {regs : Reg → Word} {m : MachineState} (h : PreS env regs m) :
    DotOwnT.PreT env (elemsAt m (regs .x10) (regs .x11).toNat) (elemsAt m (regs .x12) (regs .x11).toNat) regs m := by
  obtain ⟨h13, hox, hoy, hw⟩ := h
  refine ⟨sliceArgs_elemsAt hox.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h13]; exact sliceArgs_elemsAt hoy.2
  · simpa [elemsAt_length, Layouts.E.byteSize] using hox
  · simpa [elemsAt_length, Layouts.E.byteSize] using hoy
  · rw [elemsAt_length]; exact hw.imp id fun h => ⟨h.1, h.2.1⟩
  · rw [elemsAt_length]; exact hw.imp id fun h => ⟨h.2.2.1, h.2.2.2⟩

/-- **`dot`'s safety**: from `PreS` it returns, writing nothing outside its stack, or ends the run with `a0 = 2`. -/
theorem dotSafe {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : DotOwnT.specT env p i need) :
    HoldsT env p i need (PreS env) (fun _ _ _ _ => True) (Stop := AbortStop) :=
  fun Q ret top rest regs m ⟨⟨he, hs, hst, hn, hP, hal⟩, hW⟩ hstop hk =>
    h _ _ Q ret top rest regs m ⟨⟨he, hs, hst, hn, preT_of_preS hP, hal⟩, hW⟩ hstop
      fun r' m' ⟨⟨ha', hf, hs', _⟩, hc⟩ => hk r' m' ⟨⟨ha', hf, hs', trivial⟩, hc⟩

end Rv64mc.Proof.Multilinear.DotSafeT

/-- info: 'Rv64mc.Proof.Multilinear.DotSafeT.dotSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.DotSafeT.dotSafe
