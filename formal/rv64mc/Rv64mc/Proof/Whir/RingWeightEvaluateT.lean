/-
  Rv64mc.Proof.Whir.RingWeightEvaluateT

  `RingWeight::evaluate` is total (`specT`): from the weight (`a0`, 48 bytes) in a window and 8-byte aligned, its point
  and its coefficients vectors (`VecT`, the point's buffer from the input and heap window) and `r_prime` (`a1`, `a2`
  elements), unless empty, in a window and 8-byte aligned, it tail-calls `ring_weight` with the point, `r_prime` and
  the coefficients, so it returns writing nothing of its caller's or ends the run with `a0 = 2`. Safety only: the
  partial proof (`RingWeightEvaluate.lean`) rests on `ring_weight`'s partial specification, which has no proof.

  ## Main definitions

  * `PreT`, `specT`, `PreR`

  ## Main results

  * `slice_of_vecT`, `preR_of_preT`, `total`
-/

import Rv64mc.Proof.Whir.RingWeightT
import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Gen.Tmpl.Verifier.RingSwitch.RingWeight.Evaluate

namespace Rv64mc.Proof.Whir.RingWeightEvaluateT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Gen.Verifier.RingSwitch.RingWeight.Evaluate (Link tmpl)

/-- The total precondition: the weight's two vectors (`point` at offset `0`, `coefficients` at `24`) `VecT`, and
    `r_prime`, unless empty, in a window and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  VecT env m (regs .x10) 16 ∧ VecT env m (regs .x10 + 24#64) 16 ∧
    ((regs .x12).toNat = 0 ∨ (InWin env (regs .x11) (16 * (regs .x12).toNat) ∧ (regs .x11).toNat % 8 = 0))

/-- **The total contract of `RingWeight::evaluate`**: `ring_weight`'s. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

/-- A vector's elements as a slice, as the code reads its pointer and length: none, or allocated before, in a window
    and 8-byte aligned. -/
theorem slice_of_vecT {env : Env} {m : MachineState} {a : Word} (h : VecT env m a 16)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    (m.getMem (a + 16#64)).toNat = 0 ∨ (env.Live m (m.getMem (a + 8#64)) (16 * (m.getMem (a + 16#64)).toNat) ∧
      InWin env (m.getMem (a + 8#64)) (16 * (m.getMem (a + 16#64)).toNat) ∧ (m.getMem (a + 8#64)).toNat % 8 = 0) := by
  obtain ⟨-, ⟨-, -, hb, -⟩, hlc⟩ := h
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero] at hlc
  simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero] at hb
  change (m.getMem (a + 16#64)).toNat ≤ (m.getMem a).toNat at hlc
  rcases hb with h0 | ⟨h1, h2, h3⟩
  · exact .inl (by omega)
  · unfold Env.Live at h2
    change (m.getMem (a + 8#64)).toNat + (m.getMem a).toNat * 16 ≤ _ at h2
    refine .inr ⟨by unfold Env.Live; omega, .inl ⟨h1, by omega⟩, h3⟩

/-- The precondition the steps use: the weight's 48 bytes in a window and aligned, its two vectors' elements as
    slices (`slice_of_vecT`), `r_prime` as in `PreT`. -/
def PreR (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 48 ∧ (regs .x10).toNat % 8 = 0 ∧
  ((m.getMem (regs .x10 + 16#64)).toNat = 0 ∨
    (env.Live m (m.getMem (regs .x10 + 8#64)) (16 * (m.getMem (regs .x10 + 16#64)).toNat) ∧
      InWin env (m.getMem (regs .x10 + 8#64)) (16 * (m.getMem (regs .x10 + 16#64)).toNat))) ∧
  ((m.getMem (regs .x10 + 40#64)).toNat = 0 ∨
    (InWin env (m.getMem (regs .x10 + 32#64)) (16 * (m.getMem (regs .x10 + 40#64)).toNat) ∧
      (m.getMem (regs .x10 + 32#64)).toNat % 8 = 0)) ∧
  ((regs .x12).toNat = 0 ∨ (InWin env (regs .x11) (16 * (regs .x12).toNat) ∧ (regs .x11).toNat % 8 = 0))

theorem preR_of_preT {env : Env} {regs : Reg → Word} {m : MachineState}
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (h : PreT env regs m) : PreR env regs m := by
  obtain ⟨h0, h24, hr⟩ := h
  have hw0 : InWin env (regs .x10) 24 := h0.1
  have hw24 : InWin env (regs .x10 + 24#64) 24 := h24.1
  have hl := hw24.lt
  have h24n : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold InWin at hw0 hw24; omega
  have ha := h24.2.1.2.1
  have hs0 := slice_of_vecT h0 hnx
  have hs24 := slice_of_vecT h24 hnx
  rw [BitVec.add_assoc, BitVec.add_assoc] at hs24
  refine ⟨?_, h0.2.1.2.1, hs0.imp id fun h => ⟨h.1, h.2.1⟩, hs24.imp id fun h => ⟨h.2.1, h.2.2⟩, hr⟩
  unfold InWin at hw0 hw24 ⊢
  rw [h24n] at hw24
  have := env.layout
  omega

set_option rv_sym.heap true in
/-- The steps, over `PreR`. -/
theorem total_raw (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR : Nat} (hnR : needR ≤ need) (hrw : RingWeightT.specT env p L.ringWeight.idx needR) :
    HoldsT env p i need (PreR env) (fun _ _ _ _ => True) (Stop := AbortStop) := by
  rv_autoT hp with [hL] using [hrw]

/-- **`RingWeight::evaluate` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR : Nat} (hnR : needR ≤ need) (hrw : RingWeightT.specT env p L.ringWeight.idx needR) :
    specT env p i need :=
  Isa.TContract.mono (total_raw env p i L hp hL hnR hrw)
    (fun _ _ _ _ ⟨⟨h1, h2, h3, h4, hP, h5⟩, hw⟩ => ⟨⟨h1, h2, h3, h4, preR_of_preT h4 hP, h5⟩, hw⟩)
    (fun _ _ _ _ _ _ _ h => h) fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Whir.RingWeightEvaluateT

/-- info: 'Rv64mc.Proof.Whir.RingWeightEvaluateT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.RingWeightEvaluateT.total
