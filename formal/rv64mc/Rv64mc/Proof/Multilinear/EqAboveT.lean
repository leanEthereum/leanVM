/-
  Rv64mc.Proof.Multilinear.EqAboveT

  `Placement::eq_above` is total: it returns `EqAbove.Post`'s value (`Spec.Multilinear.EqAbove`), or ends the run
  with the guest's abort (`AbortStop`) where `selector_point` or `slice_index_fail` does, over any program holding its
  template, from the total contracts of `selector_point` (`SelectorPointT`), `eq_eval` over owned or empty slices
  (`EqEvalOwnT`) and `slice_index_fail` (`Aborts`). It calls `selector_point` with `point.len() - variables` before
  checking `variables <= point.len()`, then tail-calls `eq_eval` with that vector, empty with a dangling pointer when
  the point has no coordinate above the window, and the point's suffix.

  The precondition (`PreT`) is the partial `Pre` with the point `OwnSlice` (none, or owned by the caller, in a window,
  aligned) in place of `Live`: `verify_bus_balance` passes a vector's elements, `StackWeight::evaluate` its argument.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.SelectorPointT
import Rv64mc.Proof.Multilinear.EqEvalOwnT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Spec.Multilinear.EqAbove
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.Placement.EqAbove

namespace Rv64mc.Proof.Multilinear.EqAboveT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Multilinear.EqAbove
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Multilinear.OwnSliceT (OwnSlice)
open Rv64mc.Gen.Verifier.Multilinear.Placement.EqAbove (Link tmpl)

/-- The total precondition: the point's elements (`SliceArgs`), the point none or owned by the caller, in a window
    and 8-byte aligned (`OwnSlice`). -/
def PreT (env : Env) (pt : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x12) (regs .x13) (pt.map Model.limbs) ∧ OwnSlice env m (regs .x2) (regs .x12) pt.length

/-- **The total contract of `Placement::eq_above`**: `EqAbove.Post`, from `PreT`, or the guest's abort. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ pt, HoldsT env p i need (PreT env pt) (Post pt) (Stop := AbortStop)

/-- The selector's shift: `index >> (variables & 63)`. -/
theorem and63 (x : Word) : (x &&& 63#64).toNat = x.toNat % 64 := by
  rw [BitVec.toNat_and, show (63#64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The suffix's offset: `variables << 4`. -/
theorem shl4 (x : Word) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needE needF : Nat} (hnS : 64 + needS ≤ need) (hnE : needE ≤ need) (hnF : 64 + needF ≤ need)
    (hsp : SelectorPointT.SpecT env p L.selectorPoint.idx needS) (heq : EqEvalOwnT.specT env p L.eqEval.idx needE)
    (hfail : Aborts env p L.sliceIndexFail.idx needF) : specT env p i need := by
  intro pt
  rv_autoT hp with [hL] using [hsp, hfail, heq (Model.selectorPointRust (regs .x11 >>> (regs .x10 &&& 63#64).toNat)
    (BitVec.ofNat 64 (List.map Model.limbs pt).length - regs .x10).toNat) (pt.drop (regs .x10).toNat)]
  all_goals
    have hlen : pt.length < 2 ^ 60 := by
      have := hpre_7.1; simp only [Layouts.E.byteSize, List.length_map] at this; omega
    have hv : (regs .x10).toNat ≤ pt.length := by
      rw [BitVec.le_def] at hc; simp at hc; rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hsub : (BitVec.ofNat 64 (List.map Model.limbs pt).length - regs .x10).toNat =
        pt.length - (regs .x10).toNat := by
      rw [BitVec.toNat_sub_of_le (by simpa using hc)]; simp; omega
    have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
    have hF : env.Frame top Tactic.F m m1 := by
      have e : ∀ k, 8 ≤ k → k ≤ 64 → (top + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = top.toNat - k := fun k h1 h2 => by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have e8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := e 8 (by omega) (by omega)
      have e16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := e 16 (by omega) (by omega)
      have e24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := e 24 (by omega) (by omega)
      have e32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 := e 32 (by omega) (by omega)
      have e40 : (top + 18446744073709551576#64).toNat = top.toNat - 40 := e 40 (by omega) (by omega)
      have e64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := e 64 (by omega) (by omega)
      have hS := Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot
        (Env.Frame.refl (top := top) (out := Tactic.F) hpre_5) (a := top + 18446744073709551608#64) (v := ret)
        (by omega) (by omega)) (a := top + 18446744073709551600#64) (v := regs .x8) (by omega) (by omega))
        (a := top + 18446744073709551592#64) (v := regs .x9) (by omega) (by omega))
        (a := top + 18446744073709551584#64) (v := regs .x18) (by omega) (by omega))
        (a := top + 18446744073709551576#64) (v := regs .x19) (by omega) (by omega)
      refine hS.trans hret1_14 (by omega) fun a ha => .inl ?_
      unfold Spec.Whir.SretOut InRange at ha
      simp only [updReg, Tactic.rf_get_x10, Layouts.Vec.byteSize, reduceCtorEq, ite_false] at ha
      omega
    have hown : OwnSlice env m top (regs .x12) pt.length := hpre_2 ▸ hpre_8
    obtain ⟨ptr, cap, hV, -⟩ := hret1_16
    have hP : MachineState.getMem m1 (top + 18446744073709551560#64) = ptr := by
      rw [← hV.ptr_eq, Proof.Runtime.VecHdrT.vecPtr_eq, BitVec.add_assoc]; rfl
    have hN : MachineState.getMem m1 (top + 18446744073709551568#64) =
        BitVec.ofNat 64 (List.map Model.limbs (Model.selectorPointRust (regs .x11 >>> (regs .x10 &&& 63#64).toNat)
          (BitVec.ofNat 64 (List.map Model.limbs pt).length - regs .x10).toNat)).length := by
      rw [← hV.len_eq, Proof.Runtime.VecHdrT.vecLen_eq, BitVec.add_assoc]; rfl
  · rw [Tactic.rf_get_x11, hN]
  · rw [Tactic.rf_get_x10, hP]; exact hV.elems
  · rw [Tactic.rf_get_x13]
    apply BitVec.eq_of_toNat_eq
    rw [hsub]; simp; omega
  · rw [Tactic.rf_get_x12, shl4, List.map_drop]
    exact OwnSlice.keep (es := (List.map Model.limbs pt).drop (regs .x10).toNat)
      (by simpa using OwnSlice.drop hown hv) hF hpre_5 (by omega) (OwnSliceT.EListAt.drop hpre_7 _)
  · have hpa : rvPtrAt (top + 18446744073709551552#64) = top + 18446744073709551560#64 := by
      unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
    have hca : rvCapAt (top + 18446744073709551552#64) = top + 18446744073709551552#64 := by
      unfold rvCapAt; rw [show BitVec.ofNat 64 Layouts.RawVecInner.cap = 0#64 from rfl, BitVec.add_zero]
    rw [hpa, hP] at hret1_20
    rw [hP]
    refine OwnSlice.of_bufT hret1_20 ?_ hret1_14.2.1
    have h22 := hret1_22
    rw [Proof.Runtime.VecHdrT.vecCap_eq, hret1_23] at h22
    rw [hca]
    simpa [Model.selectorPointRust] using h22
  · rw [shl4, List.length_drop]
    exact (OwnSlice.drop hown hv).frame hF (Nat.le_refl _)
  · refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      hF.trans hret3_14 (Nat.le_refl _) fun _ h => h.elim, hret3_15, fun v hv => ?_⟩
    apply hret3_16 v
    rw [← hv, placement, Model.PlacementRust.eqAbove, and63, hsub]

end Rv64mc.Proof.Multilinear.EqAboveT

/-- info: 'Rv64mc.Proof.Multilinear.EqAboveT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.EqAboveT.total
