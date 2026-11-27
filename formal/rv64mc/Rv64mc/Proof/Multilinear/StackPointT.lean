/-
  Rv64mc.Proof.Multilinear.StackPointT

  `Placement::stack_point`'s safety contract (`SpecT`): it returns a vector (`VecT`) of the point's length plus
  `stack_log - variables` elements, its buffer fresh unless empty, or ends the run with the guest's abort
  (`AbortStop`) where `selector_point` or `<[&[E]]>::concat` does, over any program holding its template, from their
  total contracts (`SelectorPointT`, `ConcatSliceET`). The partial `StackPoint.spec`'s functional postcondition (the
  values, `Model.PlacementRust.stackPoint`) is not stated: `concat`'s total contract gives the result's length, not
  its values.

  The precondition (`PreT`) asks the result's slot a caller's, in a window and 8-byte aligned (`concat`'s), and the
  point `OwnSlice` (none, or owned by the caller, in a window, aligned), which gives `concat`'s `SliceT`
  (`sliceT_of_own`). The body is cut after `concat`'s return (instruction 52): `fin` restores the saved registers
  and returns. `concat`'s precondition is sealed (`CatPre`) so that the executor leaves it as one goal.

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`, `Slots`

  ## Main results

  * `sliceT_of_own`, `fin`, `total`
-/

import Rv64mc.Proof.Multilinear.SelectorPointT
import Rv64mc.Proof.Multilinear.OwnSliceT
import Rv64mc.Proof.Runtime.ConcatSliceET
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.Placement.StackPoint

namespace Rv64mc.Proof.Multilinear.StackPointT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT)
open Rv64mc.Proof.Runtime.ConcatSliceET (SliceT lenSum)
open Rv64mc.Proof.Runtime.VecHdrT (vecLen_eq vecPtr_eq)
open Rv64mc.Proof.Multilinear.OwnSliceT (OwnSlice)
open Rv64mc.Gen.Verifier.Multilinear.Placement.StackPoint (Link tmpl)

/-- The total precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned; the point
    (`a3`, `a4`) `OwnSlice`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    OwnSlice env m (regs .x2) (regs .x13) (regs .x14).toNat

/-- The total postcondition: the result a vector's of the point's length plus `stack_log - variables` elements, its
    buffer fresh unless empty. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ (vecLen m' (regs .x10)).toNat = (regs .x14).toNat + (regs .x15 - regs .x11).toNat ∧
    ((vecLen m' (regs .x10)).toNat = 0 ∨
      env.Fresh m m' (vecPtr m' (regs .x10)) ((vecLen m' (regs .x10)).toNat * 16))

/-- **The safety contract of `Placement::stack_point`**: `PostT` from `PreT`, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.SretOut Layouts.Vec.byteSize) AbortStop

/-- `concat`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def CatPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  Runtime.ConcatSliceET.PreT env regs m

/-- **A slice the caller may pass is one `concat` takes**, from a stack pointer `sp` no higher, after `NEXT` grew. -/
theorem sliceT_of_own {env : Env} {m M : MachineState} {top sp q n : Word} (h : OwnSlice env m top q n.toNat)
    (hA : 0xa0000000 ≤ env.nextAddr.toNat) (hE : env.heapEnd.toNat ≤ 0x78000000)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hsp : sp.toNat ≤ top.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hn : (env.next m).toNat ≤ (env.next M).toNat) :
    SliceT env M sp q n := by
  rcases h with h | ⟨⟨ho, -⟩, hw, -⟩
  · exact .inl h
  have := env.layout
  unfold InWin at hw
  refine .inr ⟨inWindow_iff.2 (by omega), ?_, ?_⟩
  · rcases ho with ho | ho
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rcases ho with ho | ho
    · exact .inl (by omega)
    · exact .inr (by omega)

/-- The prologue's four saved words in `M`, at `top - 8` down to `top - 32`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18

set_option rv_sym.heap true in
/-- **The return**, from instruction 52 (after `concat`): the saved registers restored. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (Spec.Whir.SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (h16 : top.toNat % 16 = 0) :
    ∀ R M, (R .x2 = top + 18446744073709551520#64 ∧ Runtime.ConcatSliceET.Saved regs R ∧ R .x19 = regs .x19 ∧
        R .x20 = regs .x20) → Slots M top ret regs →
      env.Frame top (Spec.Whir.SretOut Layouts.Vec.byteSize regs m) m M → env.Static M → M.code = m.code →
      PostT env regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 52, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hsl hF hS hcd hPost
  obtain ⟨t1, t2, t3, t4⟩ := hsl
  have hlay := env.layout
  rv_introT hR
  rv_symT hp with [_hL]
  · have h := hPost.1.2.2
    rwa [vecLen_eq, Runtime.VecHdrT.vecCap_eq] at h
  · exact hPost.2.1
  · exact hPost.2.2

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needC : Nat} (hnS : 96 + needS ≤ need) (hnC : 96 + needC ≤ need)
    (hsp : SelectorPointT.SpecT env p L.selectorPoint.idx needS)
    (hcat : Runtime.ConcatSliceET.SpecT env p L.concat.idx needC) : SpecT env p i need := by
  have hcat' : HoldsT env p L.concat.idx needC (CatPre env) (Runtime.ConcatSliceET.PostT env) SretVecOut
      AbortStop := by
    unfold CatPre; exact hcat
  rv_autoT hp stop [52] with [hL] using [hsp, hcat']
  all_goals
    have hlay := env.layout
    have hA := hpre_12.nextAddr_ge
    have hE := hpre_12.heapEnd_le
    have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
    have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
      fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
    have e8 := g 18446744073709551608#64 8 rfl (by omega)
    have e16 := g 18446744073709551600#64 16 rfl (by omega)
    have e24 := g 18446744073709551592#64 24 rfl (by omega)
    have e32 := g 18446744073709551584#64 32 rfl (by omega)
    have e40 := g 18446744073709551576#64 40 rfl (by omega)
    have e48 := g 18446744073709551568#64 48 rfl (by omega)
    have e56 := g 18446744073709551560#64 56 rfl (by omega)
    have e64 := g 18446744073709551552#64 64 rfl (by omega)
    have e72 := g 18446744073709551544#64 72 rfl (by omega)
    have e80 := g 18446744073709551536#64 80 rfl (by omega)
    have e88 := g 18446744073709551528#64 88 rfl (by omega)
    have e96 := g 18446744073709551520#64 96 rfl (by omega)
    have F1 := Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot
      (Env.Frame.refl (top := top) (out := Tactic.F) hpre_5) (a := top + 18446744073709551608#64) (v := ret)
      (by omega) (by omega)) (a := top + 18446744073709551600#64) (v := regs .x8) (by omega) (by omega))
      (a := top + 18446744073709551592#64) (v := regs .x9) (by omega) (by omega))
      (a := top + 18446744073709551584#64) (v := regs .x18) (by omega) (by omega)
    have F3 : env.Frame top Tactic.F m m1 := F1.trans hret1_14 (by omega) fun b hb => .inl (by
      unfold Spec.Whir.SretOut InRange at hb
      simp only [updReg, Tactic.rf_get_x10, Layouts.Vec.byteSize, reduceCtorEq, ite_false] at hb
      omega)
    have F4 := Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot F3
      (a := top + 18446744073709551552#64) (v := regs .x13) (by omega) (by omega))
      (a := top + 18446744073709551560#64) (v := regs .x14) (by omega) (by omega))
      (a := top + 18446744073709551568#64) (v := m1.getMem (top + 18446744073709551536#64)) (by omega) (by omega))
      (a := top + 18446744073709551576#64) (v := m1.getMem (top + 18446744073709551544#64)) (by omega) (by omega)
    have hown : env.Owned m top (regs .x10) 24 := hpre_2 ▸ ⟨hpre_6, hpre_7⟩
    have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  · unfold CatPre Runtime.ConcatSliceET.PreT
    simp only [updReg, Tactic.rf_get_x2, Tactic.rf_get_x10, Tactic.rf_get_x11, Tactic.rf_get_x12, reduceCtorEq,
      ite_false, show (2#64).toNat = 2 from rfl]
    have hn1 : (env.next m1).toNat ≤ (env.next ((((m1.setMem (top + 18446744073709551552#64) (regs .x13)).setMem
        (top + 18446744073709551560#64) (regs .x14)).setMem (top + 18446744073709551568#64)
        (m1.getMem (top + 18446744073709551536#64))).setMem (top + 18446744073709551576#64)
        (m1.getMem (top + 18446744073709551544#64)))).toNat := by
      rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega),
        Env.next_setMem_stack (by omega)]
    refine ⟨hown.frame (top' := top + 18446744073709551520#64) F4 (by omega), hpre_8, hpre_9, by decide,
      ⟨.inr (by omega), by omega⟩, .inr ⟨by omega, by have := hpre_12.top_le; omega⟩, by omega, fun k hk => ?_⟩
    have a0 : top + 18446744073709551552#64 + BitVec.ofNat 64 (16 * 0) = top + 18446744073709551552#64 := by
      simp
    have a8 : top + 18446744073709551552#64 + BitVec.ofNat 64 (16 * 0 + 8) = top + 18446744073709551560#64 := by
      rw [BitVec.add_assoc]; rfl
    have a16 : top + 18446744073709551552#64 + BitVec.ofNat 64 (16 * 1) = top + 18446744073709551568#64 := by
      rw [BitVec.add_assoc]; rfl
    have a24 : top + 18446744073709551552#64 + BitVec.ofNat 64 (16 * 1 + 8) = top + 18446744073709551576#64 := by
      rw [BitVec.add_assoc]; rfl
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · simp only [Runtime.ConcatSliceET.sptr, Runtime.ConcatSliceET.slen, a0, a8]
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq,
        MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_eq]
      exact sliceT_of_own (hpre_2 ▸ hpre_10) hA hE hpre_5 (by omega) (by omega) F4.1
    · simp only [Runtime.ConcatSliceET.sptr, Runtime.ConcatSliceET.slen, a16, a24]
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq,
        MachineState.getMem_setMem_eq]
      have hpa : rvPtrAt (top + 18446744073709551528#64) = top + 18446744073709551536#64 := by
        unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
      have hca : rvCapAt (top + 18446744073709551528#64) = top + 18446744073709551528#64 := by
        unfold rvCapAt; rw [show BitVec.ofNat 64 Layouts.RawVecInner.cap = 0#64 from rfl, BitVec.add_zero]
      have s2 : top + 18446744073709551528#64 + 16#64 = top + 18446744073709551544#64 := by
        rw [BitVec.add_assoc]; rfl
      have hb := hret1_20
      rw [hpa] at hb
      have hle := hret1_22
      rw [vecLen_eq, s2, Runtime.VecHdrT.vecCap_eq] at hle
      rw [hca] at hb
      exact sliceT_of_own (top := top) (OwnSlice.of_bufT hb hle hret1_14.2.1) hA hE hret1_14.2.1 (by omega)
        (by omega) hn1
  · have F5 : env.Frame top (Spec.Whir.SretOut Layouts.Vec.byteSize regs m) m m2 :=
      (Tactic.frame_weaken F4).trans hret2_14 (by omega) fun b hb => .inr (.inr (.inr (by
        unfold SretVecOut at hb
        simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false] at hb
        exact hb)))
    have k2 : ∀ a : Word, top.toNat - 32 ≤ a.toNat → a.toNat < top.toNat → m2.getMem a = m1.getMem a := by
      intro a h1 h2
      rw [hret2_14.2.2 a ?_]
      · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
          MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega))]
      · intro hw
        rcases hw with hw | hw | hw | hw
        · omega
        · have := hret2_14.2.1; omega
        · rw [hw] at h1; omega
        · unfold SretVecOut InRange at hw
          simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Vec.byteSize] at hw
          rcases hown.1 with h | h <;> omega
    have k1 : ∀ a : Word, top.toNat - 32 ≤ a.toNat → a.toNat < top.toNat →
        m1.getMem a = ((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64)
          (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64)
          (regs .x18)).getMem a := by
      intro a h1 h2
      refine hret1_14.2.2 a fun hw => ?_
      rcases hw with hw | hw | hw | hw
      · omega
      · have := hret1_14.2.1; omega
      · rw [hw] at h1; omega
      · unfold Spec.Whir.SretOut InRange at hw
        simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Vec.byteSize] at hw
        omega
    have hsl : Slots m2 top ret regs := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega),
          MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
          MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
      · rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega),
          MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
          MachineState.getMem_setMem_eq]
      · rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega),
          MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
      · rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega), MachineState.getMem_setMem_eq]
    have s0 : top + 18446744073709551552#64 + BitVec.ofNat 64 (16 * 0 + 8) = top + 18446744073709551560#64 := by
      rw [BitVec.add_assoc]; rfl
    have s1 : top + 18446744073709551552#64 + BitVec.ofNat 64 (16 * 1 + 8) = top + 18446744073709551576#64 := by
      rw [BitVec.add_assoc]; rfl
    have s2 : top + 18446744073709551528#64 + 16#64 = top + 18446744073709551544#64 := by
      rw [BitVec.add_assoc]; rfl
    have hlen := hret2_22
    simp only [lenSum, Runtime.ConcatSliceET.slen, s0, s1, show (2#64).toNat = 2 from rfl, Nat.zero_add] at hlen
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq] at hlen
    have hsel := hret1_23
    rw [vecLen_eq, s2] at hsel
    rw [hsel] at hlen
    exact fin hp hL hk hpre_12 hlim hpre_11 _ _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ hsl F5 hret2_15
      (by rw [hret2_24]; simp only [MachineState.code_setMem]; rw [hret1_25]; simp only [MachineState.code_setMem])
      ⟨⟨hret2_16, ⟨hret2_17, hret2_18, hret2_19, hret2_20⟩, hret2_21⟩, hlen,
        hret2_23.imp_right fun h => ⟨le_trans F4.1 h.1, h.2⟩⟩

end Rv64mc.Proof.Multilinear.StackPointT

/-- info: 'Rv64mc.Proof.Multilinear.StackPointT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.StackPointT.total
