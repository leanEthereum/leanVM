/-
  Rv64mc.Proof.Runtime.GrowAmortizedT

  `RawVecInner::grow_amortized` is total: `GrowAmortizedSpec`'s postcondition, and the header a vector's
  (`VecReprT.RawVecT`) after as before, over any program holding its template, or the run ends with the guest's abort
  (`AbortStop`) where `finish_grow` does. From `finish_grow`'s total contract with the new block aligned
  (`FinishGrowAT`). The partial proof (`GrowAmortized.lean`) ported: `after`, from the choice of the new capacity to
  the return, by `rv_symT`, and the choice by `rv_autoT`. Its precondition adds to `GrowPre` that the header is
  `RawVecT` (in a window, 8-byte aligned, its buffer none or allocated, aligned, from the heap window's start), which
  `finish_grow`'s `FinishGrowPreT` and the stores into the header need.

  ## Main definitions

  * `GrowPreT`, `GrowAmortizedPostT`, `GrowAmortizedSpecT`

  ## Main results

  * `after`, `total`
-/

import Rv64mc.Proof.Runtime.GrowAmortized
import Rv64mc.Proof.Runtime.FinishGrowAT
import Rv64mc.Proof.Runtime.VecReprT

namespace Rv64mc.Proof.Runtime.GrowAmortizedT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime.GrowAmortized
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT)
open Rv64mc.Proof.Runtime.FinishGrowT (FinishGrowPreT)
open Rv64mc.Proof.Runtime.FinishGrowAT (FinishGrowSpecAT FinishGrowAligned)
open Rv64mc.Gen.Alloc.RawVec.RawVecInner.GrowAmortized (Link tmpl)

/-- A grow's total precondition: `GrowPre`, and the header `RawVecT` for elements of `size` bytes. -/
def GrowPreT (env : Env) (align size : Nat) (regs : Reg → Word) (m : MachineState) : Prop :=
  GrowPre env align size regs m ∧ RawVecT env m (regs .x10) size

/-- `grow_amortized`'s total postcondition: `GrowAmortizedPost`, and the header still `RawVecT`. -/
def GrowAmortizedPostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  GrowAmortizedPost env regs m r' m' ∧ RawVecT env m' (regs .x10) (regs .x14).toNat

/-- **The total contract of `grow_amortized`.** -/
def GrowAmortizedSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => GrowPreT env (regs .x13).toNat (regs .x14).toNat regs m)
    (GrowAmortizedPostT env) GrowOut AbortStop

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

set_option rv_sym.heap true in
/-- **From the choice of the new capacity `nc` to the return.** -/
theorem after (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {nfg : Nat}
    (hfg : FinishGrowSpecAT env p L.finishGrow.idx nfg) {Q : State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (GrowAmortizedPostT env) GrowOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + (48 + nfg) ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hpre : GrowPre env (regs .x13).toNat (regs .x14).toNat regs m)
    (hW : InWin env (regs .x10) 16) (hW8 : (regs .x10).toNat % 8 = 0)
    (hbuf : BufT env m (m.getMem (rvCapAt (regs .x10))) (m.getMem (rvPtrAt (regs .x10))) (regs .x14).toNat)
    (hwin : Windows env top m)
    (hsp : regs .x2 = top) (hal : top.toNat % 16 = 0) {nc : Word}
    (hnc1 : (regs .x11).toNat + (regs .x12).toNat ≤ nc.toNat)
    (hnc2 : (m.getMem (regs .x10)).toNat ≤ nc.toNat) (hnc3 : 0 < nc.toNat) (R : Reg → Word)
    (hR2 : R .x2 = top + 0xffffffffffffffd0#64) (hR8 : R .x8 = nc) (hR10 : R .x10 = regs .x10)
    (hR11 : R .x11 = m.getMem (regs .x10)) (hR14 : R .x14 = regs .x13)
    (hR15 : R .x15 = regs .x14)
    (hRs : R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
      R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 42, ret, top⟩ :: rest, R,
      ((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)⟩ := by
  have hlay := env.layout
  rw [rvCapAt_eq, rvPtrAt_eq] at hbuf
  obtain ⟨hown, hsz, hal0, hal1, hlive, hcs⟩ := hpre
  rw [hsp] at hown
  simp only [Env.Owned, Layouts.RawVecInner.byteSize] at hown
  rw [rvCapAt_eq, rvPtrAt_eq] at hlive
  rw [rvCapAt_eq] at hcs
  have hwr : (regs .x10).toNat + 16 < 2 ^ 64 := hown.2
  have hlim : env.stackLimit.toNat + 48 ≤ top.toNat := by omega
  have hl24 : env.stackLimit.toNat + 24 ≤ top.toNat := by omega
  have h48 : (top + 0xffffffffffffffd0#64).toNat = top.toNat - 48 := off hlim (k := 48) (by decide) (by decide)
  have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := off hlim (k := 8) (by decide) (by decide)
  have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := off hlim (k := 16) (by decide) (by decide)
  have h24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := off hlim (k := 24) (by decide) (by decide)
  have hs8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have hnM : env.next (((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64)
      (regs .x8)).setMem (top + 0xffffffffffffffe8#64) (regs .x9)) = env.next m := next_saved3 hl24
  have hptrM : (((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64)
      (regs .x8)).setMem (top + 0xffffffffffffffe8#64) (regs .x9)).getMem (regs .x10 + 8#64) =
      m.getMem (regs .x10 + 8#64) :=
    saved3_getMem hl24 (by rcases hown.1 with h | h <;> omega)
  rv_symT hp with [hR2, hR8, hR10, hR11, hR14, hR15, hL] using [hfg]
  -- `finish_grow(sp, cap, ptr, nc, align, size)`'s precondition
  · rw [hR8, hR15]; exact Nat.mul_pos hnc3 hsz
  · rw [hR11, hR10, hR15]; unfold Env.Live; rw [hnM]; exact hlive
  · rw [hR11, hR15]; exact hcs
  · rw [hR11, hR10]
    rcases hbuf with h | ⟨h1, -, -⟩
    · exact .inl h
    · exact .inr h1
  -- after `finish_grow`: the frame's saved words are kept, and its result read
  all_goals
    rw [hR2] at hret1_14 ⊢
    simp only [FinishGrowOut, updReg_apply, reduceCtorEq, ite_true, ite_false,
      Layouts.ResultBlockTryReserve.byteSize] at hret1_14
    have hnx' := hret1_14.2.1
    have hF := hret1_14
    rw [show ((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64)
      (regs .x8)).setMem (top + 0xffffffffffffffe8#64) (regs .x9) = saved3 m top ret (regs .x8) (regs .x9) from rfl]
      at hF
    have hkeep : ∀ b : Word, top.toNat - 24 ≤ b.toNat → b.toNat < top.toNat →
        m1.getMem b = (saved3 m top ret (regs .x8) (regs .x9)).getMem b := fun b hb hb' =>
      hret1_14.2.2 b fun hw => by
        unfold Env.MayWrite InRange at hw
        rcases hw with hw | hw | hw | hw
        · rw [h48] at hw; omega
        · omega
        · rw [hw] at hb; omega
        · rw [h48] at hw; omega
    have hra' : m1.getMem (top + 0xfffffffffffffff8#64) = ret :=
      (hkeep _ (by rw [h8]; omega) (by rw [h8]; omega)).trans (saved3_ra hl24)
    have hs0' : m1.getMem (top + 0xfffffffffffffff0#64) = regs .x8 :=
      (hkeep _ (by rw [h16]; omega) (by rw [h16]; omega)).trans (saved3_s0 hl24)
    have hs1' : m1.getMem (top + 0xffffffffffffffe8#64) = regs .x9 :=
      (hkeep _ (Nat.le_of_eq h24.symm) (by rw [h24]; omega)).trans saved3_s1
    have F1 : env.Frame top (GrowOut regs m) m m1 :=
      (frame_saved3 hl24 hnx).trans hret1_14 (by rw [h48]; omega) fun a h => Or.inl (by
        unfold InRange at h; rw [h48] at h; omega)
    simp only [BitVec.add_assoc, show (0xffffffffffffffd0#64 + 40#64 : Word) = 0xfffffffffffffff8#64 by decide,
      show (0xffffffffffffffd0#64 + 32#64 : Word) = 0xfffffffffffffff0#64 by decide,
      show (0xffffffffffffffd0#64 + 24#64 : Word) = 0xffffffffffffffe8#64 by decide,
      show (0xffffffffffffffd0#64 + 8#64 : Word) = 0xffffffffffffffd8#64 by decide] at hret1_16 hret1_17 hret1_18 ⊢
    simp only [fgTagAt_eq, fgPtrAt_eq, BitVec.add_assoc,
      show (0xffffffffffffffd0#64 + 8#64 : Word) = 0xffffffffffffffd8#64 by decide,
      hR2, hR8, hR11, hR15, hR10] at hret1_16 hret1_17 hret1_18 hc ⊢
    have hin0 : InRange (regs .x10) 16 (regs .x10) := ⟨Nat.le_refl _, by omega⟩
    have hin8 : InRange (regs .x10) 16 (regs .x10 + 8#64) := ⟨by omega, by omega⟩
    have hn0 : regs .x10 ≠ env.nextAddr := Env.Owned.not_next (n := 16) hown hnx (by omega) hin0
    have hn8 : regs .x10 + 8#64 ≠ env.nextAddr := Env.Owned.not_next (n := 16) hown hnx (by omega) hin8
    have h08 : regs .x10 ≠ regs .x10 + 8#64 := fun h => by
      have := congrArg BitVec.toNat h; rw [hs8] at this; omega
    have hsp0 : top + (0xffffffffffffffd0#64 + 48#64) = top := by
      rw [show (0xffffffffffffffd0#64 + 48#64 : Word) = 0#64 by decide, BitVec.add_zero]
    have hge := hwin.next_ge
    have hhe := hwin.heapEnd_le
  -- `Ok`: the header takes the new capacity and block, and `-1` is returned
  · exact hra'
  · have hok := hret1_16 (hc.trans rfl)
    have hal8 := hret1_18 (hc.trans rfl)
    have G1 := Env.Frame.setMem_out (top := top) (out := GrowOut regs m) (v := nc) hnx'
      (Or.inl (rvCapAt_eq _).symm) hn0
    have G2 := Env.Frame.setMem_out (top := top) (out := GrowOut regs m)
      (v := m1.getMem (top + 0xffffffffffffffd8#64)) G1.2.1 (Or.inr (rvPtrAt_eq _).symm) hn8
    have hnext : env.next ((m1.setMem (regs .x10) nc).setMem (regs .x10 + 8#64)
        (m1.getMem (top + 0xffffffffffffffd8#64))) = env.next m1 := by
      unfold Env.next
      rw [MachineState.getMem_setMem_ne (Ne.symm hn8), MachineState.getMem_setMem_ne (Ne.symm hn0)]
    have hq1 := hok.1.1
    have hq2 := hok.1.2
    rw [hnM] at hq1
    have hcap2 : ((m1.setMem (regs .x10) nc).setMem (regs .x10 + 8#64)
        (m1.getMem (top + 0xffffffffffffffd8#64))).getMem (rvCapAt (regs .x10)) = nc := by
      rw [rvCapAt_eq, MachineState.getMem_setMem_ne h08, MachineState.getMem_setMem_eq]
    have hptr2 : ((m1.setMem (regs .x10) nc).setMem (regs .x10 + 8#64)
        (m1.getMem (top + 0xffffffffffffffd8#64))).getMem (rvPtrAt (regs .x10)) =
        m1.getMem (top + 0xffffffffffffffd8#64) := by
      rw [rvPtrAt_eq, MachineState.getMem_setMem_eq]
    refine ⟨⟨hsp0, hs0', hs1', hRs.1, hRs.2.1, hRs.2.2.1, hRs.2.2.2.1, hRs.2.2.2.2.1, hRs.2.2.2.2.2.1,
      hRs.2.2.2.2.2.2.1, hRs.2.2.2.2.2.2.2.1, hRs.2.2.2.2.2.2.2.2.1, hRs.2.2.2.2.2.2.2.2.2⟩,
      (F1.trans G1 (Nat.le_refl _) fun a h => Or.inr (Or.inr (Or.inr h))).trans G2 (Nat.le_refl _)
        (fun a h => Or.inr (Or.inr (Or.inr h))),
      Env.static_setMem (Env.static_setMem hret1_15 (Env.Owned.not_static (n := 16) hown hnx (by omega) hin0))
        (Env.Owned.not_static (n := 16) hown hnx (by omega) hin8), fun _ => ?_, ?_⟩
    · simp only [Grown, hcap2, hptr2]
      refine ⟨hnc1, ⟨hq1, by rw [hnext]; exact hq2⟩, fun k hk => ?_⟩
      have hcap0 : (m.getMem (regs .x10)).toNat ≠ 0 := fun h => by rw [rvCapAt_eq, h] at hk; omega
      have hl := hlive.resolve_left hcap0
      unfold Env.Live at hl
      rw [rvCapAt_eq] at hk
      have hk' : k < nc.toNat * (regs .x14).toNat := Nat.lt_of_lt_of_le hk (Nat.mul_le_mul_right _ hnc2)
      have hqk : (m1.getMem (top + 0xffffffffffffffd8#64) + BitVec.ofNat 64 k).toNat =
          (m1.getMem (top + 0xffffffffffffffd8#64)).toNat + k := toNat_add_ofNat (by omega)
      have hpk : (m.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 k).toNat =
          (m.getMem (regs .x10 + 8#64)).toNat + k := toNat_add_ofNat (by omega)
      have a1 := toNat_alignToDword (m1.getMem (top + 0xffffffffffffffd8#64) + BitVec.ofNat 64 k)
      have a2 := toNat_alignToDword (m.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 k)
      rw [hqk] at a1
      rw [hpk] at a2
      rw [getByte_setMem_ne (fun h => by rw [← h, hs8] at a1; rcases hown.1 with h | h <;> omega),
        getByte_setMem_ne (fun h => by rw [← h] at a1; rcases hown.1 with h | h <;> omega), hok.2 k hk, rvPtrAt_eq]
      exact getByte_congr (saved3_getMem hl24 (Or.inl (by omega)))
    · refine ⟨hW, hW8, ?_, ?_⟩
      · rw [hcap2, hptr2]
        exact BufT.of_fresh ⟨hq1, by rw [hnext]; exact hq2⟩ hge hal8
      · rw [hcap2]
        omega
  -- `Err`: the payload returned, which is not `-1`, the header untouched
  · exact hra'
  · have hkh : ∀ b, InRange (regs .x10) 16 b → m1.getMem b = m.getMem b := fun b hb => by
      have hb' := hb
      unfold InRange at hb'
      have e1 := saved3_getMem (m := m) (ra := ret) (s0 := regs .x8) (s1 := regs .x9) hl24
        (b := b) (by rcases hown.1 with h | h <;> omega)
      refine (hF.2.2 b fun hw => ?_).trans e1
      rcases hw with hw | hw | hw | hw
      · rw [h48] at hw; rcases hown.1 with h | h <;> omega
      · rw [next_saved3 hl24] at hw; rcases hown.1 with h | h <;> omega
      · exact Env.Owned.not_next (n := 16) hown hnx (by omega) hb hw
      · unfold InRange at hw; rw [h48] at hw; rcases hown.1 with h | h <;> omega
    have hc0 := hkh _ hin0
    have hc8 := hkh _ hin8
    refine ⟨⟨hsp0, hs0', hs1', hRs.1, hRs.2.1, hRs.2.2.1, hRs.2.2.2.1, hRs.2.2.2.2.1, hRs.2.2.2.2.2.1,
      hRs.2.2.2.2.2.2.1, hRs.2.2.2.2.2.2.2.1, hRs.2.2.2.2.2.2.2.2.1, hRs.2.2.2.2.2.2.2.2.2⟩, F1, hret1_15,
      fun h => absurd (hret1_17 fun h' => hc (h'.trans rfl)) ?_, hW, hW8, ?_, ?_⟩
    · intro hlt
      have h' : m1.getMem (top + 0xffffffffffffffd8#64) = 18446744073709551615#64 := h
      rw [h'] at hlt
      exact absurd hlt (by decide)
    · rw [rvCapAt_eq, rvPtrAt_eq, hc0, hc8]
      exact hbuf.mono (by rw [← hnM]; exact hret1_14.1)
    · rw [rvCapAt_eq, hc0]
      exact hcs

set_option rv_sym.heap true in
/-- **`grow_amortized` is total**, with 48 bytes of stack beyond `finish_grow`'s. -/
theorem total (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {nfg : Nat}
    (hfg : FinishGrowSpecAT env p L.finishGrow.idx nfg) : GrowAmortizedSpecT env p i (48 + nfg) := by
  rv_autoT hp stop [42] with [hL]
  all_goals
    have hcs := hpre_12
    rw [rvCapAt_eq] at hcs
    have hcle : (m.getMem (regs .x10)).toNat ≤ (m.getMem (regs .x10)).toNat * (regs .x14).toNat :=
      Nat.le_mul_of_pos_right _ hpre_8
    have h2c : (m.getMem (regs .x10) <<< 1).toNat = 2 * (m.getMem (regs .x10)).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  -- the four choices of the new capacity, each at the cut
  iterate 8
    · have hreq : (regs .x12 + regs .x11).toNat = (regs .x11).toNat + (regs .x12).toNat := by
        rw [BitVec.le_def] at hc_1; rw [BitVec.toNat_add] at hc_1 ⊢; omega
      refine after (nc := _) hp hL hfg hstop hk hpre_3 hpre_4 hpre_5
        ⟨⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, hpre_10, hpre_11, hpre_12⟩ hpre_13 hpre_14 hpre_15 hpre_18 hpre_2 hpre_17
        ?_ ?_ ?_ _ rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
        simp only [Tactic.rf] <;>
        simp only [BitVec.lt_def, BitVec.le_def, h2c, hreq] at hc hc_2 ⊢ <;>
        first | omega | (simp only [BitVec.toNat_ofNat] at hc ⊢; omega)
  -- `len + additional` overflows: `0`, an error
  intro h
  exact absurd h (by decide)

end Rv64mc.Proof.Runtime.GrowAmortizedT

/-- info: 'Rv64mc.Proof.Runtime.GrowAmortizedT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.GrowAmortizedT.total
