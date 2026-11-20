/-
  Rv64mc.Proof.Runtime.GrowAmortized

  `RawVecInner::grow_amortized` meets `GrowAmortizedSpec`, from `finish_grow`'s contract. Up to the call it
  computes the new capacity, the largest of `len + additional` (or returns `0` on overflow), twice the old one and
  the least nonzero one (8 for bytes, else 4), and saves `ra`, `s0`, `s1`; this part is stepped to the instruction
  after the choice (`stop [42]`), where `after` takes over: it calls `finish_grow(sp, cap, ptr, new_cap, align,
  size)` and on `Ok` stores the new capacity and pointer in the header and returns `-1`.
-/

import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecInner.GrowAmortized
import Rv64mc.Spec.Runtime.RawVec

namespace Rv64mc.Proof.Runtime.GrowAmortized

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.Alloc.RawVec.RawVecInner.GrowAmortized (Link tmpl)

theorem toNat_sub {top : Word} {k : Nat} (hk : k ≤ top.toNat) (hk' : k < 2 ^ 64) :
    (top + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = top.toNat - k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := top.isLt; omega

theorem rvCapAt_eq (a : Word) : rvCapAt a = a := by
  simp only [rvCapAt, Layouts.RawVecInner.cap]; exact BitVec.add_zero a

theorem rvPtrAt_eq (a : Word) : rvPtrAt a = a + 8#64 := rfl

theorem fgTagAt_eq (a : Word) : fgTagAt a = a := by
  simp only [fgTagAt, Layouts.ResultBlockTryReserve.tagOffset]; exact BitVec.add_zero a

theorem fgPtrAt_eq (a : Word) : fgPtrAt a = a + 8#64 := rfl

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

/-- The frame's three saved words, below `top`. -/
def saved (m : MachineState) (top ra s0 s1 : Word) : MachineState :=
  ((m.setMem (top + 0xfffffffffffffff8#64) ra).setMem (top + 0xfffffffffffffff0#64) s0).setMem
    (top + 0xffffffffffffffe8#64) s1

section Saved

variable {m : MachineState} {top ra s0 s1 : Word} (hlim : env.stackLimit.toNat + 48 ≤ top.toNat)
include hlim

theorem off {k : Nat} (hk : 0 < k) (hk' : k ≤ 48) :
    (top + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = top.toNat - k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := top.isLt; have := env.layout; omega

/-- A word not in the frame's three slots reads as before. -/
theorem saved_getMem {b : Word} (hb : b.toNat < top.toNat - 24 ∨ top.toNat ≤ b.toNat) :
    (saved m top ra s0 s1).getMem b = m.getMem b := by
  have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := off hlim (k := 8) (by decide) (by decide)
  have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := off hlim (k := 16) (by decide) (by decide)
  have h24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := off hlim (k := 24) (by decide) (by decide)
  have n8 : b ≠ top + 0xfffffffffffffff8#64 := fun h => by rw [h, h8] at hb; omega
  have n16 : b ≠ top + 0xfffffffffffffff0#64 := fun h => by rw [h, h16] at hb; omega
  have n24 : b ≠ top + 0xffffffffffffffe8#64 := fun h => by rw [h, h24] at hb; omega
  simp only [saved, MachineState.getMem_setMem_ne n8, MachineState.getMem_setMem_ne n16,
    MachineState.getMem_setMem_ne n24]

theorem next_saved : env.next (saved m top ra s0 s1) = env.next m := by
  have := env.layout
  unfold Env.next
  exact saved_getMem hlim (by omega)

theorem frame_saved {out : Word → Prop} (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Frame top out m (saved m top ra s0 s1) := by
  refine ⟨by rw [next_saved hlim]; exact Nat.le_refl _, by rw [next_saved hlim]; exact hnx, fun b hb => ?_⟩
  refine saved_getMem hlim ?_
  rcases Nat.lt_or_ge b.toNat (top.toNat - 24) with h | h
  · exact Or.inl h
  · rcases Nat.lt_or_ge b.toNat top.toNat with h' | h'
    · exact absurd (Or.inl ⟨by omega, h'⟩) hb
    · exact Or.inr h'

theorem static_saved (hs : env.Static m) : env.Static (saved m top ra s0 s1) :=
  env.static_frame m _ (fun b _ hb => saved_getMem hlim (by have := env.layout; omega)) hs

theorem saved_ra : (saved m top ra s0 s1).getMem (top + 0xfffffffffffffff8#64) = ra := by
  have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := off hlim (k := 8) (by decide) (by decide)
  have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := off hlim (k := 16) (by decide) (by decide)
  have h24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := off hlim (k := 24) (by decide) (by decide)
  have n16 : top + 0xfffffffffffffff8#64 ≠ top + 0xfffffffffffffff0#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [h8, h16] at this; omega
  have n24 : top + 0xfffffffffffffff8#64 ≠ top + 0xffffffffffffffe8#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [h8, h24] at this; omega
  simp only [saved, MachineState.getMem_setMem_ne n24, MachineState.getMem_setMem_ne n16,
    MachineState.getMem_setMem_eq]

theorem saved_s0 : (saved m top ra s0 s1).getMem (top + 0xfffffffffffffff0#64) = s0 := by
  have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := off hlim (k := 16) (by decide) (by decide)
  have h24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := off hlim (k := 24) (by decide) (by decide)
  have n24 : top + 0xfffffffffffffff0#64 ≠ top + 0xffffffffffffffe8#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [h16, h24] at this; omega
  simp only [saved, MachineState.getMem_setMem_ne n24, MachineState.getMem_setMem_eq]

omit hlim in
theorem saved_s1 : (saved m top ra s0 s1).getMem (top + 0xffffffffffffffe8#64) = s1 := by
  simp only [saved, MachineState.getMem_setMem_eq]

end Saved

/-- **From the choice of the new capacity `nc` to the return.** -/
theorem after (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {nfg : Nat}
    (hfg : FinishGrowSpec env p L.finishGrow.idx nfg) {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (GrowAmortizedPost env) GrowOut ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + (48 + nfg) ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hpre : GrowPre env (regs .x13).toNat (regs .x14).toNat regs m)
    (hsp : regs .x2 = top) {nc : Word} (hnc1 : (regs .x11).toNat + (regs .x12).toNat ≤ nc.toNat)
    (hnc2 : (m.getMem (regs .x10)).toNat ≤ nc.toNat) (hnc3 : 0 < nc.toNat) (R : Reg → Word)
    (hR2 : R .x2 = top + 0xffffffffffffffd0#64) (hR8 : R .x8 = nc) (hR10 : R .x10 = regs .x10)
    (hR11 : R .x11 = m.getMem (regs .x10)) (hR14 : R .x14 = regs .x13)
    (hR15 : R .x15 = regs .x14)
    (hRs : R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
      R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27) :
    rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 42, ret, top⟩ :: rest, R, saved m top ret (regs .x8) (regs .x9)⟩ := by

  lsym hp with [hR2, hR8, hR10, hR11, hR14, hR15, Lprog.Isa.addrAt, hL.finishGrow, hL.s0, Holds.post,
    AbiRegs] using [hfg.contract]
  all_goals
    have hlay := env.layout
    obtain ⟨hown, hsz, hal0, hal1, hlive, hcs⟩ := hpre
    rw [hsp] at hown
    simp only [Env.Owned, Layouts.RawVecInner.byteSize] at hown
    rw [rvCapAt_eq, rvPtrAt_eq] at hlive
    rw [rvCapAt_eq] at hcs
    have hwr : (regs .x10).toNat + 16 < 2 ^ 64 := hown.2
    have hlim : env.stackLimit.toNat + 48 ≤ top.toNat := by omega
    have h48 : (top + 0xffffffffffffffd0#64).toNat = top.toNat - 48 := off hlim (k := 48) (by decide) (by decide)
    have h40 : (top + 0xffffffffffffffd8#64).toNat = top.toNat - 40 := off hlim (k := 40) (by decide) (by decide)
    have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := off hlim (k := 8) (by decide) (by decide)
    have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := off hlim (k := 16) (by decide) (by decide)
    have h24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := off hlim (k := 24) (by decide) (by decide)
    have hs8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
    -- the header's two words are not the frame's, nor `NEXT`, nor static
    have hin0 : InRange (regs .x10) 16 (regs .x10) := ⟨Nat.le_refl _, by omega⟩
    have hin8 : InRange (regs .x10) 16 (regs .x10 + 8#64) := ⟨by omega, by omega⟩
    have hcapM : (saved m top ret (regs .x8) (regs .x9)).getMem (regs .x10) = m.getMem (regs .x10) :=
      saved_getMem hlim (by rcases hown.1 with h | h <;> omega)
    have hptrM : (saved m top ret (regs .x8) (regs .x9)).getMem (regs .x10 + 8#64) = m.getMem (regs .x10 + 8#64) :=
      saved_getMem hlim (by rcases hown.1 with h | h <;> omega)
  -- `finish_grow(sp, cap, ptr, nc, align, size)`'s precondition
  · refine Holds.pre_call (by show _ ≤ (R .x2).toNat; rw [hR2, h48]; omega) (static_saved hlim hst)
      (by rw [next_saved hlim]; exact hnx) ?_
    simp only [FinishGrowPre, updReg_apply, reduceCtorEq, ite_true, ite_false, hR2, hR11, hR14, hR15]
    refine ⟨⟨Or.inr (Nat.le_refl _), by simp only [Layouts.ResultBlockTryReserve.byteSize]; omega⟩, hal0, hal1,
      hnc2, Nat.mul_pos hnc3 hsz, ?_, hcs⟩
    rw [hptrM]; unfold Env.Live; rw [next_saved hlim]; exact hlive
  -- after `finish_grow`: the frame's saved words are kept, and its result read
  all_goals
    obtain ⟨⟨hr2, hr8, hr9, hr18, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27⟩, hfr, hst', hfg'⟩ := hret
    simp only [FinishGrowPost, updReg_apply, reduceCtorEq, ite_true, ite_false, hR11, hR15, fgTagAt_eq,
      fgPtrAt_eq, hptrM, BitVec.add_assoc, show (0xffffffffffffffd0#64 + 8#64 : Word) = 0xffffffffffffffd8#64 by
        decide] at hfg'
    simp only [FinishGrowOut, updReg_apply, reduceCtorEq, ite_true, ite_false,
      Layouts.ResultBlockTryReserve.byteSize] at hfr
    have hnx' := hfr.2.1
    have hkeep : ∀ b : Word, top.toNat - 24 ≤ b.toNat → b.toNat < top.toNat →
        m'.getMem b = (saved m top ret (regs .x8) (regs .x9)).getMem b := fun b hb hb' => hfr.2.2 b fun hw => by
      unfold Env.MayWrite InRange at hw
      rcases hw with hw | hw | hw | hw
      · rw [h48] at hw; omega
      · omega
      · rw [hw] at hb; omega
      · rw [h48] at hw; omega
    have hra' : m'.getMem (top + 0xfffffffffffffff8#64) = ret :=
      (hkeep _ (by rw [h8]; omega) (by rw [h8]; omega)).trans (saved_ra hlim)
    have hs0' : m'.getMem (top + 0xfffffffffffffff0#64) = regs .x8 :=
      (hkeep _ (by rw [h16]; omega) (by rw [h16]; omega)).trans (saved_s0 hlim)
    have hs1' : m'.getMem (top + 0xffffffffffffffe8#64) = regs .x9 :=
      (hkeep _ (by rw [h24]; omega) (by rw [h24]; omega)).trans saved_s1
    have F1 : env.Frame top (GrowOut regs m) m m' :=
      (frame_saved hlim hnx).trans hfr (by rw [h48]; omega) fun a h => Or.inl (by
        unfold InRange at h; rw [h48] at h; omega)
    have hRS : r' .x18 = regs .x18 ∧ r' .x19 = regs .x19 ∧ r' .x20 = regs .x20 ∧ r' .x21 = regs .x21 ∧
        r' .x22 = regs .x22 ∧ r' .x23 = regs .x23 ∧ r' .x24 = regs .x24 ∧ r' .x25 = regs .x25 ∧
        r' .x26 = regs .x26 ∧ r' .x27 = regs .x27 :=
      ⟨hr18.trans hRs.1, hr19.trans hRs.2.1, hr20.trans hRs.2.2.1, hr21.trans hRs.2.2.2.1,
        hr22.trans hRs.2.2.2.2.1, hr23.trans hRs.2.2.2.2.2.1, hr24.trans hRs.2.2.2.2.2.2.1,
        hr25.trans hRs.2.2.2.2.2.2.2.1, hr26.trans hRs.2.2.2.2.2.2.2.2.1, hr27.trans hRs.2.2.2.2.2.2.2.2.2⟩
    -- a word of the frame's saved slots is not the header's
    have hfar : ∀ b : Word, top.toNat - 24 ≤ b.toNat → b.toNat < top.toNat →
        b ≠ regs .x10 ∧ b ≠ regs .x10 + 8#64 := fun b h1 h2 =>
      ⟨fun h => by rw [h] at h1 h2; rcases hown.1 with h | h <;> omega,
        fun h => by rw [h, hs8] at h1 h2; rcases hown.1 with h | h <;> omega⟩
    have n8 := hfar _ (by rw [h8]; omega) (by rw [h8]; omega)
    have n16 := hfar _ (by rw [h16]; omega) (by rw [h16]; omega)
    have n24 := hfar _ (by rw [h24]; omega) (by rw [h24]; omega)
  -- `Ok`: the header takes the new capacity and block, and `-1` is returned
  · have hok := hfg'.1 hc
    have hn0 : regs .x10 ≠ env.nextAddr := Env.Owned.not_next (n := 16) hown hnx (by omega) hin0
    have hn8 : regs .x10 + 8#64 ≠ env.nextAddr := Env.Owned.not_next (n := 16) hown hnx (by omega) hin8
    have h08 : regs .x10 ≠ regs .x10 + 8#64 := fun h => by
      have := congrArg BitVec.toNat h; rw [hs8] at this; omega
    have G1 := Env.Frame.setMem_out (top := top) (out := GrowOut regs m) (v := nc) hnx'
      (Or.inl (rvCapAt_eq _).symm) hn0
    have G2 := Env.Frame.setMem_out (top := top) (out := GrowOut regs m)
      (v := m'.getMem (top + 0xffffffffffffffd8#64)) G1.2.1 (Or.inr (rvPtrAt_eq _).symm) hn8
    have hnext : env.next ((m'.setMem (regs .x10) nc).setMem (regs .x10 + 8#64)
        (m'.getMem (top + 0xffffffffffffffd8#64))) = env.next m' := by
      unfold Env.next
      rw [MachineState.getMem_setMem_ne (Ne.symm hn8), MachineState.getMem_setMem_ne (Ne.symm hn0)]
    refine SafeN.ret hp rfl ?_ ?_ (hk _ _ ⟨?_, (F1.trans G1 (Nat.le_refl _) fun a h => Or.inr (Or.inr (Or.inr h))).trans
      G2 (Nat.le_refl _) (fun a h => Or.inr (Or.inr (Or.inr h))),
      Env.static_setMem (Env.static_setMem hst' (Env.Owned.not_static (n := 16) hown hnx (by omega) hin0))
        (Env.Owned.not_static (n := 16) hown hnx (by omega) hin8), fun _ => ?_⟩)
    · show (_ : Reg → Word) .x1 = ret
      simp only [updReg_apply, reduceCtorEq, ite_true, ite_false, MachineState.getMem_setMem_ne n8.2,
        MachineState.getMem_setMem_ne n8.1, hra']
    · show (_ : Reg → Word) .x2 = top
      simp only [updReg_apply, reduceCtorEq, ite_true, ite_false]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [updReg_apply, reduceCtorEq, ite_true, ite_false, MachineState.getMem_setMem_ne n16.2,
          MachineState.getMem_setMem_ne n16.1, hs0', MachineState.getMem_setMem_ne n24.2,
          MachineState.getMem_setMem_ne n24.1, hs1', hRS.1, hRS.2.1, hRS.2.2.1, hRS.2.2.2.1, hRS.2.2.2.2.1,
          hRS.2.2.2.2.2.1, hRS.2.2.2.2.2.2.1, hRS.2.2.2.2.2.2.2.1, hRS.2.2.2.2.2.2.2.2.1, hRS.2.2.2.2.2.2.2.2.2]
    · simp only [Grown, rvCapAt_eq, rvPtrAt_eq, MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne h08]
      refine ⟨hnc1, ⟨by rw [← next_saved hlim (ra := ret) (s0 := regs .x8) (s1 := regs .x9)]; exact hok.1.1,
        by rw [hnext]; exact hok.1.2⟩, fun k hk => ?_⟩
      have hcap0 : (m.getMem (regs .x10)).toNat ≠ 0 := fun h => by rw [h] at hk; omega
      have hl := hlive.resolve_left hcap0
      unfold Env.Live at hl
      have hk' : k < nc.toNat * (regs .x14).toNat := Nat.lt_of_lt_of_le hk (Nat.mul_le_mul_right _ hnc2)
      have hq1 := hok.1.1
      have hq2 := hok.1.2
      rw [next_saved hlim] at hq1
      have hqk : (m'.getMem (top + 0xffffffffffffffd8#64) + BitVec.ofNat 64 k).toNat =
          (m'.getMem (top + 0xffffffffffffffd8#64)).toNat + k := toNat_add_ofNat (by omega)
      have hpk : (m.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 k).toNat =
          (m.getMem (regs .x10 + 8#64)).toNat + k := toNat_add_ofNat (by omega)
      have a1 := toNat_alignToDword (m'.getMem (top + 0xffffffffffffffd8#64) + BitVec.ofNat 64 k)
      have a2 := toNat_alignToDword (m.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 k)
      rw [hqk] at a1
      rw [hpk] at a2
      rw [getByte_setMem_ne (fun h => by rw [← h, hs8] at a1; rcases hown.1 with h | h <;> omega),
        getByte_setMem_ne (fun h => by rw [← h] at a1; rcases hown.1 with h | h <;> omega), hok.2 k hk]
      exact getByte_congr (saved_getMem hlim (Or.inl (by omega)))
  -- `Err`: the payload returned, which is not `-1`, the header untouched
  · show (_ : Reg → Word) .x1 = ret
    simp only [updReg_apply, reduceCtorEq, ite_true, ite_false, hra']
  · show (_ : Reg → Word) .x2 = top
    simp only [updReg_apply, reduceCtorEq, ite_true, ite_false]
  · apply hk
    refine ⟨?_, F1, hst', fun h => ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [updReg_apply, reduceCtorEq, ite_true, ite_false, hs0', hs1', hRS.1, hRS.2.1, hRS.2.2.1,
          hRS.2.2.2.1, hRS.2.2.2.2.1, hRS.2.2.2.2.2.1, hRS.2.2.2.2.2.2.1, hRS.2.2.2.2.2.2.2.1,
          hRS.2.2.2.2.2.2.2.2.1, hRS.2.2.2.2.2.2.2.2.2]
    · have hlt := hfg'.2 hc
      simp only [updReg_apply, reduceCtorEq, ite_true, ite_false] at h
      rw [h] at hlt
      exact absurd hlt (by decide)

/-- **The contract of `grow_amortized`**, with 48 bytes of stack beyond `finish_grow`'s. -/
theorem ok (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {nfg : Nat}
    (hfg : FinishGrowSpec env p L.finishGrow.idx nfg) : GrowAmortizedSpec env p i (48 + nfg) := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, hpre⟩ hk
  lsym hp stop [42] with [hra, hsp]
  all_goals
    have hpre' := hpre
    obtain ⟨-, hsz, -, -, -, hcs⟩ := hpre'
    rw [rvCapAt_eq] at hcs
    have hcle : (m.getMem (regs .x10)).toNat ≤ (m.getMem (regs .x10)).toNat * (regs .x14).toNat :=
      Nat.le_mul_of_pos_right _ hsz
    have h2c : (m.getMem (regs .x10) <<< 1).toNat = 2 * (m.getMem (regs .x10)).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  -- the four choices of the new capacity, each at the cut
  iterate 8
    · have hreq : (regs .x12 + regs .x11).toNat = (regs .x11).toNat + (regs .x12).toNat := by
        rw [BitVec.le_def] at hc_1; rw [BitVec.toNat_add] at hc_1 ⊢; omega
      refine after (nc := _) hp hL hfg hk hstk hst hnx hpre hsp ?_ ?_ ?_ _ rfl rfl rfl rfl rfl rfl
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
        simp only [updReg_apply, reduceCtorEq, ite_true, ite_false] <;>
        simp only [BitVec.lt_def, BitVec.le_def, h2c, hreq] at hc hc_2 ⊢ <;>
        first | omega | (simp only [BitVec.toNat_ofNat] at hc ⊢; omega)
  -- `len + additional` overflows: `0`, an error
  · apply hk
    refine ⟨by simp (disch := decide) only [AbiRegs.updReg_iff]; exact AbiRegs.refl hsp, Env.Frame.refl hnx, hst,
      fun h => ?_⟩
    simp only [updReg_apply, reduceCtorEq, ite_true, ite_false] at h
    exact absurd h (by decide)

end Rv64mc.Proof.Runtime.GrowAmortized
