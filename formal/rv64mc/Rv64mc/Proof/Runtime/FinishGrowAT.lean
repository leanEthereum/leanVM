/-
  Rv64mc.Proof.Runtime.FinishGrowAT

  `RawVecInner::finish_grow`'s total contract with the new block's alignment: `FinishGrowSpecT`'s
  (`FinishGrowT.lean`), and on `Ok` the block's pointer a multiple of 8, which `alloc` gives (`AllocPost`) and the
  growth chain's callers need to load and store the vector's elements (`VecReprT.BufT`). `FinishGrowPost` does not
  say it, so this is `FinishGrowT`'s proof with that one conjunct more at the two `Ok` returns.

  ## Main definitions

  * `FinishGrowAligned`, `FinishGrowSpecAT`

  ## Main results

  * `total`, `FinishGrowSpecAT.spec`: the alignment dropped, `FinishGrowSpecT`
-/

import Rv64mc.Proof.Runtime.FinishGrowT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.FinishGrowAT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime.FinishGrow
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Gen.Alloc.RawVec.RawVecInner.FinishGrow (Link tmpl)

open Rv64mc.Proof.Runtime.FinishGrowT (FinishGrowPreT FinishGrowSpecT)

/-- On `Ok`, the new block's pointer is a multiple of 8. -/
def FinishGrowAligned (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (fgTagAt (regs .x10)) = BitVec.ofNat 64 Layouts.ResultBlockTryReserve.Ok.tag →
    (m'.getMem (fgPtrAt (regs .x10))).toNat % 8 = 0

/-- **`finish_grow`'s total contract with the new block aligned**: `FinishGrowSpecT`'s, and `FinishGrowAligned`. -/
def FinishGrowSpecAT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (FinishGrowPreT env)
    (fun regs m r' m' => FinishGrowPost env regs m r' m' ∧ FinishGrowAligned regs m r' m') FinishGrowOut AbortStop

/-- The alignment dropped. -/
theorem FinishGrowSpecAT.spec {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}
    (h : FinishGrowSpecAT env p i need) : FinishGrowSpecT env p i need :=
  Isa.TContract.mono h (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ _ _ ⟨⟨ha, hf, hs, hp⟩, hc⟩ => ⟨⟨ha, hf, hs, hp.1⟩, hc⟩) fun _ _ _ _ _ _ _ hs => hs

set_option maxHeartbeats 2000000 in
set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needM : Nat} (hnA : 80 + needA ≤ need) (hnM : 80 + needM ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcp : MemcpySpecT env p L.memcpy.idx needM) :
    FinishGrowSpecAT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [48] with [hL] using [hal', hcp]
  · rv_symT hp stop [74] with [hL] using [hal', hcp]
    all_goals try (rv_symT hp stop [76] with [hL] using [hal', hcp])
    all_goals try (rv_symT hp with [hL] using [hal', hcp])
    all_goals
      have ho : (regs .x10).toNat + 24 < 2 ^ 64 := hpre_7
      have hlay := env.layout
      have hown : env.Owned m top (regs .x10) 24 := ⟨by rw [← hpre_2]; exact hpre_6, ho⟩
      have hn0 : regs .x10 ≠ env.nextAddr := hown.not_next hpre_5 (by omega) ⟨Nat.le_refl _, by omega⟩
      have hn8 : regs .x10 + 8#64 ≠ env.nextAddr := hown.not_next hpre_5 (by omega)
        ⟨by rw [toNat_add_ofNat (k := 8) (by omega)]; omega, by rw [toNat_add_ofNat (k := 8) (by omega)]; omega⟩
      have hn16 : regs .x10 + 16#64 ≠ env.nextAddr := hown.not_next hpre_5 (by omega)
        ⟨by rw [toNat_add_ofNat (k := 16) (by omega)]; omega, by rw [toNat_add_ofNat (k := 16) (by omega)]; omega⟩
      have hb := bytes_ok hc_1 hpre_8 hpre_9
    -- the new block's alignment at the returns: `alloc`'s; no block on `Err`
    all_goals try (show _ → _ % 8 = 0
                   first
                     | (intro hT; rw [res3_tag] at hT; done)
                     | (intro _; rwa [res3_ptr ho])
                     | (exfalso; have := hb.1; rw [hc] at this; simp only [Nat.mul_comm] at this hpre_11
                        rw [show (0#64 : Word).toNat = 0 by decide] at this; omega))
    -- no block (`new_cap * size = 0`): not reached, the precondition asks for a nonzero size
    · exfalso; have := hb.1; rw [hc] at this; simp only [Nat.mul_comm] at this hpre_11
      rw [show (0#64 : Word).toNat = 0 by decide] at this; omega
    · intro h; rw [res3_tag] at h; exact absurd (by decide) h
    -- `alloc`'s argument
    · exact hb.2
    -- `Ok` from `alloc`, nothing to copy
    · intro _
      refine ⟨⟨by rw [res3_ptr ho]; exact hret1_16, ?_⟩, fun k hk => ?_⟩
      · rw [res3_ptr ho, res3_next hn0 hn8 hn16, ← hret1_18, hb.1, Nat.mul_comm]
      · rw [hc_2, show (0#64 : Word).toNat = 0 by decide, Nat.zero_mul] at hk; exact absurd hk (Nat.not_lt_zero _)
    · intro h; rw [res3_tag] at h; exact absurd (by decide) h
    · exact hb.2
    -- `memcpy(new, old, cap * size)`'s precondition
    all_goals
      have hcs : (regs .x11 * regs .x15).toNat = (regs .x11).toNat * (regs .x15).toNat := toNat_mul_lt hpre_13
      have hc0 : (regs .x11).toNat ≠ 0 := fun h => hc_2 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      have hlive : env.Live m (regs .x12) ((regs .x11).toNat * (regs .x15).toNat) := hpre_12.resolve_left hc0
      have hle : (regs .x11).toNat * (regs .x15).toNat ≤ (regs .x15 * regs .x13).toNat := by
        rw [hb.1, Nat.mul_comm (regs .x15).toNat]; exact Nat.mul_le_mul_right _ hpre_10
    · rw [hcs]; exact lt64 hret2_18 hret2_14.2.1 env.heapEnd.isLt hle
    · rw [hcs]; unfold Env.Live at hlive; exact lt64 (Nat.add_comm _ _ ▸ rfl) (Nat.le_trans hlive hpre_5)
        env.heapEnd.isLt (Nat.le_refl _)
    · intro _ b h1 h2
      unfold InRange at h1 h2; unfold Env.Live at hlive; rw [hcs] at h1 h2
      have := hret2_16
      omega
    -- its windows: the new block in the heap, the old one in the input and heap window
    · have hge := hpre_18.next_ge
      have hhe := hpre_18.heapEnd_le
      have hn2 := hret2_14.2.1
      have h12 := hpre_16.resolve_left hc0
      unfold Env.Live at hlive
      rw [hcs]
      exact .inr ⟨.inl ⟨by omega, by omega⟩, by unfold OffStack; omega, inWindow_iff.2 (.inl ⟨by omega, by omega⟩),
        by unfold OffStack; omega⟩
    -- after `memcpy`: the frame's slots, above the copy, are kept
    all_goals
      have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
      have h80 : (top + 0xffffffffffffffb0#64).toNat = top.toNat - 80 := by
        rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
      have hq := hret2_18
      rw [hb.1] at hq
      have hn2 := hret2_14.2.1
      have hno : ∀ a : Word, (env.next m2).toNat ≤ a.toNat →
          ¬ DwordsOf (r2 .x10) (regs .x11 * regs .x15).toNat a := fun a ha hin => by
        unfold DwordsOf InRange at hin
        rw [toNat_alignToDword, hcs] at hin
        have := Nat.mul_le_mul_right (regs .x15).toNat hpre_10
        rw [Nat.mul_comm (regs .x15).toNat] at hq
        omega
      have hk1 : ∀ a : Word, top + 0xffffffffffffffb0#64 ≤ a → m1.getMem a = m2.getMem a := fun a ha =>
        keep1_1 a ha (hno a (by rw [BitVec.le_def, h80] at ha; omega))
    -- `ra` read back
    · have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := by
        rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
      have hle : top + 0xffffffffffffffb0#64 ≤ top + 0xfffffffffffffff8#64 := by rw [BitVec.le_def, h80, h8]; omega
      rw [hk1 _ hle, keep2_1 _ hle]
      rv_close
    -- the return after the copy
    · have F2 : env.Frame top Tactic.F m m2 := by
        refine Tactic.frame_call ?_ hret2_14 (by rw [h80]; omega)
        repeat (first | exact Tactic.frame_refl hpre_5 | refine Tactic.frame_store ?_ (by rv_close) (by rv_close))
      have hst80 : 80 ≤ top.toNat := by omega
      have hrd : ∀ c : Word, 0xffffffffffffffb0#64 ≤ c → m1.getMem (top + c) = m2.getMem (top + c) :=
        fun c hc => hk1 _ (slot_le hst80 hc)
      -- the frame: the prologue, `alloc`, `memcpy` (into the new block), the result's three words
      have Fm : env.Frame top (FinishGrowOut regs m) m m1 :=
        (Tactic.frame_weaken F2).trans hret1_14 (by rw [h80]; omega) fun a h => Or.inr (Or.inl (by
          have h' : DwordsOf (r2 .x10) (regs .x11 * regs .x15).toNat a := h
          unfold DwordsOf InRange at h'
          rw [toNat_alignToDword, hcs, hret2_17] at h'
          have := hret1_14.1
          have := Nat.mul_le_mul_right (regs .x15).toNat hpre_10
          rw [Nat.mul_comm (regs .x15).toNat] at hq
          omega))
      have hin0 : InRange (regs .x10) 24 (regs .x10) := ⟨Nat.le_refl _, by omega⟩
      have hin8 : InRange (regs .x10) 24 (regs .x10 + 8#64) :=
        ⟨by rw [toNat_add_ofNat (k := 8) (by omega)]; omega, by rw [toNat_add_ofNat (k := 8) (by omega)]; omega⟩
      have hin16 : InRange (regs .x10) 24 (regs .x10 + 16#64) :=
        ⟨by rw [toNat_add_ofNat (k := 16) (by omega)]; omega, by rw [toNat_add_ofNat (k := 16) (by omega)]; omega⟩
      have G1 := Env.Frame.setMem_out (top := top) (out := FinishGrowOut regs m) (v := r2 .x10) Fm.2.1 hin8 hn8
      have G2 := Env.Frame.setMem_out (top := top) (out := FinishGrowOut regs m) (v := regs .x15 * regs .x13)
        G1.2.1 hin16 hn16
      have G3 := Env.Frame.setMem_out (top := top) (out := FinishGrowOut regs m) (v := 0#64) G2.2.1 hin0 hn0
      have hst8 := Env.Owned.not_static hown hpre_5 (by omega) hin8
      have hst16 := Env.Owned.not_static hown hpre_5 (by omega) hin16
      have hst0 := Env.Owned.not_static hown hpre_5 (by omega) hin0
      have hm12 := hret1_14.1
      refine ⟨?_, ((Fm.trans G1 (Nat.le_refl _) fun a h => Or.inr (Or.inr (Or.inr h))).trans G2 (Nat.le_refl _)
        fun a h => Or.inr (Or.inr (Or.inr h))).trans G3 (Nat.le_refl _) fun a h => Or.inr (Or.inr (Or.inr h)),
        Env.static_setMem (Env.static_setMem (Env.static_setMem hret1_15 hst8) hst16) hst0, ⟨?_, ?_⟩, ?_⟩
      -- the saved registers, from the frame's slots
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;>
          (show m1.getMem _ = _
           rw [hrd _ (by decide), keep2_1 _ (slot_le hst80 (by decide))]
           rv_close)
      -- `Ok`: the new block, fresh, holding the old bytes first
      · intro _
        refine ⟨⟨by rw [res3_ptr ho]; exact hret2_16, ?_⟩, fun k hk => ?_⟩
        · rw [res3_ptr ho, res3_next hn0 hn8 hn16, Nat.mul_comm]
          rw [Nat.mul_comm (regs .x15).toNat] at hq
          omega
        · rw [res3_ptr ho]
          have hkn : k < (regs .x11 * regs .x15).toNat := by rw [hcs]; exact hk
          have hqk : (r2 .x10 + BitVec.ofNat 64 k).toNat = (r2 .x10).toNat + k := toNat_add_ofNat (by
            have := Nat.mul_le_mul_right (regs .x15).toNat hpre_10
            rw [Nat.mul_comm (regs .x15).toNat] at hq
            have := env.heapEnd.isLt
            omega)
          have hpk : (regs .x12 + BitVec.ofNat 64 k).toNat = (regs .x12).toNat + k := toNat_add_ofNat (by
            unfold Env.Live at hlive; have := env.heapEnd.isLt; omega)
          have a1 := toNat_alignToDword (r2 .x10 + BitVec.ofNat 64 k)
          have a2 := toNat_alignToDword (regs .x12 + BitVec.ofNat 64 k)
          rw [hqk] at a1
          rw [hpk] at a2
          have hfar : ∀ j : Nat, j < 24 → regs .x10 + BitVec.ofNat 64 j ≠ alignToDword (r2 .x10 + BitVec.ofNat 64 k) :=
            fun j hj he => by
              have h1 := congrArg BitVec.toNat he
              rw [toNat_add_ofNat (by omega), a1] at h1
              have hm := Nat.mul_le_mul_right (regs .x15).toNat hpre_10
              rw [Nat.mul_comm (regs .x15).toNat] at hq
              have hHT : env.heapEnd.toNat < top.toNat := by omega
              rw [← hpre_2] at hHT
              exact far hj hret2_17 rfl hpre_6 hret2_16 hk (by omega) hn2 hHT h1
          rw [getByte_setMem_ne (by simpa using hfar 0 (by decide)), getByte_setMem_ne (hfar 16 (by decide)),
            getByte_setMem_ne (hfar 8 (by decide)), hret1_17 k hkn]
          refine getByte_congr ?_
          rw [Env.Frame.getMem_below_next F2 hpre_5 (by unfold Env.Live at hlive; omega) id]
      · intro h; rw [res3_tag] at h; exact absurd (by decide) h
      · intro _; rw [res3_ptr ho]; exact hret2_17
  -- the overflow: `Err`, payload `0`
  all_goals first
    | (intro h; rw [res2_tag] at h; exact absurd h (by decide))
    | (intro _; rw [res2_ptr (by simpa using hpre_7)]; decide)

end Rv64mc.Proof.Runtime.FinishGrowAT

/-- info: 'Rv64mc.Proof.Runtime.FinishGrowAT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.FinishGrowAT.total
