/-
  Rv64mc.Proof.Runtime.FinishGrow

  `RawVecInner::finish_grow` meets `FinishGrowSpec`, from `alloc`'s and `memcpy`'s contracts: it checks that
  `new_cap * size` fits an `isize` rounded to the alignment (else `Err(CapacityOverflow)`, payload `0`), allocates
  the new block, copies the old one into it when there is one (`memcpy`), and writes `Ok(block)` (or, were the
  allocator to return null, `Err(AllocError)` with the alignment as payload).
-/

import Rv64mc.Spec.Runtime.RawVec
import Rv64mc.Spec.Runtime.Alloc
import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecInner.FinishGrow
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Runtime.FinishGrow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.Alloc.RawVec.RawVecInner.FinishGrow (Link tmpl)

theorem ult_or_zero {a b c d : Word} (h : (BinOp.ult.eval a b ||| BinOp.ult.eval c d) = 0#64) :
    b.toNat ≤ a.toNat ∧ d.toNat ≤ c.toNat := by
  unfold BinOp.eval at h
  by_cases h1 : a.ult b <;> by_cases h2 : c.ult d <;> simp only [h1, h2, ite_true] at h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at h1 h2
    exact ⟨h1, h2⟩

theorem mulhu_toNat (a b : Word) : (BinOp.mulhu.eval a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  show (BitVec.truncate 64 ((BitVec.zeroExtend 128 a * BitVec.zeroExtend 128 b) >>> 64)).toNat = _
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
  have : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by rw [← Nat.pow_add]
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]

theorem mul_toNat_of_mulhu {a b : Word} (h : (BinOp.mulhu.eval a b).toNat ≤ (0#64 : Word).toNat) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [mulhu_toNat, show (0#64 : Word).toNat = 0 by decide, Nat.le_zero, Nat.div_eq_zero_iff] at h
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]

/-- The new block's size: `new_cap * size` as the code computes it, exact and below `2^63` when its check passes. -/
theorem bytes_ok {a b al : Word}
    (h : (BinOp.ult.eval 0#64 (BinOp.mulhu.eval a b) ||| BinOp.ult.eval (9223372036854775808#64 - al) (a * b)) = 0#64)
    (h0 : 0 < al.toNat) (h1 : al.toNat < 2 ^ 63) : (a * b).toNat = a.toNat * b.toNat ∧ (a * b).toNat < 2 ^ 63 := by
  obtain ⟨g1, g2⟩ := ult_or_zero h
  refine ⟨mul_toNat_of_mulhu g1, ?_⟩
  rw [BitVec.toNat_sub, show (9223372036854775808#64 : Word).toNat = 2 ^ 63 by decide] at g2
  omega

theorem tag_eq (a : Word) : fgTagAt a = a := by
  simp only [fgTagAt, Layouts.ResultBlockTryReserve.tagOffset]; exact BitVec.add_zero a

theorem ptr_eq (a : Word) : fgPtrAt a = a + 8#64 := rfl

theorem ne8 {o : Word} (ho : o.toNat + 24 < 2 ^ 64) : o + 8#64 ≠ o := fun h => by
  have := congrArg BitVec.toNat h; rw [toNat_add_ofNat (k := 8) (by omega)] at this; omega

theorem ne16 {o : Word} (ho : o.toNat + 24 < 2 ^ 64) : o + 16#64 ≠ o := fun h => by
  have := congrArg BitVec.toNat h; rw [toNat_add_ofNat (k := 16) (by omega)] at this; omega

theorem ne816 {o : Word} (ho : o.toNat + 24 < 2 ^ 64) : o + 8#64 ≠ o + 16#64 := fun h => by
  have := congrArg BitVec.toNat h
  rw [toNat_add_ofNat (k := 8) (by omega), toNat_add_ofNat (k := 16) (by omega)] at this; omega

/-- The result's tag and pointer, through the three stores of a return. -/
theorem res3_tag {M : MachineState} {o a b t : Word} :
    (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t).getMem (fgTagAt o) = t := by
  rw [tag_eq, MachineState.getMem_setMem_eq]

theorem res3_ptr {M : MachineState} {o a b t : Word} (ho : o.toNat + 24 < 2 ^ 64) :
    (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t).getMem (fgPtrAt o) = a := by
  rw [ptr_eq, MachineState.getMem_setMem_ne (ne8 ho), MachineState.getMem_setMem_ne (ne816 ho),
    MachineState.getMem_setMem_eq]

theorem toNat_mul_lt {a b : Word} (h : a.toNat * b.toNat < 2 ^ 63) : (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]

theorem res3_next {env : Env} {M : MachineState} {o a b t : Word} (h0 : o ≠ env.nextAddr)
    (h8 : o + 8#64 ≠ env.nextAddr) (h16 : o + 16#64 ≠ env.nextAddr) :
    env.next (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t) = env.next M := by
  unfold Env.next
  rw [MachineState.getMem_setMem_ne (Ne.symm h0), MachineState.getMem_setMem_ne (Ne.symm h16),
    MachineState.getMem_setMem_ne (Ne.symm h8)]

theorem lt64 {a b c n h : Nat} (h1 : a + c = n) (h2 : n ≤ h) (h3 : h < 2 ^ 64) (h4 : b ≤ c) : a + b < 2 ^ 64 := by
  omega

theorem slot_le {top c : Word} (ht : 80 ≤ top.toNat) (hc : 0xffffffffffffffb0#64 ≤ c) :
    top + 0xffffffffffffffb0#64 ≤ top + c := by
  rw [BitVec.le_def] at hc ⊢
  rw [BitVec.toNat_add, BitVec.toNat_add]
  rw [show (0xffffffffffffffb0#64 : Word).toNat = 2 ^ 64 - 80 by decide] at hc ⊢
  have := top.isLt; have := c.isLt; omega

theorem far {o j q k a n N M H T : Nat} (hj : j < 24) (hq8 : q % 8 = 0) (ha : a = q + k - (q + k) % 8)
    (hown : o + 24 ≤ N ∨ T ≤ o) (hNq : N ≤ q) (hk : k < n) (hqn : q + n ≤ M) (hM : M ≤ H) (hHT : H < T) :
    o + j ≠ a := by
  omega

theorem res2_tag {M : MachineState} {o a t : Word} : ((M.setMem (o + 8#64) a).setMem o t).getMem (fgTagAt o) = t := by
  rw [tag_eq, MachineState.getMem_setMem_eq]

theorem res2_ptr {M : MachineState} {o a t : Word} (ho : o.toNat + 24 < 2 ^ 64) :
    ((M.setMem (o + 8#64) a).setMem o t).getMem (fgPtrAt o) = a := by
  rw [ptr_eq, MachineState.getMem_setMem_ne (ne8 ho), MachineState.getMem_setMem_eq]

set_option maxHeartbeats 2000000 in
set_option rv_sym.heap true in
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needM : Nat} (hnA : 80 + needA ≤ need) (hnM : 80 + needM ≤ need)
    (hal : AllocSpec env p L.alloc.idx needA) (hcp : MemcpySpec env p L.memcpy.idx needM) :
    FinishGrowSpec env p i need := by
  rv_auto hp stop [48] with [hL] using [hal, hcp]
  · rv_sym hp stop [74] with [hL] using [hal, hcp]
    all_goals try (rv_sym hp stop [76] with [hL] using [hal, hcp])
    all_goals try (rv_sym hp with [hL] using [hal, hcp])
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
    -- no block (`new_cap * size = 0`): not reached, the precondition asks for a nonzero size
    · exfalso; have := hb.1; rw [hc] at this; simp only [Nat.mul_comm] at this hpre_11
      rw [show (0#64 : Word).toNat = 0 by decide] at this; omega
    · intro h; rw [res3_tag] at h; exact absurd (by decide) h
    -- `alloc`'s argument
    · exact hb.2
    -- `Ok` from `alloc`, nothing to copy
    · intro _
      refine ⟨⟨by rw [res3_ptr ho]; exact hret1_16, ?_⟩, fun k hk => ?_⟩
      · rw [res3_ptr ho, res3_next hn0 hn8 hn16, ← hret1_18, hb.1, Nat.mul_comm]; exact Nat.le_refl _
      · rw [hc_2, show (0#64 : Word).toNat = 0 by decide, Nat.zero_mul] at hk; exact absurd hk (Nat.not_lt_zero _)
    · intro h; rw [res3_tag] at h; exact absurd (by decide) h
    -- `alloc` null: `Err`, the alignment
    · intro h; rw [res3_tag] at h; exact absurd h (by decide)
    · intro _; rw [res3_ptr ho]; exact hpre_9
    · exact hb.2
    · intro h; rw [res3_tag] at h; exact absurd h (by decide)
    · intro _; rw [res3_ptr ho]; exact hpre_9
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
        Env.static_setMem (Env.static_setMem (Env.static_setMem hret1_15 hst8) hst16) hst0, ?_, ?_⟩
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
  -- the overflow: `Err`, payload `0`
  · intro h; rw [res2_tag] at h; exact absurd h (by decide)
  · intro _; rw [res2_ptr (by simpa using hpre_7)]; decide

end Rv64mc.Proof.Runtime.FinishGrow
