/-
  Rv64mc.Proof.Runtime.Memcmp

  `memcmp` meets `MemcmpSpec`: a loop over the bytes (`lbu` from each side, `bne` to the difference), counting
  `a2` down. The loop is a lemma by induction on the bytes left, its invariant that the comparison of what is left
  is the whole comparison (`memcmpVal`'s first equal bytes drop).
-/

import Rv64mc.Gen.Tmpl.Memcmp
import Rv64mc.Spec.Runtime.Mem

namespace Rv64mc.Proof.Runtime.Memcmp

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.Memcmp (Link tmpl)

theorem bytesFrom_succ (m : MachineState) (a : Word) (n : Nat) :
    bytesFrom m a (n + 1) = m.getByte a :: bytesFrom m (a + 1#64) n := by
  simp only [bytesFrom, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [BitVec.add_zero]
  · refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply]
    congr 1
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem setWidth_inj {x y : BitVec 8} (h : x.setWidth 64 = y.setWidth 64) : x = y := by
  have := congrArg (BitVec.setWidth 8) h
  rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_eq, BitVec.setWidth_eq] at this

theorem pred_ofNat (k : Nat) :
    BitVec.ofNat 64 (k + 1 + 1) + 0xffffffffffffffff#64 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem pred_ne {k : Nat} (h : k + 2 < 2 ^ 64) : BitVec.ofNat 64 (k + 1 + 1) + 0xffffffffffffffff#64 ≠ 0#64 := by
  rw [pred_ofNat]; intro he; have := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega

theorem memcmpVal_eq {x y : BitVec 8} {xs ys : List (BitVec 8)} (h : x = y) :
    memcmpVal (x :: xs) (y :: ys) = memcmpVal xs ys := by
  simp [memcmpVal, h]

theorem memcmpVal_ne {x y : BitVec 8} {xs ys : List (BitVec 8)} (h : x ≠ y) :
    memcmpVal (x :: xs) (y :: ys) = x.setWidth 64 + -y.setWidth 64 := by
  simp [memcmpVal, h, BitVec.sub_eq_add_neg]

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

/-- **The loop**, at its head with `k + 1` bytes left from `a` and `b`, whose comparison is the whole one `V`. -/
theorem loop (hp : p[i]? = some (tmpl L)) {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState} {V : Word}
    (hk : ∀ r' m', Holds.post env (fun _ _ r' _ => r' .x10 = V) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hst : env.Static m) :
    ∀ k (a b : Word) (R : Reg → Word), AbiRegs top regs R → R .x1 = ret → R .x10 = a → R .x11 = b →
      R .x12 = BitVec.ofNat 64 (k + 1) → k + 1 < 2 ^ 64 →
      memcmpVal (bytesFrom m a (k + 1)) (bytesFrom m b (k + 1)) = V →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 2, ret, top⟩ :: rest, R, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro a b R hR hra h10 h11 h12 _ hV
    lsym hp stop [2] with [hra, hR.1, h10, h11, h12]
    -- the bytes differ: their difference
    · apply hk
      refine ⟨by simp (disch := decide) only [AbiRegs.updReg_iff]; exact hR, Env.Frame.refl hnx, hst, ?_⟩
      dsimp only
      show _ + -_ = V
      rw [← hV, bytesFrom_succ, bytesFrom_succ, memcmpVal_ne fun h => hc (congrArg (BitVec.setWidth 64) h)]
    -- the last byte is equal: zero
    · apply hk
      refine ⟨by simp (disch := decide) only [AbiRegs.updReg_iff]; exact hR, Env.Frame.refl hnx, hst, ?_⟩
      dsimp only
      show _ = V
      rw [← hV, bytesFrom_succ, bytesFrom_succ, memcmpVal_eq (setWidth_inj hc_1)]
      rfl
  | succ k ih =>
    intro a b R hR hra h10 h11 h12 hlt hV
    lsym hp stop [2] with [hra, hR.1, h10, h11, h12, pred_ne hlt]
    -- the bytes differ: their difference
    · apply hk
      refine ⟨by simp (disch := decide) only [AbiRegs.updReg_iff]; exact hR, Env.Frame.refl hnx, hst, ?_⟩
      dsimp only
      show _ + -_ = V
      rw [← hV, bytesFrom_succ m a (k + 1), bytesFrom_succ m b (k + 1),
        memcmpVal_ne fun h => hc (congrArg (BitVec.setWidth 64) h)]
    -- equal: the next byte
    · refine ih (a + 1#64) (b + 1#64) _ ?_ (by simpa [updReg_apply] using hra) (by simp [updReg_apply])
        (by simp [updReg_apply]) (by simp only [updReg_apply]; exact pred_ofNat k) (by omega) ?_
      · simp (disch := decide) only [AbiRegs.updReg_iff]; exact hR
      · rw [← hV, bytesFrom_succ m a (k + 1), bytesFrom_succ m b (k + 1), memcmpVal_eq (setWidth_inj hc_1)]

/-- **The contract of `memcmp`**, with no stack. -/
theorem ok (hp : p[i]? = some (tmpl L)) : MemcmpSpec env p i 0 := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, _, hst, hnx, _⟩ hk
  lsym hp stop [2] with [hra, hsp]
  -- nothing to compare
  · apply hk
    refine ⟨by simp (disch := decide) only [AbiRegs.updReg_iff]; exact AbiRegs.refl hsp, Env.Frame.refl hnx, hst, ?_⟩
    show _ = memcmpVal _ _
    rw [hc]; rfl
  -- the loop, with every byte left
  · obtain ⟨k, hk'⟩ : ∃ k, (regs .x12).toNat = k + 1 :=
      ⟨(regs .x12).toNat - 1, by
        have : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
        omega⟩
    refine loop (V := memcmpVal (bytesFrom m (regs .x10) (regs .x12).toNat)
      (bytesFrom m (regs .x11) (regs .x12).toNat)) hp hk hnx hst k _ _ _ (AbiRegs.refl hsp) hra rfl rfl ?_
      (by rw [← hk']; exact (regs .x12).isLt) (by rw [hk'])
    rw [← hk', BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Rv64mc.Proof.Runtime.Memcmp
