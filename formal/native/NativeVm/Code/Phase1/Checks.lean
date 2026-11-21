module

public import NativeVm.Code.Phase1.Frame

/-!
# Phase 1's checks

`checkBc_spec`, `checkScalars_spec`: each check fails exactly when its condition fails, and the
words it stores are the layout's (`BcOk`, `ScalarsOk`).
-/

@[expose] public section

namespace NativeVm.Code.Phase1

open Native NativeVm.Model LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wdisp eval_cw toNat_toUInt64 wp_load wp_store wp_then setMem_wd_ne
  setMem_wd_eq ctxBytecodeLen)

variable {s : QState} {P E : QState → Prop} {xs : List Stmt}

/-! ## Steps -/

theorem wp_failIf_by {c : Cond} {b : Prop} [Decidable b] (hc : c.eval s = decide b)
    (hok : ¬ b → WP (blk xs) s P E) (hfail : b → E s) : WP (blk (failIf c :: xs)) s P E := by
  by_cases h : b
  · exact NativeVm.Transcript.wp_failIf_fail (by rw [hc]; simp [h]) (hfail h)
  · exact NativeVm.Transcript.wp_failIf (by rw [hc]; simp [h]) (hok h)

theorem cmp_geu_subw {r : Reg64} {v : UInt64} {d k : Nat} {ki : Int64} (hd : d < 2 ^ 63)
    (hk : k < 2 ^ 63) (hki : ki.toUInt64.toNat = k) (h : s.reg r = v - d.toUInt64) :
    (Cond.cmp .geu r (.imm ki)).eval s = decide (¬ (d ≤ v.toNat ∧ v.toNat < d + k)) := by
  have := geu_sub (x := v.toNat) (d := d) (k := k) v.toNat_lt (by omega) (by omega)
  rw [toUInt64_toNat] at this
  simp only [Cond.eval, Rhs.eval, h, UInt64.le_iff_toNat_le, hki, this, decide_not]

/-! ## `checkBc` -/

/-- The bytecode's length is a power of two `2^l`, `4 ≤ l ≤ 34`. -/
def BcOk (n : Nat) : Prop := (0 < n ∧ n &&& (n - 1) = 0) ∧ (5 ≤ bitLength n ∧ bitLength n ≤ 35)

instance (n : Nat) : Decidable (BcOk n) := inferInstanceAs (Decidable (_ ∧ _))

theorem pow2_u {n : Nat} (hn : n < 2 ^ 64) (h0 : n ≠ 0) :
    ((n.toUInt64 - 1) &&& n.toUInt64 == 0) = decide (n &&& (n - 1) = 0) := by
  have h1 : n.toUInt64 - 1 = (n - 1).toUInt64 := by
    rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, toUInt64_sub hn (by omega)]
  rw [h1, toUInt64_and (by omega) hn, toUInt64_eq_zero (lt_of_le_of_lt Nat.and_le_left (by omega)),
    Nat.land_comm]

theorem checkBc_spec {p ctx : UInt64} {n : Nat} (hr14 : s.reg .r14 = p) (hrdi : s.reg .rdi = ctx)
    (hn : s.mem (wd ctx ctxBytecodeLen) = some n.toUInt64) (hn64 : n < 2 ^ 64)
    (hd : LDom p s.mem) :
    WP checkBc s (fun s' ↦ BcOk n ∧ s'.mem (wd p 1) = some (bitLength n - 5).toUInt64 ∧
      (∀ k, k ≠ 1 → k < 2 ^ 61 → s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s' ∧
      s'.reg .r13 = s.reg .r13)
      (fun s' ↦ ¬ BcOk n ∧ LFr p s s') := by
  unfold checkBc
  refine wp_load (eval_cw hrdi _) hn ?_
  refine wp_failIf_by (b := n = 0) (cmp_eq_imm (c := n) 0 hn64 (by omega) (by rsimp)) (fun h0 ↦ ?_)
    (fun h0 ↦ ⟨fun h ↦ by have := h.1.1; omega, LFr.refl p s |>.setReg (by decide) (by decide) _⟩)
  fstep; fstep; fstep
  refine wp_failIf_by (b := ¬ n &&& (n - 1) = 0) (by
    rw [cond_test_self]; rsimp; rw [pow2_u hn64 h0, decide_not]) (fun hp ↦ ?_)
    (fun hp ↦ ⟨fun h ↦ hp h.1.2, by
      refine LFr.setReg (LFr.setReg (LFr.setReg (LFr.setReg (LFr.refl p s) ?_ ?_ _) ?_ ?_ _) ?_ ?_ _)
        ?_ ?_ _ <;> decide⟩)
  rw [not_not] at hp
  refine wp_then (bitLen_spec _) fun s₁ ⟨h1, m1, f1⟩ ↦ ?_
  have e1 : ((((s.setReg .rax n.toUInt64).setReg .rbx n.toUInt64).setReg .rbx
      (n.toUInt64 - 1)).setReg .rbx ((n.toUInt64 - 1) &&& n.toUInt64)).reg .rax = n.toUInt64 := by
    rsimp
  rw [e1, toNat_toUInt64 hn64] at h1
  have F0 : LFr p s ((((s.setReg .rax n.toUInt64).setReg .rbx n.toUInt64).setReg .rbx
    (n.toUInt64 - 1)).setReg .rbx ((n.toUInt64 - 1) &&& n.toUInt64)) :=
    LFr.setReg (LFr.setReg (LFr.setReg (LFr.setReg (LFr.refl p s) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _
  have F1 := F0.trans (LFr.of_regs m1 f1 (by decide) (by decide))
  have hb : bitLength n < 2 ^ 63 := lt_of_le_of_lt (bitLength_le (k := 64) hn64) (by norm_num)
  fstep
  refine wp_failIf_by (b := ¬ (5 ≤ bitLength n ∧ bitLength n < 5 + 31))
    (by rw [cmp_geu_subw (v := (bitLength n).toUInt64) (d := 5) (k := 31) (by omega) (by omega)
      rfl (by rsimp; rw [h1]), toNat_toUInt64 (by omega)]) (fun hl ↦ ?_)
    (fun hl ↦ ⟨fun h ↦ hl ⟨h.2.1, by have := h.2.2; omega⟩, F1.setReg (by decide) (by decide) _⟩)
  rw [not_not] at hl
  have F2 := F1.setReg (r := .rdx) (by decide) (by decide) (s₁.reg .rdx - 5)
  have hr14' : (s₁.setReg .rdx (s₁.reg .rdx - 5)).reg .r14 = p := by
    rw [F2.r14, hr14]
  refine wp_store (eval_L hr14' 1) (F2.isSome hd (by omega)) ?_
  refine WP.blk_nil ⟨⟨⟨by omega, hp⟩, by omega⟩, ?_, fun k hk hk' ↦ ?_,
    F2.setMem hd (by omega) _, ?_⟩
  · rw [setMem_wd_eq _ _ rfl]
    rsimp
    rw [h1, show (5 : UInt64) = (5 : Nat).toUInt64 from rfl, toUInt64_sub (by omega) (by omega)]
  · rw [setMem_wd_ne _ _ hk (by omega) hk']
    rsimp
    rw [m1]
    rsimp
  · rsimp
    rw [f1 _ (by decide)]
    rsimp

/-! ## `checkScalars` -/

/-- The scalars' checks: the high limbs' `or` zero, the rate exponent `v7` in `1 .. 4`, the
memory's log-size `v0` in `1 .. 30`. -/
def ScalarsOk (o v0 v7 : UInt64) : Prop :=
  o = 0 ∧ (1 ≤ v7.toNat ∧ v7.toNat ≤ 4) ∧ (1 ≤ v0.toNat ∧ v0.toNat ≤ 30)

instance (o v0 v7 : UInt64) : Decidable (ScalarsOk o v0 v7) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem checkScalars_spec {p v0 v7 : UInt64} (hr14 : s.reg .r14 = p) (hd : LDom p s.mem)
    (h9 : s.mem (wd p 9) = some v0) (h16 : s.mem (wd p 16) = some v7) :
    WP checkScalars s (fun s' ↦ ScalarsOk (s.reg .r13) v0 v7 ∧ s'.mem (wd p 0) = some v0 ∧
      s'.mem (wd p 3) = some v7 ∧
      (∀ k, k ≠ 0 → k ≠ 3 → k < 2 ^ 61 → s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s')
      (fun s' ↦ ¬ ScalarsOk (s.reg .r13) v0 v7 ∧ LFr p s s') := by
  unfold checkScalars
  refine wp_failIf_by (b := ¬ s.reg .r13 = 0) (by
    rw [cond_test_self]; by_cases h : s.reg .r13 = 0 <;> simp [h]) (fun ho ↦ ?_)
    (fun ho ↦ ⟨fun h ↦ ho h.1, LFr.refl p s⟩)
  rw [not_not] at ho
  refine wp_load (eval_L hr14 16) h16 ?_
  refine wp_store (eval_L (by rsimp; exact hr14) 3) (by rsimp; exact hd 3 (by omega)) ?_
  fstep
  refine wp_failIf_by (b := ¬ (1 ≤ v7.toNat ∧ v7.toNat < 1 + 4))
    (by rw [cmp_geu_subw (v := v7) (d := 1) (k := 4) (by omega) (by omega) rfl (by rsimp)])
    (fun hr ↦ ?_) (fun hr ↦ ⟨fun h ↦ hr ⟨h.2.1.1, by have := h.2.1.2; omega⟩, by fr_tac hd⟩)
  rw [not_not] at hr
  refine wp_load (eval_L (by rsimp; exact hr14) 9) (by mem_simp; exact h9) ?_
  refine wp_store (eval_L (by rsimp; exact hr14) 0)
    (NativeVm.Field.isSome_setMem (by rsimp; exact hd 0 (by omega)) _ _) ?_
  fstep
  refine wp_failIf_by (b := ¬ (1 ≤ v0.toNat ∧ v0.toNat < 1 + 30))
    (by rw [cmp_geu_subw (v := v0) (d := 1) (k := 30) (by omega) (by omega) rfl (by rsimp)])
    (fun hm ↦ ?_) (fun hm ↦ ⟨fun h ↦ hm ⟨h.2.2.1, by have := h.2.2.2; omega⟩, by fr_tac hd⟩)
  rw [not_not] at hm
  refine WP.blk_nil ⟨⟨ho, ⟨hr.1, by omega⟩, ⟨hm.1, by omega⟩⟩, by mem_simp, by mem_simp,
    fun k hk0 hk3 hk ↦ by mem_simp, by fr_tac hd⟩

/-! ## The heights -/

theorem cmp_geu_w {r : Reg64} {v : UInt64} {k : Nat} {ki : Int64} (hki : ki.toUInt64.toNat = k)
    (h : s.reg r = v) : (Cond.cmp .geu r (.imm ki)).eval s = decide (k ≤ v.toNat) := by
  simp only [Cond.eval, Rhs.eval, h, UInt64.le_iff_toNat_le, hki]

theorem cmp_ltu_w {r : Reg64} {v : UInt64} {k : Nat} {ki : Int64} (hki : ki.toUInt64.toNat = k)
    (h : s.reg r = v) : (Cond.cmp .ltu r (.imm ki)).eval s = decide (v.toNat < k) := by
  simp only [Cond.eval, Rhs.eval, h, UInt64.lt_iff_toNat_lt, hki]

theorem cmp_eq_w {r : Reg64} {v : UInt64} {ki : Int64} (hki : ki.toUInt64 = 0)
    (h : s.reg r = v) : (Cond.cmp .eq r (.imm ki)).eval s = decide (v.toNat = 0) := by
  simp only [Cond.eval, Rhs.eval, h, hki]
  by_cases hv : v = 0
  · simp [hv]
  · have : v.toNat ≠ 0 := fun e ↦ hv (UInt64.toNat_inj.mp (by simpa using e))
    simp [hv, this]

/-- `rax := v - 1`, saturating at `0`. -/
theorem wp_pred {v : UInt64} (hv : s.reg .rax = v) :
    WP (.ite (.cmp .eq .rax (.imm 0)) .skip (I (.subi .rax 1))) s (fun s' ↦
      s'.reg .rax = (v.toNat - 1).toUInt64 ∧ s'.mem = s.mem ∧ RegsFrame [.rax] s s') E := by
  refine wp_ite_of (cmp_eq_w rfl hv) (fun h0 ↦ ?_) (fun h0 ↦ ?_)
  · simp only [decide_eq_true_eq] at h0
    refine WP.skip ⟨?_, rfl, fun _ _ ↦ rfl⟩
    rw [hv, h0]
    exact (UInt64.toNat_inj.mp (by simpa using h0) : v = 0) ▸ rfl
  · simp only [decide_eq_false_iff_not] at h0
    refine WP.ins rfl ⟨?_, rfl, by rf_tac⟩
    rsimp
    rw [hv, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl]
    have := toUInt64_sub (a := v.toNat) (b := 1) v.toNat_lt (by omega)
    rw [toUInt64_toNat] at this
    exact this

/-- `rdx := max rdx floor`. -/
theorem wp_maxi {x floor : Nat} {ki : Int64} (hki : ki.toUInt64 = floor.toUInt64)
    (hfl : floor < 2 ^ 64) (hx64 : x < 2 ^ 64) (hx : s.reg .rdx = x.toUInt64) :
    WP (.ite (.cmp .ltu .rdx (.imm ki)) (I (.movi .rdx ki)) .skip) s (fun s' ↦
      s'.reg .rdx = (max x floor).toUInt64 ∧ s'.mem = s.mem ∧ RegsFrame [.rdx] s s') E := by
  refine wp_ite_of (cmp_ltu_w (k := floor) (by rw [hki, toNat_toUInt64 hfl]) hx) (fun h ↦ ?_)
    (fun h ↦ ?_)
  · rw [decide_eq_true_eq, toNat_toUInt64 hx64] at h
    refine WP.ins rfl ⟨?_, rfl, by rf_tac⟩
    rsimp
    rw [hki, Nat.max_eq_right (by omega)]
  · rw [decide_eq_false_iff_not, toNat_toUInt64 hx64] at h
    refine WP.skip ⟨?_, rfl, fun _ _ ↦ rfl⟩
    rw [hx, Nat.max_eq_left (by omega)]

theorem heightC_spec {p v : UInt64} {i floor : Nat} (hi : i < 6) (hfl : floor < 2 ^ 31)
    (hr14 : s.reg .r14 = p) (hd : LDom p s.mem) (hv : s.mem (wd p (10 + i)) = some v) :
    WP (heightC i floor) s (fun s' ↦ v.toNat ≤ 2 ^ 30 ∧
      s'.mem (wd p (4 + i)) = some (max (log2Ceil v.toNat) floor).toUInt64 ∧
      (∀ k, k ≠ 4 + i → k < 2 ^ 61 → s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s')
      (fun s' ↦ ¬ v.toNat ≤ 2 ^ 30 ∧ LFr p s s') := by
  unfold heightC
  refine wp_load (eval_L hr14 _) hv ?_
  refine wp_failIf_by (b := 2 ^ 30 + 1 ≤ v.toNat) (cmp_geu_w rfl (by rsimp)) (fun hb ↦ ?_)
    (fun hb ↦ ⟨by omega, by fr_tac hd⟩)
  have F1 : LFr p s (s.setReg .rax v) := by fr_tac hd
  refine wp_then (wp_pred (v := v) (by rsimp)) fun s₂ ⟨h2, m2, f2⟩ ↦ ?_
  have F2 := F1.trans (LFr.of_regs m2 f2 (by decide) (by decide))
  refine wp_then (bitLen_spec s₂) fun s₃ ⟨h3, m3, f3⟩ ↦ ?_
  have F3 := F2.trans (LFr.of_regs m3 f3 (by decide) (by decide))
  rw [h2, toNat_toUInt64 (by have := v.toNat_lt; omega)] at h3
  have hbl : bitLength (v.toNat - 1) < 2 ^ 64 :=
    lt_of_le_of_lt (bitLength_le (k := 64) (by have := v.toNat_lt; omega)) (by norm_num)
  refine wp_then (wp_maxi (floor := floor) (by rfl) (by omega) hbl h3) fun s₄ ⟨h4, m4, f4⟩ ↦ ?_
  have F4 := F3.trans (LFr.of_regs m4 f4 (by decide) (by decide))
  refine wp_store (eval_L (by rw [F4.r14, hr14]) _) (F4.isSome hd (by omega)) ?_
  refine WP.blk_nil ⟨by omega, by rw [setMem_wd_eq _ _ rfl, h4]; rfl, fun k hk hk' ↦ ?_,
    F4.setMem hd (by omega) _⟩
  rw [setMem_wd_ne _ _ hk (by omega) hk', m4, m3, m2]
  rsimp

theorem heights_spec {p : UInt64} {rw : Nat → UInt64} (hr14 : s.reg .r14 = p) (hd : LDom p s.mem)
    (hrows : ∀ i < 6, s.mem (wd p (10 + i)) = some (rw i)) :
    WP heights s (fun s' ↦ (∀ i < 6, (rw i).toNat ≤ 2 ^ 30) ∧
      (∀ i < 6, s'.mem (wd p (4 + i)) = some (max (log2Ceil (rw i).toNat) (floorF i)).toUInt64) ∧
      (∀ k, (k < 4 ∨ 10 ≤ k) → k < 2 ^ 61 → s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s')
      (fun s' ↦ ¬ (∀ i < 6, (rw i).toNat ≤ 2 ^ 30) ∧ LFr p s s') := by
  unfold heights
  have := Keccak.Proof.wp_range_flatMap (s := s)
    (E := fun s' ↦ ¬ (∀ i < 6, (rw i).toNat ≤ 2 ^ 30) ∧ LFr p s s')
    (fun i ↦ [heightC i (floorF i)])
    (fun j s' ↦ (∀ i < j, (rw i).toNat ≤ 2 ^ 30) ∧
      (∀ i < j, s'.mem (wd p (4 + i)) = some (max (log2Ceil (rw i).toNat) (floorF i)).toUInt64) ∧
      (∀ k, (k < 4 ∨ 4 + j ≤ k) → k < 2 ^ 61 → s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s')
    6 ?_ ⟨fun _ h ↦ absurd h (by omega), fun _ h ↦ absurd h (by omega), fun _ _ _ ↦ rfl,
      LFr.refl p s⟩
  · refine WP.mono this (fun s' ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2, fun k hk hk' ↦ h3 k (by omega) hk', h4⟩)
      (fun _ h ↦ h)
  · intro j hj s' ⟨h1, h2, h3, h4⟩
    have hfl : floorF j < 2 ^ 31 := by unfold floorF; split <;> omega
    refine WP.blk_cons (WP.mono (heightC_spec (v := rw j) hj hfl (by rw [h4.r14, hr14])
      (LDom.of_fr hd h4) (by rw [h3 _ (by omega) (by omega)]; exact hrows j hj))
      (fun s₂ ⟨g1, g2, g3, g4⟩ ↦ WP.blk_nil ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, fun k hk hk' ↦ ?_,
        h4.trans g4⟩) (fun s₂ ⟨g1, g4⟩ ↦ ⟨fun h ↦ g1 (h j hj), h4.trans g4⟩))
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact g1
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [g3 _ (by omega) (by omega)]; exact h2 i hi
      · exact g2
    · rw [g3 _ (by omega) hk']; exact h3 k (by omega) hk'

/-! ## The stack -/

/-- The stack's log-size. -/
def stackLogF (κ : Nat → Nat) : Nat := max 16 (log2Ceil (sumF κ 0))

theorem stackC_spec {p : UInt64} {lm lb : Nat} {hs : Array Nat} (hr14 : s.reg .r14 = p)
    (hd : LDom p s.mem) (hm : KapMem s.mem p lm lb hs) :
    WP stackC s (fun s' ↦ stackLogF (kapF lm lb hs) ≤ 30 ∧
      s'.mem (wd p 2) = some (stackLogF (kapF lm lb hs)).toUInt64 ∧
      (∀ k, k ≠ 2 → k < 2 ^ 61 → s'.mem (wd p k) = s.mem (wd p k)) ∧
      s'.reg .rbp = (sumF (kapF lm lb hs) (keyF (kapF lm lb hs) 4)).toUInt64 ∧ LFr p s s')
      (fun s' ↦ ¬ stackLogF (kapF lm lb hs) ≤ 30 ∧ LFr p s s') := by
  unfold stackC
  have hκ := hm.kap_le
  fstep
  have F0 : LFr p s (s.setReg .r8 0) := by fr_tac hd
  refine wp_then (sumC_spec (kr := 0) (by rsimp; exact hr14) (hm.congr (by rsimp)) (by omega)
    (by rsimp; rfl)) fun s₁ ⟨h1, m1, f1⟩ ↦ ?_
  have F1 := F0.trans (LFr.of_regs m1 f1 (by decide) (by decide))
  have hlt := sumF_lt hκ 0
  fstep
  refine wp_then (wp_pred (v := (sumF (kapF lm lb hs) 0).toUInt64) (by rsimp; exact h1))
    fun s₂ ⟨h2, m2, f2⟩ ↦ ?_
  have F2 := (F1.setReg (r := .rax) (by decide) (by decide) (s₁.reg .r10)).trans
    (LFr.of_regs m2 f2 (by decide) (by decide))
  refine wp_then (bitLen_spec s₂) fun s₃ ⟨h3, m3, f3⟩ ↦ ?_
  have F3 := F2.trans (LFr.of_regs m3 f3 (by decide) (by decide))
  rw [h2, toNat_toUInt64 (n := sumF (kapF lm lb hs) 0) (by omega),
    toNat_toUInt64 (by omega)] at h3
  have hbl : log2Ceil (sumF (kapF lm lb hs) 0) < 2 ^ 64 :=
    lt_of_le_of_lt (bitLength_le (k := 64) (by omega)) (by norm_num)
  refine wp_then (wp_maxi (floor := 16) (by rfl) (by omega) hbl h3) fun s₄ ⟨h4, m4, f4⟩ ↦ ?_
  have F4 := F3.trans (LFr.of_regs m4 f4 (by decide) (by decide))
  replace h4 : s₄.reg .rdx = (stackLogF (kapF lm lb hs)).toUInt64 := by rw [h4, Nat.max_comm]; rfl
  have hsl : stackLogF (kapF lm lb hs) < 2 ^ 63 := by
    unfold stackLogF; have := bitLength_le (k := 64) (show sumF (kapF lm lb hs) 0 - 1 < 2 ^ 64 by omega)
    unfold log2Ceil; omega
  refine wp_failIf_by (b := ¬ stackLogF (kapF lm lb hs) ≤ 30)
    (by
      rw [cmp_geu_w (k := 31) (ki := 31) rfl h4, toNat_toUInt64 (by omega)]
      by_cases h : stackLogF (kapF lm lb hs) ≤ 30
      · simp [h]; omega
      · simp [h]; omega)
    (fun hl ↦ ?_) (fun hl ↦ ⟨hl, F4⟩)
  rw [not_not] at hl
  refine wp_store (eval_L (by rw [F4.r14, hr14]) _) (F4.isSome hd (by omega)) ?_
  have F5 := F4.setMem hd (k := 2) (by omega) (s₄.reg .rdx)
  have hmem : ∀ k, k ≠ 2 → k < 2 ^ 61 →
      (s₄.setMem (wd p 2) (s₄.reg .rdx)).mem (wd p k) = s.mem (wd p k) := fun k hk hk' ↦ by
    rw [setMem_wd_ne _ _ hk (by omega) hk', m4, m3, m2]; rsimp; rw [m1]; rsimp
  fstep
  have hm' : KapMem ((s₄.setMem (wd p 2) (s₄.reg .rdx)).setReg .rsi 4).mem p lm lb hs := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hm
    refine ⟨by rsimp; rw [hmem 0 (by omega) (by omega)]; exact a1,
      by rsimp; rw [hmem 1 (by omega) (by omega)]; exact a2,
      fun i hi ↦ by rsimp; rw [hmem _ (by omega) (by omega)]; exact a3 i hi, a4, a5, a6⟩
  refine wp_then (kapC_spec (c := 4) (by rsimp; rw [F4.r14, hr14]) hm' (by omega) (by rsimp))
    fun s₆ ⟨h6, m6, f6⟩ ↦ ?_
  have F6 := (F5.setReg (r := .rsi) (by decide) (by decide) 4).trans
    (LFr.of_regs m6 f6 (by decide) (by decide))
  fstep; fstep; fstep
  have hk4 := hκ 4
  have hkey : (kapF lm lb hs 4).toUInt64 <<< 8 + 251 = (keyF (kapF lm lb hs) 4).toUInt64 := by
    rw [show (8 : UInt64) = (8 : Nat).toUInt64 from rfl,
      NativeVm.Transcript.toUInt64_shl _ _ (by omega), show (251 : UInt64) = (251 : Nat).toUInt64 from rfl,
      NativeVm.Transcript.toUInt64_add, keyF]
    exact congrArg Nat.toUInt64 (by omega)
  refine wp_then (sumC_spec (kr := keyF (kapF lm lb hs) 4) (lm := lm) (lb := lb) (hs := hs)
    (by rsimp; rw [F6.r14, hr14])
    (by rsimp; rw [m6]; rsimp; exact hm') (by unfold keyF; omega) (by rsimp; rw [h6, hkey]))
    fun s₇ ⟨h7, m7, f7⟩ ↦ ?_
  fstep
  refine WP.blk_nil ⟨hl, ?_, fun k hk hk' ↦ ?_, by rsimp; exact h7, ?_⟩
  · rsimp; rw [m7]; rsimp; rw [m6]; rsimp; rw [setMem_wd_eq _ _ rfl, h4]
  · rsimp; rw [m7]; rsimp; rw [m6]; rsimp; exact hmem k hk hk'
  · refine LFr.setReg ?_ (by decide) (by decide) _
    refine LFr.trans ?_ (LFr.of_regs m7 f7 (by decide) (by decide))
    fr_tac hd

end NativeVm.Code.Phase1
