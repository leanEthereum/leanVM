module

public import NativeVm.Code.Data

/-!
# Phase 7: one challenge's query positions

`qchunkC` is the inner chunk of `sampleQueriesAux` (`NativeVm.Model.Whir`): from a challenge `c`,
the `n = min (128 / depth) rem` positions `queryBits c (i * depth) depth`, `i < n`, stored from `D`.
The machine has no division and no variable right shift, so the loop counts while
`(i + 1) · depth ≤ 128` and `i < rem` (a sentinel `129` in `rdx` once `rem` runs out), and a
position's right shift goes by the bits of the count (`qShrSeq`, six conditional shifts). A position
`sh < 128` is the low word `lo` shifted right by `t` and the high word `hi` shifted left by `64 - t`
(as `(hi <<< 1) <<< (63 - t)`, which is `0` at `t = 0`): `lo, hi, t = c0, c1, sh` below `64`,
`c1, 0, sh - 64` above (`qword`, equal to `queryBits` by `qword_eq`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field

/-! ## Shifts on words -/

theorem qShr_shr (y : UInt64) {a b : Nat} (h : a + b < 64) :
    (y >>> a.toUInt64) >>> b.toUInt64 = y >>> (a + b).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_shiftRight,
    toNat_toUInt64 (by omega), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega),
    Nat.mod_eq_of_lt (show a < 64 by omega), Nat.mod_eq_of_lt (show b < 64 by omega),
    Nat.mod_eq_of_lt h, Nat.shiftRight_add]

theorem qShl_one_shl (y : UInt64) {b : Nat} (h : b < 64) :
    (y <<< 1) <<< b.toUInt64 = if b = 63 then 0 else y <<< (b + 1).toUInt64 := by
  have key : ((y <<< 1) <<< b.toUInt64).toNat = y.toNat * 2 ^ (b + 1) % 2 ^ 64 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft, toNat_toUInt64 (by omega),
      UInt64.toNat_one, Nat.mod_eq_of_lt h, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mod_mul_mod,
      show 1 % 64 = 1 from rfl]
    congr 1
    ring
  split
  · subst b
    apply UInt64.toNat_inj.mp
    rw [key, Nat.mul_mod_left]
    rfl
  · apply UInt64.toNat_inj.mp
    rw [key, UInt64.toNat_shiftLeft, toNat_toUInt64 (by omega),
      Nat.mod_eq_of_lt (show b + 1 < 64 by omega), Nat.shiftLeft_eq]

theorem qAnd63 {n : Nat} (h : n < 64) : n.toUInt64 &&& 63 = n.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, toNat_toUInt64 (by omega), show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem qNeg_add63 {t : Nat} (h : t < 64) : 0 - t.toUInt64 + 63 = (63 - t).toUInt64 := by
  have e : (63 - t).toUInt64 + t.toUInt64 = 63 := by
    rw [toUInt64_add, show 63 - t + t = 63 by omega]
    rfl
  rw [← e]
  open scoped UInt64.CommRing in ring

theorem qNeg_neg (T : UInt64) : 0 - (0 - T + 63) + 63 = T := by
  open scoped UInt64.CommRing in ring

theorem qToUInt64_sub {a b : Nat} (h : b ≤ a) : a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  have e : a.toUInt64 = (a - b).toUInt64 + b.toUInt64 := by
    rw [toUInt64_add, Nat.sub_add_cancel h]
  rw [e, sub_add_cancel']

/-- The word the code computes at position `sh`, the mask `mask`. -/
def qword (c : EW) (sh : Nat) (mask : UInt64) : UInt64 :=
  (((if sh < 64 then c.c0 else c.c1) >>> (if sh < 64 then sh else sh - 64).toUInt64) |||
    (((if sh < 64 then c.c1 else 0) <<< 1) <<< (63 - (if sh < 64 then sh else sh - 64)).toUInt64))
    &&& mask

/-- **The code's word at a position below `128` is `queryBits`.** -/
theorem qword_eq {c : EW} {sh depth : Nat} (hsh : sh < 128) (hd : depth < 64) :
    qword c sh (((1 : UInt64) <<< depth.toUInt64) - 1) = queryBits c sh depth := by
  unfold qword queryBits
  rw [ite_eq_right (show ¬ 64 ≤ depth by omega)]
  by_cases h64 : sh < 64
  · simp only [h64, ↓reduceIte]
    rw [qShl_one_shl _ (by omega)]
    by_cases h0 : sh = 0
    · subst h0
      simp
    · simp only [h0, ↓reduceIte, show 63 - sh ≠ 63 by omega, show 63 - sh + 1 = 64 - sh by omega]
  · simp only [h64, ↓reduceIte, UInt64.zero_shiftLeft, UInt64.or_zero, show sh ≠ 0 by omega,
      show sh < 128 by omega]

/-! ## A right shift by a register -/

/-- Shift `x` right by `k` when the count `t` is at least `k`, and take `k` off the count. -/
def qShrStep (x t : Reg64) (k : Nat) : Stmt :=
  .ite (.cmp .geu t (.imm (Int64.ofNat k))) (blk [I (.shri x k), I (.subi t (Int64.ofNat k))]) .skip

/-- `x := x >>> t` for `t < 64`, `t` consumed. -/
def qShrSeq (x t : Reg64) : Stmt :=
  blk [qShrStep x t 32, qShrStep x t 16, qShrStep x t 8, qShrStep x t 4, qShrStep x t 2,
    qShrStep x t 1]

variable {s : QState} {F : QState → Prop}

theorem qShrStep_spec {x t : Reg64} (hxt : x ≠ t) {k n r : Nat} {y : UInt64}
    (hk : (Int64.ofNat k).toUInt64 = k.toUInt64) (hk64 : k < 64) (hn : n < 64) (hr : r < 2 * k)
    (hrn : r ≤ n) (hx : s.reg x = y >>> (n - r).toUInt64) (ht : s.reg t = r.toUInt64) :
    WP (qShrStep x t k) s (fun s' ↦ s'.reg x = y >>> (n - r % k).toUInt64 ∧
      s'.reg t = (r % k).toUInt64 ∧ RegsFrame [x, t] s s' ∧ s'.mem = s.mem) F := by
  unfold qShrStep
  by_cases hkr : k ≤ r
  · have hm : r % k = r - k := by
      rw [Nat.mod_eq_sub_mod hkr, Nat.mod_eq_of_lt (by omega)]
    refine wp_ite_true ?_ ?_
    · rw [cond_geu, rhs_imm, ht, hk]
      exact decide_eq_true ((toUInt64_le (by omega) (by omega)).mpr hkr)
    fstep; fstep; fdone
    refine ⟨?_, ?_, rf_setReg (rf_setReg (rf_refl _ _) (by simp) _) (by simp) _, trivial⟩
    · rw [ite_eq_right hxt, hx, qShr_shr _ (by omega), hm]
      congr 2
      omega
    · rw [ite_eq_right (Ne.symm hxt), ht, hk, hm, qToUInt64_sub hkr]
  · have hm : r % k = r := Nat.mod_eq_of_lt (show r < k by omega)
    refine wp_ite_false ?_ (WP.skip ⟨?_, ?_, rf_refl _ _, rfl⟩)
    · rw [cond_geu, rhs_imm, ht, hk]
      exact decide_eq_false fun h ↦ hkr ((toUInt64_le (by omega) (by omega)).mp h)
    · rw [hx, hm]
    · rw [ht, hm]

theorem qShrSeq_spec {x t : Reg64} (hxt : x ≠ t) {n : Nat} (hn : n < 64) (ht : s.reg t = n.toUInt64) :
    WP (qShrSeq x t) s (fun s' ↦ s'.reg x = s.reg x >>> n.toUInt64 ∧ RegsFrame [x, t] s s' ∧
      s'.mem = s.mem) F := by
  have hx : s.reg x = s.reg x >>> (n - n).toUInt64 := by simp
  unfold qShrSeq
  refine WP.then (qShrStep_spec hxt (k := 32) (by decide) (by omega) hn (by omega) le_rfl hx ht)
    fun s1 ⟨x1, t1, f1, m1⟩ ↦ ?_
  refine WP.then (qShrStep_spec hxt (k := 16) (by decide) (by omega) hn (Nat.mod_lt _ (by omega))
    (by have := Nat.mod_le n 32; omega) x1 t1) fun s2 ⟨x2, t2, f2, m2⟩ ↦ ?_
  refine WP.then (qShrStep_spec hxt (k := 8) (by decide) (by omega) hn (Nat.mod_lt _ (by omega))
    (by have := Nat.mod_le n 32; have := Nat.mod_le (n % 32) 16; omega) x2 t2)
    fun s3 ⟨x3, t3, f3, m3⟩ ↦ ?_
  refine WP.then (qShrStep_spec hxt (k := 4) (by decide) (by omega) hn (Nat.mod_lt _ (by omega))
    (by have := Nat.mod_le n 32; have := Nat.mod_le (n % 32) 16;
        have := Nat.mod_le (n % 32 % 16) 8; omega) x3 t3)
    fun s4 ⟨x4, t4, f4, m4⟩ ↦ ?_
  refine WP.then (qShrStep_spec hxt (k := 2) (by decide) (by omega) hn (Nat.mod_lt _ (by omega))
    (by have := Nat.mod_le n 32; have := Nat.mod_le (n % 32) 16;
        have := Nat.mod_le (n % 32 % 16) 8; have := Nat.mod_le (n % 32 % 16 % 8) 4; omega) x4 t4)
    fun s5 ⟨x5, t5, f5, m5⟩ ↦ ?_
  refine WP.then (qShrStep_spec hxt (k := 1) (by decide) (by omega) hn (Nat.mod_lt _ (by omega))
    (by have := Nat.mod_le n 32; have := Nat.mod_le (n % 32) 16;
        have := Nat.mod_le (n % 32 % 16) 8; have := Nat.mod_le (n % 32 % 16 % 8) 4;
        have := Nat.mod_le (n % 32 % 16 % 8 % 4) 2; omega) x5 t5)
    fun s6 ⟨x6, _, f6, m6⟩ ↦ WP.blk_nil ⟨?_, ?_, ?_⟩
  · rw [x6, Nat.mod_one, Nat.sub_zero]
  · exact RegsFrame.trans f1 (RegsFrame.trans f2 (RegsFrame.trans f3 (RegsFrame.trans f4
      (RegsFrame.trans f5 f6))))
  · rw [m6, m5, m4, m3, m2, m1]

/-! ## One position -/

/-- Position `rbx` of the challenge in `r9`, `r10`, masked by `r11`, into `rsi`. -/
def qval : Stmt := blk [
  I (.mov .rsi .r9), I (.mov .rax .r10), I (.mov .rcx .rbx),
  .ite (.cmp .ltu .rcx (.imm 64)) .skip
    (blk [I (.mov .rsi .r10), I (.movi .rax 0), I (.subi .rcx 64)]),
  I (.shli .rax 1), I (.neg .rcx), I (.addi .rcx 63), I (.shlcl .rax),
  I (.neg .rcx), I (.addi .rcx 63),
  qShrSeq .rsi .rcx,
  I (.or .rsi .rax), I (.and .rsi .r11)]

theorem qval_spec {c : EW} {sh : Nat} {mask : UInt64} (h9 : s.reg .r9 = c.c0)
    (h10 : s.reg .r10 = c.c1) (hbx : s.reg .rbx = sh.toUInt64) (hsh : sh < 128)
    (h11 : s.reg .r11 = mask) :
    WP qval s (fun s' ↦ s'.reg .rsi = qword c sh mask ∧ RegsFrame [.rax, .rcx, .rsi] s s' ∧
      s'.mem = s.mem) F := by
  unfold qval
  fstep; fstep; fstep
  refine WP.then (Q := fun s1 ↦ s1.reg .rsi = (if sh < 64 then c.c0 else c.c1) ∧
      s1.reg .rax = (if sh < 64 then c.c1 else 0) ∧
      s1.reg .rcx = (if sh < 64 then sh else sh - 64).toUInt64 ∧
      RegsFrame [.rax, .rcx, .rsi] s s1 ∧ s1.mem = s.mem) ?_ fun s1 ⟨e1, e2, e3, f1, m1⟩ ↦ ?_
  · have hc : (Cond.cmp .ltu .rcx (.imm 64)).eval
        (((s.setReg .rsi (s.reg .r9)).setReg .rax (s.reg .r10)).setReg .rcx (s.reg .rbx)) =
        decide (sh < 64) := by
      rw [cond_ltu, rhs_imm]
      rsimp
      rw [hbx]
      exact decide_eq_decide.mpr (toUInt64_lt (b := 64) (by omega) (by omega))
    by_cases h64 : sh < 64
    · refine wp_ite_true (by rw [hc]; exact decide_eq_true h64) (WP.skip ⟨?_, ?_, ?_, ?_, rfl⟩)
      · rsimp; rw [h9, ite_eq_left h64]
      · rsimp; rw [h10, ite_eq_left h64]
      · rsimp; rw [hbx, ite_eq_left h64]
      · rf_tac
    · refine wp_ite_false (by rw [hc]; exact decide_eq_false h64) ?_
      fstep; fstep; fstep; fdone
      refine ⟨?_, ?_, ?_, by rf_tac, trivial⟩
      · rw [h10, ite_eq_right h64]
      · rw [ite_eq_right h64]
      · rw [hbx, ite_eq_right h64]
        exact qToUInt64_sub (b := 64) (by omega)
  · have ht : (if sh < 64 then sh else sh - 64) < 64 := by split <;> omega
    unfold qword
    generalize (if sh < 64 then sh else sh - 64) = t at e3 ht ⊢
    have q11 : s1.reg .r11 = mask := by rw [f1 .r11 (by simp), h11]
    fstep; fstep; fstep; fstep; fstep; fstep
    refine WP.then (qShrSeq_spec (x := .rsi) (t := .rcx) (by decide) ht (by rsimp; rw [qNeg_neg, e3]))
      fun s2 ⟨x2, f2, m2⟩ ↦ ?_
    rsimp at x2
    have a2 : s2.reg .rax = s1.reg .rax <<< 1 <<< (0 - s1.reg .rcx + 63 &&& 63) := by
      rw [f2 .rax (by simp)]; rsimp
    have r2 : s2.reg .r11 = mask := by rw [f2 .r11 (by simp)]; rsimp; exact q11
    have mm : s2.mem = s.mem := by rw [m2]; rsimp; exact m1
    have fr : RegsFrame [.rax, .rcx, .rsi] s s2 := fun r hr ↦ by
      have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [f2 r (by simp [hr'.2.1, hr'.2.2])]
      rsimp
      simp only [hr'.1, hr'.2.1, ↓reduceIte]
      exact f1 r hr
    fstep; fstep; fdone
    refine ⟨?_, by rf_tac; exact fr, ?_⟩
    · rw [x2, a2, r2, e1, e2, e3, qNeg_add63 ht, qAnd63 (by omega)]
    · exact mm

/-! ## The chunk -/

/-- The registers `qchunkC` writes. -/
abbrev qRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11, .r14, .r15]

/-- `rdx := 129` (the loop's exit) once the count `r15` is `0`. -/
def qSentinel : Stmt := .ite (.test true .r15 (.reg .r15)) (I (.movi .rdx 129)) .skip

/-- The positions of one challenge: `r9`, `r10` the challenge, `rcx` the depth, `r15` the positions
left, `r14` the destination. -/
def qchunkC : Stmt := blk [
  I (.mov .r8 .rcx), I (.movi .r11 1), I (.shlcl .r11), I (.subi .r11 1),
  I (.movi .rbx 0), I (.mov .rdx .rcx),
  qSentinel,
  .loop (.cmp .ltu .rdx (.imm 129)) (blk [
    qval, I (.store (at_ .r14 0) .rsi), I (.addi .r14 8), I (.subi .r15 1),
    I (.add .rbx .r8), I (.add .rdx .r8),
    qSentinel]),
  I (.mov .rcx .r8)]

theorem qSentinel_spec {m v : Nat} (h15 : s.reg .r15 = m.toUInt64) (hm : m < 2 ^ 64)
    (hdx : s.reg .rdx = v.toUInt64) :
    WP qSentinel s (fun s' ↦ s'.reg .rdx = (if m = 0 then 129 else v).toUInt64 ∧
      RegsFrame [.rdx] s s' ∧ s'.mem = s.mem) F := by
  have hc : (Cond.test true .r15 (.reg .r15)).eval s = decide (m = 0) := by
    simp only [Cond.eval, Rhs.eval, UInt64.and_self, h15]
    by_cases h0 : m = 0
    · subst h0
      rfl
    · have e : m.toUInt64 ≠ 0 := fun e ↦
        h0 ((NativeVm.Transcript.toUInt64_inj hm (show 0 < 2 ^ 64 by omega)).mp e)
      simp [e, h0]
  unfold qSentinel
  by_cases h0 : m = 0
  · refine wp_ite_true (by rw [hc]; exact decide_eq_true h0) (WP.ins' ?_)
    simp only [QInstr.step, QState.setReg_reg, QState.setReg_mem, ↓reduceIte, h0,
      int64Lit_toUInt64, NativeVm.Field.natLit_toUInt64]
    exact ⟨trivial, by rf_tac, trivial⟩
  · refine wp_ite_false (by rw [hc]; exact decide_eq_false h0) (WP.skip ⟨?_, rf_refl _ _, rfl⟩)
    rw [hdx, ite_eq_right h0]

/-- The loop's state after `i` positions. -/
def QInv (s : QState) (c : EW) (depth rem : Nat) (D mask : UInt64) (t : QState) : Prop :=
  ∃ i ≤ min (128 / depth) rem, t.reg .r14 = wd D i ∧ t.reg .r15 = (rem - i).toUInt64 ∧
    t.reg .rbx = (i * depth).toUInt64 ∧
    t.reg .rdx = (if rem - i = 0 then 129 else (i + 1) * depth).toUInt64 ∧
    t.reg .r8 = depth.toUInt64 ∧ t.reg .r11 = mask ∧
    (∀ k < i, t.mem (wd D k) = some (queryBits c (k * depth) depth)) ∧
    (∀ a, (∀ k < min (128 / depth) rem, a ≠ wd D k) → t.mem a = s.mem a) ∧
    (∀ k < min (128 / depth) rem, (t.mem (wd D k)).isSome) ∧ RegsFrame qRegs s t

/-- **`qchunkC` stores one challenge's positions.** -/
theorem qchunkC_spec {s : QState} {F : QState → Prop} {c : EW} {depth rem : Nat} {D : UInt64}
    (h9 : s.reg .r9 = c.c0) (h10 : s.reg .r10 = c.c1) (hcx : s.reg .rcx = depth.toUInt64)
    (hd1 : 1 ≤ depth) (hd : depth < 64)
    (h15 : s.reg .r15 = rem.toUInt64) (hrem : rem < 2 ^ 32) (h14 : s.reg .r14 = D)
    (hD : ∀ k < min (128 / depth) rem, (s.mem (wd D k)).isSome)
    (_hfD : Fits D (min (128 / depth) rem)) :
    WP qchunkC s (fun s' ↦ WordArr s'.mem D ((Array.range (min (128 / depth) rem)).map
        fun i ↦ queryBits c (i * depth) depth) ∧
      s'.reg .r14 = wd D (min (128 / depth) rem) ∧
      s'.reg .r15 = (rem - min (128 / depth) rem).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11, .r14, .r15] s s' ∧
      s'.reg .rcx = depth.toUInt64 ∧
      ∀ a, (∀ k < min (128 / depth) rem, a ≠ wd D k) → s'.mem a = s.mem a) F := by
  have hn128 : min (128 / depth) rem ≤ 128 := le_trans (min_le_left _ _) (Nat.div_le_self _ _)
  have hnd : min (128 / depth) rem * depth ≤ 128 :=
    le_trans (Nat.mul_le_mul_right _ (min_le_left _ _)) (Nat.div_mul_le_self _ _)
  set n := min (128 / depth) rem with hn
  set mask : UInt64 := ((1 : UInt64) <<< depth.toUInt64) - 1 with hmask
  -- bounds on the products the loop compares
  have hb : ∀ i ≤ n, (i + 1) * depth < 2 ^ 64 := fun i hi ↦ by
    have := Nat.mul_le_mul (show i + 1 ≤ 129 by omega) (show depth ≤ 64 by omega)
    omega
  unfold qchunkC
  fstep; fstep; fstep; fstep; fstep; fstep
  refine WP.then (Q := QInv s c depth rem D mask) ?_ fun s1 h1 ↦ ?_
  · refine WP.mono (qSentinel_spec (m := rem) (v := (0 + 1) * depth) (by rsimp; exact h15)
      (by omega) (by rsimp; rw [hcx, Nat.zero_add, Nat.one_mul])) (fun t ⟨d1, f1, m1⟩ ↦ ?_)
      (fun _ h ↦ h)
    have k : ∀ r, r ≠ .rdx → t.reg r = _ := fun r hr ↦ f1 r (by simpa using hr)
    refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk ↦ absurd hk (Nat.not_lt_zero _),
      fun a _ ↦ by rw [m1]; rfl, fun k hk ↦ by rw [m1]; exact hD k hk, ?_⟩
    · rw [k .r14 (by decide)]; rsimp; rw [h14, wd_zero]
    · rw [k .r15 (by decide)]; rsimp; rw [h15, Nat.sub_zero]
    · rw [k .rbx (by decide)]; rsimp; rw [Nat.zero_mul]; rfl
    · rw [d1, Nat.sub_zero]
    · rw [k .r8 (by decide)]; rsimp; rw [hcx]
    · rw [k .r11 (by decide)]; rsimp; rw [hcx, qAnd63 hd]
    · intro r hr
      have hr' := hr
      simp only [qRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [f1 r (by simpa using hr'.2.2.2.1)]
      rsimp
      simp only [hr'.2.2.2.2.2.1, hr'.2.2.2.2.2.2.1, hr'.2.1, hr'.2.2.2.1, ↓reduceIte]
  apply WP.blk_cons
  refine WP.loop (QInv s c depth rem D mask) (fun t ↦ (t.reg .r15).toNat) h1 ?_ ?_
  · intro t ⟨i, hi, t14, t15, tbx, tdx, t8, t11, tW, tF, tS, tf⟩ hc
    have hlt : (if rem - i = 0 then 129 else (i + 1) * depth) < 129 := by
      rw [cond_ltu, rhs_imm, tdx, int64Lit_toUInt64, decide_eq_true_eq] at hc
      exact (toUInt64_lt (b := 129) (by split <;> [omega; exact hb i hi]) (by omega)).mp hc
    have hri : rem - i ≠ 0 := fun h ↦ by rw [ite_eq_left h] at hlt; omega
    rw [ite_eq_right hri] at hlt
    have hi1 : i + 1 ≤ n := le_min ((Nat.le_div_iff_mul_le hd1).mpr (by omega)) (by omega)
    have hsh : i * depth < 128 := by rw [Nat.succ_mul] at hlt; omega
    refine WP.then (qval_spec (c := c) (sh := i * depth) (by rw [tf .r9 (by simp), h9])
      (by rw [tf .r10 (by simp), h10]) tbx hsh t11) fun t1 ⟨v1, f1, m1⟩ ↦ ?_
    refine wp_store (x := wd D i)
      (by rw [eval_at, f1 .r14 (by simp), t14, int64Zero_toUInt64, UInt64.add_zero])
      (by rw [m1]; exact tS i (by omega)) ?_
    fstep; fstep; fstep; fstep
    refine WP.then (qSentinel_spec (m := rem - (i + 1)) (v := (i + 1 + 1) * depth)
      (by rsimp; rw [f1 .r15 (by simp), t15, show rem - i = rem - (i + 1) + 1 by omega,
        ← toUInt64_succ, sub_add_cancel'])
      (by omega)
      (by rsimp; rw [f1 .rdx (by simp), f1 .r8 (by simp), tdx, t8, ite_eq_right hri, toUInt64_add,
        Nat.succ_mul (i + 1)])) fun t2 ⟨d2, f2, m2⟩ ↦ WP.blk_nil ⟨?_, ?_⟩
    · have k : ∀ r, r ≠ .rdx → t2.reg r = _ := fun r hr ↦ f2 r (by simpa using hr)
      have hm : ∀ a, t2.mem a = if a = wd D i then some (qword c (i * depth) mask) else t.mem a :=
        fun a ↦ by rw [m2]; rsimp; rw [QState.setMem_mem, m1, v1]
      refine ⟨i + 1, hi1, ?_, ?_, ?_, d2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [k .r14 (by decide)]; rsimp
        rw [f1 .r14 (by simp), t14, ← wd_add]
        rfl
      · rw [k .r15 (by decide)]; rsimp
        rw [f1 .r15 (by simp), t15, show rem - i = rem - (i + 1) + 1 by omega, ← toUInt64_succ,
          sub_add_cancel']
      · rw [k .rbx (by decide)]; rsimp
        rw [f1 .rbx (by simp), f1 .r8 (by simp), tbx, t8, toUInt64_add, Nat.succ_mul]
      · rw [k .r8 (by decide)]; rsimp; rw [f1 .r8 (by simp), t8]
      · rw [k .r11 (by decide)]; rsimp; rw [f1 .r11 (by simp), t11]
      · intro q hq
        rw [hm]
        by_cases hqi : q = i
        · subst hqi
          rw [ite_eq_left rfl, hmask, qword_eq hsh hd]
        · rw [ite_eq_right (fun h ↦ hqi ((wd_inj (by omega) (by omega)).mp h)), tW q (by omega)]
      · intro a ha
        rw [hm, ite_eq_right (ha i (by omega)), tF a ha]
      · intro q hq
        rw [hm]
        split
        · rfl
        · exact tS q hq
      · intro r hr
        have hr' := hr
        simp only [qRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        rw [f2 r (by simpa using hr'.2.2.2.1)]
        rsimp
        simp only [hr'.2.2.2.2.2.2.2.1, hr'.2.2.2.2.2.2.2.2, hr'.2.1, hr'.2.2.2.1, ↓reduceIte]
        rw [f1 r (by simp [hr'.1, hr'.2.2.1, hr'.2.2.2.2.1]), tf r hr]
    · rw [f2 .r15 (by simp)]; rsimp
      rw [f1 .r15 (by simp), t15, show rem - i = rem - (i + 1) + 1 by omega, ← toUInt64_succ,
        sub_add_cancel', toNat_toUInt64 (by omega), toUInt64_succ, toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hi, t14, t15, tbx, tdx, t8, t11, tW, tF, tS, tf⟩ hc
    have hin : i = n := by
      by_contra hne
      have hri : rem - i ≠ 0 := by omega
      rw [cond_ltu, rhs_imm, tdx, int64Lit_toUInt64, ite_eq_right hri, decide_eq_false_iff_not]
        at hc
      have hi1 : (i + 1) * depth ≤ n * depth := Nat.mul_le_mul_right _ (by omega)
      exact hc ((toUInt64_lt (b := 129) (hb i hi) (by omega)).mpr (by omega))
    subst hin
    fstep; fdone
    refine ⟨fun k hk ↦ ?_, t14, t15, by rf_tac; exact tf, t8, tF⟩
    simp only [Array.size_map, Array.size_range] at hk
    rw [Array.getElem_map, Array.getElem_range]
    exact tW k hk

end NativeVm.Code.P7
