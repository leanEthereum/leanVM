module

public import NativeVm.Wire.Tables
public import NativeVm.Wire.ModelSpec

/-!
# The rows

`rows` reads the row at each distinct position into its leaf, its leading zeros first (`row`), and
fails where the model's `rdRows` gives `none` or where the row width is not the least
(`rows_ok`). The rows are `rdRows`'s in closed form (`rows_rdRows`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Wire
open Native.SphincsVerifier (toUInt64_shl cond_ne_imm)

/-- The row of `w` words at `c`. -/
def rowsRowAt (B : List UInt8) (w c : Nat) : List K :=
  (List.range w).map fun i ↦ K.ofLane (leAt B (c + 8 * i) 8)

/-- `rdRows` in closed form. -/
theorem rows_rdRows (B : List UInt8) (w : Nat) : ∀ (n c : Nat), c ≤ B.length →
    rdRows B w n c = if c + 8 * w * n ≤ B.length then
      some ((List.range n).map fun j ↦ rowsRowAt B w (c + 8 * w * j), c + 8 * w * n) else none
  | 0, c, hc => by simp [rdRows, hc]
  | n + 1, c, hc => by
    simp only [rdRows, rdWords, Option.bind_eq_bind]
    by_cases h1 : c + 8 * w ≤ B.length
    · rw [ite_yes h1, Option.bind_some, rows_rdRows B w n (c + 8 * w) h1]
      by_cases h2 : c + 8 * w + 8 * w * n ≤ B.length
      · rw [ite_yes h2, ite_yes (by rw [Nat.mul_succ]; omega), Option.bind_some]
        simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
          rowsRowAt, Nat.mul_succ, Nat.add_assoc]
        ring_nf
      · rw [ite_no h2, ite_no (by rw [Nat.mul_succ]; omega)]
        rfl
    · rw [ite_no h1, ite_no (by rw [Nat.mul_succ]; omega)]
      rfl

theorem rows_lane_ofLane (w : UInt64) : (K.ofLane w).lane = w := (rfl)

theorem rows_ofLane_eq_zero (w : UInt64) : K.ofLane w = 0 ↔ w = 0 :=
  ⟨fun h ↦ by rw [← rows_lane_ofLane w, h]; rfl, fun h ↦ by rw [h]; rfl⟩

theorem rows_getD0 (B : List UInt8) (w c : Nat) :
    (rowsRowAt B w c).getD 0 0 = 0 ↔ w = 0 ∨ leAt B c 8 = 0 := by
  cases w with
  | zero => simp [rowsRowAt]
  | succ w => simp [rowsRowAt, List.range_succ_eq_map, rows_ofLane_eq_zero]

theorem rows_padded (B : List UInt8) {w lw c t : Nat} (hw : w ≤ lw) (ht : t < lw) :
    ((paddedLeaf (rowsRowAt B w c) lw).getD t 0).lane =
      if t < lw - w then 0 else leAt B (c + 8 * (t - (lw - w))) 8 := by
  unfold paddedLeaf rowsRowAt
  by_cases h : t < lw - w
  · rw [ite_yes h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, h]
    rfl
  · rw [ite_no h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, h, show t - (lw - w) < w by omega]
    rfl

theorem rows_workWords_lt : workWords < 2 ^ 32 := by
  unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ; norm_num

section Run

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64} {F : QState → Prop}

omit P in
theorem rows_shl3 {a : Nat} (h : a < 2 ^ 60) : a.toUInt64 <<< (3 : Nat).toUInt64 = (8 * a).toUInt64 := by
  rw [toUInt64_shl (by norm_num) (by omega), Nat.mul_comm]
  rfl

omit P in
theorem rows_adr_sub (a : UInt64) (j k : Nat) : adr a (j + k) - (8 * k).toUInt64 = adr a j := by
  rw [← adr_add, UInt64.add_sub_cancel]

omit P in
theorem rows_adr_step (a : UInt64) (b lw : Nat) :
    adr a (b + lw) + ((0 : UInt64) - (8 * lw).toUInt64 + (512 : Int64).toUInt64) = adr a (b + 64) := by
  rw [← adr_add, ← adr_add a b 64, show (512 : Int64).toUInt64 = (8 * 64 : Nat).toUInt64 from rfl]
  grind

omit P in
theorem Inv.rowsOf {t t' : QState} (h : Inv e t D W) (hm : t'.mem = t.mem)
    (hr : t'.reg .rdi = t.reg .rdi) : Inv e t' D W :=
  ⟨hr.trans h.rdi, fun a ha ↦ hm ▸ h.out a ha, fun k hk ↦ hm ▸ h.scr k hk,
    fun k hk ↦ hm ▸ h.dec k hk, fun k hk ↦ hm ▸ h.work k hk⟩

/-- The leading zeros of a row. -/
theorem rowsZeros_ok (hI : Inv e s D W) {b m : Nat} (h9 : s.reg .r9 = adr e.wk b)
    (hsi : s.reg .rsi = m.toUInt64) (hb : b + m ≤ workWords) :
    WP (.loop (.cmp .ne .rsi (.imm 0)) (blk [I (.storei (rw .r9 0) 0), I (.addi .r9 8),
      I (.subi .rsi 1)])) s (fun s' ↦ ∃ W', Inv e s' D W' ∧ (∀ t < m, W' (b + t) = 0) ∧
        Same (fun k ↦ b ≤ k ∧ k < b + m) W W' ∧ s'.reg .r9 = adr e.wk (b + m) ∧
        RegsFrame [.rsi, .r9] s s') F := by
  have hw := rows_workWords_lt
  let Iv : QState → Prop := fun t ↦ ∃ i, i ≤ m ∧ ∃ W', Inv e t D W' ∧ (∀ x < i, W' (b + x) = 0) ∧
    Same (fun k ↦ b ≤ k ∧ k < b + m) W W' ∧ t.reg .r9 = adr e.wk (b + i) ∧
    t.reg .rsi = (m - i).toUInt64 ∧ RegsFrame [.rsi, .r9] s t
  refine WP.loop Iv (fun t ↦ (t.reg .rsi).toNat) ⟨0, by omega, W, hI, fun x hx ↦ absurd hx (by omega),
    Same.refl _ _, by simpa using h9, by simpa using hsi, RegsFrame.refl s⟩ ?_ ?_
  · intro t ⟨i, hin, W', hIt, hz, hS, h9t, hst, hft⟩ hc
    have hlt : i < m := by
      rw [cond_ne_imm (k := 0) (K := 0) hst rfl (by omega) (by omega)] at hc
      simp at hc; omega
    refine blk_storei_work P hIt (k := b + i) (by rw [eval_rw t .r9 h9t, Nat.add_zero]) (by omega)
      fun t1 h1 r1 ↦ ?_
    step; step
    apply WP.blk_nil
    refine ⟨⟨i + 1, by omega, _, (h1.setReg (by decide) _).setReg (by decide) _, fun x hx ↦ ?_,
      hS.update (by omega) _, ?_, ?_, ?_⟩, ?_⟩
    · rw [Function.update_apply]
      by_cases h : b + x = b + i
      · rw [ite_yes h]; rfl
      · rw [ite_no h]; exact hz x (by omega)
    · simp [r1, h9t, show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r1, hst]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl, SphincsVerifier.toUInt64_sub (by omega),
        Nat.sub_sub]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.1, hr.2, r1, hft r (by simp [hr.1, hr.2])]
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r1, hst]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl, SphincsVerifier.toUInt64_sub (by omega),
        toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hin, W', hIt, hz, hS, h9t, hst, hft⟩ hc
    have hi : i = m := by
      rw [cond_ne_imm (k := 0) (K := 0) hst rfl (by omega) (by omega)] at hc
      simp at hc; omega
    subst hi
    exact ⟨W', hIt, hz, hS, h9t, hft⟩

/-- The words of a row. -/
theorem rowsWords_ok (hI : Inv e s D W) {b m p : Nat} (h9 : s.reg .r9 = adr e.wk b)
    (hsi : s.reg .rsi = m.toUInt64) (hp : s.reg .r15 = p.toUInt64) (hpL : p + 8 * m ≤ e.L)
    (hb : b + m ≤ workWords) :
    WP (.loop (.cmp .ne .rsi (.imm 0)) (blk [rdLE 8, I (.store (rw .r9 0) .rbx), I (.addi .r9 8),
      I (.subi .rsi 1)])) s (fun s' ↦ ∃ W', Inv e s' D W' ∧
        (∀ t < m, W' (b + t) = leAt e.B (p + 8 * t) 8) ∧
        Same (fun k ↦ b ≤ k ∧ k < b + m) W W' ∧ s'.reg .r9 = adr e.wk (b + m) ∧
        s'.reg .r15 = (p + 8 * m).toUInt64 ∧
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r9, .r15] s s') F := by
  have hw := rows_workWords_lt
  let Iv : QState → Prop := fun t ↦ ∃ i, i ≤ m ∧ ∃ W', Inv e t D W' ∧
    (∀ x < i, W' (b + x) = leAt e.B (p + 8 * x) 8) ∧
    Same (fun k ↦ b ≤ k ∧ k < b + m) W W' ∧ t.reg .r9 = adr e.wk (b + i) ∧
    t.reg .rsi = (m - i).toUInt64 ∧ t.reg .r15 = (p + 8 * i).toUInt64 ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r9, .r15] s t
  refine WP.loop Iv (fun t ↦ (t.reg .rsi).toNat) ⟨0, by omega, W, hI, fun x hx ↦ absurd hx (by omega),
    Same.refl _ _, by simpa using h9, by simpa using hsi, by simpa using hp, RegsFrame.refl s⟩ ?_ ?_
  · intro t ⟨i, hin, W', hIt, hz, hS, h9t, hst, hpt, hft⟩ hc
    have hlt : i < m := by
      rw [cond_ne_imm (k := 0) (K := 0) hst rfl (by omega) (by omega)] at hc
      simp at hc; omega
    apply WP.blk_cons
    refine WP.mono (rdLE_ok P hIt (n := 8) (by norm_num) le_rfl hpt (by omega))
      (fun t1 ⟨h1, hb1, hr1, hf1⟩ ↦ ?_) (fun _ h ↦ h)
    have h91 : t1.reg .r9 = adr e.wk (b + i) := by rw [hf1 .r9 (by simp), h9t]
    refine blk_store_work P h1 (k := b + i) (by rw [eval_rw t1 .r9 h91, Nat.add_zero]) (by omega)
      fun t2 h2 r2 ↦ ?_
    step; step
    apply WP.blk_nil
    refine ⟨⟨i + 1, by omega, _, (h2.setReg (by decide) _).setReg (by decide) _, fun x hx ↦ ?_,
      hS.update (by omega) _, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Function.update_apply]
      by_cases h : b + x = b + i
      · rw [ite_yes h, hb1, show x = i by omega]; rfl
      · rw [ite_no h]; exact hz x (by omega)
    · simp [r2, h91, show (8 : Int64).toUInt64 = 8 from rfl, adr_succ, Nat.add_assoc]
    · have hs1 : t1.reg .rsi = t.reg .rsi := hf1 .rsi (by simp)
      simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r2, hs1, hst]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        SphincsVerifier.toUInt64_sub (by omega), Nat.sub_sub]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, r2, hr1]
      congr 1
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, ite_false, r2]
      rw [hf1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2]),
        hft r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
          hr.2.2.2.2.2.2])]
    · have hs1 : t1.reg .rsi = t.reg .rsi := hf1 .rsi (by simp)
      simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, r2, hs1, hst]
      rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        SphincsVerifier.toUInt64_sub (by omega), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hin, W', hIt, hz, hS, h9t, hst, hpt, hft⟩ hc
    have hi : i = m := by
      rw [cond_ne_imm (k := 0) (K := 0) hst rfl (by omega) (by omega)] at hc
      simp at hc; omega
    subst hi
    exact ⟨W', hIt, hz, hS, h9t, hpt, hft⟩

/-- One row into the leaf at `r9`, its leading zeros first. -/
theorem rowsRow_ok (hI : Inv e s D W) {p lw rw b : Nat} (hp : s.reg .r15 = p.toUInt64)
    (hpL : p ≤ e.L) (h12 : s.reg .r12 = lw.toUInt64) (h11 : s.reg .r11 = rw.toUInt64)
    (h9 : s.reg .r9 = adr e.wk b) (hrw : rw ≤ lw) (hlw : lw ≤ 64) (hb : b + 64 ≤ workWords) :
    WP row s (fun s' ↦ p + 8 * rw ≤ e.L ∧ ∃ W', Inv e s' D W' ∧
      (∀ t < lw, W' (b + t) = if t < lw - rw then 0 else leAt e.B (p + 8 * (t - (lw - rw))) 8) ∧
      Same (fun k ↦ b ≤ k ∧ k < b + lw) W W' ∧ s'.reg .r15 = (p + 8 * rw).toUInt64 ∧
      s'.reg .r9 = adr e.wk (b + 64) ∧
      (s'.reg .r8 = 0 ↔ s.reg .r8 = 0 ∧ (rw = 0 ∨ leAt e.B p 8 = 0)) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r15] s s')
      (fun s' ↦ e.L < p + 8 * rw ∧ Kept e s') := by
  have hw := rows_workWords_lt
  unfold row
  step; step
  apply WP.blk_cons
  refine WP.mono (needR_ok P (hI.setReg (d := .rbx) (by decide) _) (p := p) (n := 8 * rw)
    (r := .rbx) (by decide) (by simpa using hp) hpL
    (by simp only [QState.setReg_reg, ite_true]; rw [h11, rows_shl3 (by omega)]) (by omega))
    (fun s1 ⟨hok, h1, hf1⟩ ↦ ?_) (fun _ h ↦ h)
  have hr1 : ∀ r, r ≠ .rax → r ≠ .rbx → s1.reg r = s.reg r := fun r ha hb' ↦ by
    rw [hf1 r (by simpa using ha)]; simp [hb']
  step; step
  apply WP.blk_cons
  refine WP.mono (rowsZeros_ok P (h1.setReg (d := .rsi) (by decide) _) (b := b) (m := lw - rw)
    (by simp only [QState.setReg_reg, reduceCtorEq, ite_false]; rw [hr1 .r9 (by decide) (by decide), h9])
    (by simp only [QState.setReg_reg, ite_true]
        rw [hr1 .r12 (by decide) (by decide), hr1 .r11 (by decide) (by decide), h12, h11,
          SphincsVerifier.toUInt64_sub hrw])
    (by omega)) (fun s2 ⟨W2, h2, hz2, hS2, h92, hf2⟩ ↦ ?_) (fun _ h ↦ h)
  have hr2 : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rsi → r ≠ .r9 → s2.reg r = s.reg r :=
    fun r ha hb' hsi h9' ↦ by
      rw [hf2 r (by simp [hsi, h9']), QState.setReg_reg, ite_no hsi, hr1 r ha hb']
  step
  apply WP.blk_cons
  refine WP.mono (rowsWords_ok P (h2.setReg (d := .rsi) (by decide) _) (b := b + (lw - rw))
    (m := rw) (p := p) (by simpa using h92)
    (by simp only [QState.setReg_reg, ite_true]; rw [hr2 .r11 (by decide) (by decide) (by decide)
      (by decide), h11])
    (by simp only [QState.setReg_reg, reduceCtorEq, ite_false]; rw [hr2 .r15 (by decide)
      (by decide) (by decide) (by decide), hp])
    hok (by omega)) (fun s3 ⟨W3, h3, hw3, hS3, h93, hp3, hf3⟩ ↦ ?_) (fun _ h ↦ h)
  have hr3 : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r9, .r15] → s3.reg r = s.reg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ha, hb', hc, hd, hsi, h9', h15⟩ := hr
    rw [hf3 r (by simp [ha, hb', hc, hd, hsi, h9', h15]), QState.setReg_reg, ite_no hsi,
      hr2 r ha hb' hsi h9']
  have h113 : s3.reg .r11 = rw.toUInt64 := by rw [hr3 .r11 (by simp), h11]
  have h123 : s3.reg .r12 = lw.toUInt64 := by rw [hr3 .r12 (by simp), h12]
  have h83 : s3.reg .r8 = s.reg .r8 := hr3 .r8 (by simp)
  apply WP.blk_cons
  refine WP.mono (P := fun t ↦ t.mem = s3.mem ∧ RegsFrame [.rax, .rbx, .r8] s3 t ∧
      (t.reg .r8 = 0 ↔ s.reg .r8 = 0 ∧ (rw = 0 ∨ leAt e.B p 8 = 0))) ?_
    (fun t ⟨hm, hft, h8⟩ ↦ ?_) (fun _ h ↦ h)
  · apply WP.ite
    rw [cond_ne_imm (k := 0) (K := 0) h113 rfl (by omega) (by omega)]
    by_cases h0 : rw = 0
    · rw [ite_no (by simpa using h0)]
      exact WP.skip ⟨rfl, RegsFrame.refl _, by simp [h83, h0]⟩
    · rw [ite_yes (by simpa using h0)]
      step; step; step; step
      refine blk_load_work ((h3.setReg (d := .rax) (by decide) _).setReg (d := .rbx) (by decide) _)
        (k := b + (lw - rw)) ?_ (by omega) ?_
      · simp only [eval_rw', QState.setReg_reg, ite_true, reduceCtorEq, ite_false]
        rw [h93, h113, rows_shl3 (by omega), rows_adr_sub]
        simp
      step
      apply WP.blk_nil
      refine ⟨by simp, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.1, hr.2.1, hr.2.2]
      · have := hw3 0 (by omega)
        simp only [Nat.add_zero, Nat.mul_zero] at this
        simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, UInt64.or_eq_zero_iff,
          h83, this, h0, false_or]
  · step; step; step; step; step
    apply WP.blk_nil
    have h9t : t.reg .r9 = adr e.wk (b + lw) := by
      rw [hft .r9 (by simp), h93, show b + (lw - rw) + rw = b + lw by omega]
    have h12t : t.reg .r12 = lw.toUInt64 := by rw [hft .r12 (by simp), h123]
    refine ⟨hok, W3, ((h3.rowsOf hm (hft .rdi (by simp))).setReg (by decide) _).setReg
      (by decide) _, fun x hx ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_cases hx' : x < lw - rw
      · rw [ite_yes hx', hS3 _ (by omega)]
        exact hz2 x hx'
      · rw [ite_no hx', show b + x = b + (lw - rw) + (x - (lw - rw)) by omega]
        exact hw3 _ (by omega)
    · exact (hS2.mono fun k hk ↦ by omega).trans (hS3.mono fun k hk ↦ by omega)
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false]
      rw [hft .r15 (by simp), hp3]
    · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false]
      rw [h9t, h12t, rows_shl3 (by omega), rows_adr_step]
    · simpa using h8
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.1, hr.2.2.2.2.2.2.1, ite_false]
      rw [hft r (by simp [hr.1, hr.2.1, hr.2.2.2.2.2.1]), hr3 r (by simp [hr.1, hr.2.1, hr.2.2.1,
        hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2])]

/-- **`rows`**: the rows at the distinct positions into their leaves, as `rdRows` reads them, or a
failure where `rdRows` gives `none` or every row's first word is zero. -/
theorem rows_ok (hI : Inv e s D W) {c lw rw n : Nat} (hp : s.reg .r15 = c.toUInt64)
    (hc : c ≤ e.L) (hr12 : s.reg .r12 = lw.toUInt64) (hr11 : s.reg .r11 = rw.toUInt64)
    (hr10 : s.reg .r10 = n.toUInt64) (hrw : rw ≤ lw) (hlw : lw ≤ wireMaxLeafWords)
    (hn : n ≤ wireMaxQueries) :
    WP rows s (fun s' ↦ ∃ rws c', rdRows e.B rw n c = some (rws, c') ∧
      ¬(0 < rw ∧ ∀ r ∈ rws, r.getD 0 0 = 0) ∧ ∃ W', Inv e s' D W' ∧
      LeafTab W' (rws.map fun r ↦ paddedLeaf r lw) lw ∧
      Same (fun k ↦ wLeaf ≤ k ∧ k < wLeaf + wireMaxLeafWords * wireMaxQueries) W W' ∧
      s'.reg .r15 = c'.toUInt64 ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .rbp, .r15] s s')
      (fun s' ↦ (rdRows e.B rw n c = none ∨ ∃ rws c', rdRows e.B rw n c = some (rws, c') ∧
        0 < rw ∧ ∀ r ∈ rws, r.getD 0 0 = 0) ∧ Kept e s') := by
  have hw := rows_workWords_lt
  have hBl := B_length P
  have hlw' : lw ≤ 64 := hlw
  have hn' : n ≤ 256 := hn
  have hWQ : wireMaxLeafWords * wireMaxQueries = 64 * 256 := rfl
  have hLW : wLeaf + 64 * 256 = workWords := rfl
  unfold rows
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  step; step; step
  apply WP.blk_cons
  let Iv : QState → Prop := fun t ↦ ∃ i, i ≤ n ∧ c + 8 * rw * i ≤ e.L ∧ ∃ W', Inv e t D W' ∧
    (∀ j < i, ∀ x < lw, W' (wLeaf + 64 * j + x) =
      if x < lw - rw then 0 else leAt e.B (c + 8 * rw * j + 8 * (x - (lw - rw))) 8) ∧
    Same (fun k ↦ wLeaf ≤ k ∧ k < wLeaf + wireMaxLeafWords * wireMaxQueries) W W' ∧
    t.reg .r15 = (c + 8 * rw * i).toUInt64 ∧ t.reg .r9 = adr e.wk (wLeaf + 64 * i) ∧
    t.reg .rbp = (n - i).toUInt64 ∧
    (t.reg .r8 = 0 ↔ ∀ j < i, rw = 0 ∨ leAt e.B (c + 8 * rw * j) 8 = 0) ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .rbp, .r15] s t
  refine WP.loop Iv (fun t ↦ (t.reg .rbp).toNat) ⟨0, by omega, by simpa using hc, W, hI.setReg
    (by decide) _ |>.setReg (by decide) _ |>.setReg (by decide) _, fun j hj ↦ absurd hj (by omega),
    Same.refl _ _, by simpa using hp, by simp [wd_toUInt64, adr], by simpa using hr10,
    by simp only [QState.setReg_reg, ite_true]; exact ⟨fun _ j hj ↦ absurd hj (by omega),
      fun _ ↦ rfl⟩, ?_⟩ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]
  · intro t ⟨i, hin, hci, W', hIt, hlv, hS, h15, h9, hbp, h8, hft⟩ hcnd
    have hlt : i < n := by
      rw [cond_ne_imm (k := 0) (K := 0) hbp rfl (by omega) (by omega)] at hcnd
      simp at hcnd; omega
    have hmul : 8 * rw * (i + 1) ≤ 8 * rw * n := Nat.mul_le_mul_left _ hlt
    apply WP.blk_cons
    refine WP.mono (rowsRow_ok P hIt (p := c + 8 * rw * i) (lw := lw) (rw := rw)
      (b := wLeaf + 64 * i) h15 hci (by rw [hft .r12 (by simp), hr12])
      (by rw [hft .r11 (by simp), hr11]) h9 hrw hlw' (by omega))
      (fun t1 ⟨hok, W1, h1, hv1, hS1, h151, h91, h81, hf1⟩ ↦ ?_)
      (fun t1 ⟨hfail, hk⟩ ↦ ⟨Or.inl ?_, hk⟩)
    swap
    · rw [rows_rdRows e.B rw n c (hBl ▸ hc), ite_no (by rw [hBl, Nat.mul_succ] at *; omega)]
    step
    apply WP.blk_nil
    refine ⟨⟨i + 1, by omega, by rw [Nat.mul_succ]; omega, W1, h1.setReg (by decide) _,
      fun j hj x hx ↦ ?_, hS.trans (hS1.mono fun k hk ↦ by omega), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hS1 _ (by omega)]
        exact hlv j hj x hx
      · exact hv1 x hx
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, h151, Nat.mul_succ, Nat.add_assoc]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, h91]
      congr 1
    · simp only [QState.setReg_reg, ite_true]
      rw [hf1 .rbp (by simp), hbp, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        SphincsVerifier.toUInt64_sub (by omega), Nat.sub_sub]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false, h81, h8]
      constructor
      · rintro ⟨ha, hb⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ha j hj
        · exact hb
      · intro ha
        exact ⟨fun j hj ↦ ha j (by omega), ha i (by omega)⟩
    · intro r hr
      have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [QState.setReg_reg, hr'.2.2.2.2.2.2.2.1, ite_false]
      rw [hf1 r (by simp [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1, hr'.2.2.2.2.2.1,
        hr'.2.2.2.2.2.2.1, hr'.2.2.2.2.2.2.2.2]), hft r hr]
    · simp only [QState.setReg_reg, ite_true]
      rw [hf1 .rbp (by simp), hbp, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        SphincsVerifier.toUInt64_sub (by omega), toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hin, hci, W', hIt, hlv, hS, h15, h9, hbp, h8, hft⟩ hcnd
    have hi : i = n := by
      rw [cond_ne_imm (k := 0) (K := 0) hbp rfl (by omega) (by omega)] at hcnd
      simp at hcnd; omega
    subst hi
    have hrd := rows_rdRows e.B rw i c (hBl ▸ hc)
    rw [ite_yes (by rw [hBl]; exact hci)] at hrd
    have hall : (∀ r ∈ (List.range i).map (fun j ↦ rowsRowAt e.B rw (c + 8 * rw * j)),
        r.getD 0 0 = 0) ↔ ∀ j < i, rw = 0 ∨ leAt e.B (c + 8 * rw * j) 8 = 0 := by
      simp only [List.forall_mem_map, List.mem_range, rows_getD0]
    have hleaf : LeafTab W' (((List.range i).map fun j ↦ rowsRowAt e.B rw (c + 8 * rw * j)).map
        fun r ↦ paddedLeaf r lw) lw := fun j hj x hx ↦ by
      simp only [List.getElem_map, List.getElem_range]
      rw [rows_padded e.B hrw hx]
      exact hlv j (by simpa using hj) x hx
    have h11t : t.reg .r11 = rw.toUInt64 := by rw [hft .r11 (by simp), hr11]
    apply WP.blk_cons
    apply WP.ite
    rw [cond_ne_imm (k := 0) (K := 0) h11t rfl (by omega) (by omega)]
    by_cases h0 : rw = 0
    · rw [ite_no (by simpa using h0)]
      exact WP.skip (WP.blk_nil ⟨_, _, hrd, by omega, W', hIt, hleaf, hS, h15, hft⟩)
    · rw [ite_yes (by simpa using h0)]
      refine wp_failIf (fun hc8 ↦ ⟨Or.inr ⟨_, _, hrd, by omega, hall.2 (h8.1 ?_)⟩, hIt.kept⟩)
        (fun hc8 ↦ WP.blk_nil ⟨_, _, hrd, fun ⟨_, ha⟩ ↦ ?_, W', hIt, hleaf, hS, h15, hft⟩)
      · have : (t.reg .r8 == (0 : UInt64)) = true := hc8
        simpa using this
      · have : (t.reg .r8 == (0 : UInt64)) = false := hc8
        simp only [beq_eq_false_iff_ne] at this
        exact this (h8.2 (hall.1 ha))

end Run

end NativeVm.Wire
