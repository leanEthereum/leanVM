module

public import NativeVm.Field.Fold

/-!
# The multilinear extension at a point

`emle`: `A := multilinearEval mle point`, the table `mle` at `r13` (`r15` elements, `2^|point|` of
them, as `multilinear_eval` requires), the point at `rsi`. Each coordinate folds the table once
(`efold`) into the work area at `r14`: the first from `r13`, the others in place, so the table
itself is only read. The half length is in `rbp`; the result is the work area's first element (the
table's when the point is empty).
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters LeanVM.Protocol.Verifier

/-- The table after the first `q` coordinates. -/
def mleCur (mle point : List E) (q : Nat) : List E :=
  (point.take q).foldl (fun cur r ↦ foldPairs r cur) mle

theorem mleCur_zero (mle point : List E) : mleCur mle point 0 = mle := by
  simp [mleCur]

theorem mleCur_succ (mle point : List E) {q : Nat} (hq : q < point.length) :
    mleCur mle point (q + 1) = foldPairs (point.getD q 0) (mleCur mle point q) := by
  rw [mleCur, mleCur, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hq,
    ← List.getElem_eq_getD 0]
  rfl

theorem mleCur_length {mle point : List E} (hpow : mle.length = 2 ^ point.length) :
    ∀ q ≤ point.length, (mleCur mle point q).length = 2 ^ (point.length - q)
  | 0, _ => by rw [mleCur_zero, hpow, Nat.sub_zero]
  | q + 1, hq => by
    rw [mleCur_succ _ _ (by omega), foldPairs_length, mleCur_length hpow q (by omega),
      show point.length - q = point.length - (q + 1) + 1 by omega, pow_succ, Nat.mul_div_cancel]
    norm_num

theorem mleCur_last (mle point : List E) : mleCur mle point point.length =
    point.foldl (fun cur r ↦ foldPairs r cur) mle := by
  rw [mleCur, List.take_length]

/-- `A := multilinearEval mle point`: `mle` at `r13`, `r15` elements, the point at `rsi`, the work
area at `r14`. -/
def emle : Stmt := blk [
  I (.mov .rbp .r15), I (.shri .rbp 1),
  .loop (.test false .rbp (.reg .rbp)) (blk [
    I (.load .r11 (at_ .rsi 0)), I (.load .r12 (at_ .rsi 8)), I (.addi .rsi 16),
    I (.mov .r15 .rbp), efold,
    I (.mov .r13 .rbp), I (.shli .r13 4), I (.sub .r14 .r13), I (.mov .r13 .r14),
    I (.shri .rbp 1)]),
  I (.load .r9 (at_ .r13 0)), I (.load .r10 (at_ .r13 8))]

theorem shr1_toUInt64 {c : Nat} (hc : c < 2 ^ 64) : c.toUInt64 >>> 1 = (c / 2).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, toNat_toUInt64 hc, toNat_toUInt64 (by omega)]
  simp [Nat.shiftRight_eq_div_pow]

theorem shl4 (x : UInt64) : x <<< 4 = x * 16 := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_mul, Nat.shiftLeft_eq]

theorem ew_back (p : UInt64) (c : Nat) : ew p (2 * c) - c.toUInt64 <<< 4 = p := by
  rw [shl4]
  uring

variable {s : QState} {F : QState → Prop}

/-- **`emle` computes `multilinearEval`.** It writes the work area's first `|mle|` words (none
when the point is empty) and no other memory. -/
theorem emle_spec {mle point : List E} {src work pt : UInt64} (h13 : s.reg .r13 = src)
    (h14 : s.reg .r14 = work) (hsi : s.reg .rsi = pt) (hm : EArr s.mem src mle)
    (hp : EArr s.mem pt point) (hn : s.reg .r15 = mle.length.toUInt64)
    (hpow : mle.length = 2 ^ point.length) (hlen : point.length < 60)
    (hdom : ∀ k < 2 * (mle.length / 2), (s.mem (ew work k)).isSome)
    (hsep : FoldSep src work mle.length)
    (hpt : ∀ k < 2 * (mle.length / 2), ∀ j < 2 * point.length, ew work k ≠ ew pt j) :
    WP emle s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = multilinearEval mle point ∧
      (∀ a, (∀ k < 2 * (mle.length / 2), a ≠ ew work k) → s'.mem a = s.mem a) ∧
      RegsFrame arrRegs s s') F := by
  set m := point.length with hm_def
  set W := 2 * (mle.length / 2) with hW_def
  have hpm : 2 ^ m < 2 ^ 60 := Nat.pow_lt_pow_right (by norm_num) hlen
  have hcur : ∀ q ≤ m, (mleCur mle point q).length ≤ mle.length := fun q hq ↦ by
    rw [mleCur_length hpow q hq, hpow]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [EArr_iff_EW] at hp
  unfold emle
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ q ≤ m,
      t.reg .rbp = ((mleCur mle point q).length / 2).toUInt64 ∧ t.reg .rsi = ew pt (2 * q) ∧
      t.reg .r13 = (if q = 0 then src else work) ∧ t.reg .r14 = work ∧
      EArr t.mem (t.reg .r13) (mleCur mle point q) ∧
      (∀ j < m, EW t.mem pt j (point.getD j 0)) ∧
      (∀ a, (∀ k < W, a ≠ ew work k) → t.mem a = s.mem a) ∧
      (∀ k < W, (t.mem (ew work k)).isSome) ∧ RegsFrame arrRegs s t)
    (fun t ↦ (t.reg .rbp).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, hp, fun _ _ ↦ rfl, hdom, by rf_tac⟩ <;> rsimp
    · rw [hn, mleCur_zero, shr1_toUInt64 (by omega)]
    · rw [hsi, Nat.mul_zero, ew_zero]
    · exact h13
    · exact h14
    · rw [h13, mleCur_zero]
      exact hm
  · intro t ⟨q, hq, tbp, tsi, t13, t14, hC, hP, hF, hW, hf⟩ hc
    have hne : t.reg .rbp ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    set cur := mleCur mle point q with hcur_def
    have hlc : cur.length = 2 ^ (m - q) := mleCur_length hpow q hq
    have hqm : q < m := by
      by_contra h
      apply hne
      rw [tbp, hlc, show m - q = 0 by omega]
      rfl
    have hcl : cur.length ≤ mle.length := hcur q hq
    obtain ⟨p0, p1⟩ := hP q hqm
    refine WP.load_at (by
      rsimp; rw [tsi, show ew pt (2 * q) + 0 = ew pt (2 * q) by uring]; exact p0) ?_
    refine WP.load_at (by
      rsimp; rw [tsi, show ew pt (2 * q) + 8 = ew pt (2 * q + 1) by uring]; exact p1) ?_
    fstep; fstep
    set c := cur.length / 2 with hc_def
    have hcW : 2 * c ≤ W := by omega
    refine WP.then (efold_spec (xs := cur) (src := t.reg .r13) (dst := work) (by rsimp)
      (by rsimp; exact t14)
      (by rsimp; exact hC) (by rsimp; exact tbp) (by omega)
      (fun k hk ↦ by rsimp; exact hW k (by omega)) ?_) fun t₁ ⟨e1, e2, e3, _, e5, e6⟩ ↦ ?_
    · by_cases h0 : q = 0
      · rw [t13, ite_eq_left h0]
        subst h0
        rw [hcur_def, mleCur_zero]
        exact hsep
      · rw [t13, ite_eq_right h0]
        exact FoldSep.self work (by omega)
    rsimp at e1 e2 e3
    rw [eOf_lanes] at e1
    have k : ∀ r ∉ foldRegs, r ≠ .r11 → r ≠ .r12 → r ≠ .rsi → t₁.reg r = t.reg r :=
      fun r hr a b c ↦ by
        rw [e6 r hr]
        have : r ≠ .r15 := fun h ↦ hr (by simp [h])
        simp [QState.setReg_reg, a, b, c, this]
    have ksi : t₁.reg .rsi = t.reg .rsi + 16 := by rw [e6 .rsi (by decide)]; rsimp
    have kbp : t₁.reg .rbp = c.toUInt64 := by
      rw [k .rbp (by decide) (by decide) (by decide) (by decide), tbp]
    have hcpos : c ≠ 0 := fun h ↦ hne (by rw [tbp, h]; rfl)
    have hcl2 : c < 2 ^ 64 := by omega
    fstep; fstep; fstep; fstep; fstep
    fdone
    rw [kbp, e5, ew_back, shr1_toUInt64 hcl2]
    -- Memory outside the fold's words is kept.
    have hkeep : ∀ a, (∀ k < 2 * c, a ≠ ew work k) → t₁.mem a = t.mem a := fun a ha ↦ by
      rw [e2 a ha]
    have hlc' : (mleCur mle point (q + 1)).length = c := by
      rw [mleCur_succ _ _ hqm, foldPairs_length]
    refine ⟨⟨q + 1, by omega, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hlc']
    · rw [ksi, tsi]; uring
    · simp
    · rw [mleCur_succ _ _ hqm]
      exact e1
    · intro j hj
      obtain ⟨d0, d1⟩ := hP j hj
      refine ⟨?_, ?_⟩
      · rw [hkeep _ fun k hk ↦ Ne.symm (hpt k (by omega) (2 * j) (by omega))]
        exact d0
      · rw [hkeep _ fun k hk ↦ Ne.symm (hpt k (by omega) (2 * j + 1) (by omega))]
        exact d1
    · intro a ha
      rw [hkeep a fun k hk ↦ ha k (by omega)]
      exact hF a ha
    · intro k' hk'
      by_cases hk2 : k' < 2 * c
      · exact e3 k' hk2
      · rw [hkeep _ fun k hk ↦ ew_ne _ (by omega) (by omega) (by omega)]
        exact hW k' hk'
    · intro r hr
      have hr' := hr
      simp only [arrRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13', h14'⟩ := hr'
      have hk : r ∉ foldRegs := by simp [foldRegs, *]
      simp only [QState.setReg_reg, h6, h12, h13', ↓reduceIte]
      rw [k r hk h10 h11 h5]
      exact hf r hr
    · rw [tbp, toNat_toUInt64 (by omega), toNat_toUInt64 hcl2]
      omega
  · intro t ⟨q, hq, tbp, _, _, _, hC, _, hF, _, hf⟩ hc
    have h0 : t.reg .rbp = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hlc : (mleCur mle point q).length = 2 ^ (m - q) := mleCur_length hpow q hq
    have hpq : 2 ^ (m - q) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hqm : q = m := by
      have := toUInt64_inj (a := (mleCur mle point q).length / 2) (b := 0) (by omega)
        (by norm_num) (by rw [← tbp, h0]; rfl)
      rw [hlc] at this
      by_contra hne
      have : 2 ≤ 2 ^ (m - q) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (m - q) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hqm
    rw [EArr_iff_EW, hlc, Nat.sub_self, pow_zero] at hC
    obtain ⟨c0, c1⟩ := hC 0 Nat.one_pos
    refine WP.load_at (by
      rsimp; rw [show t.reg .r13 + 0 = ew (t.reg .r13) (2 * 0) by uring]; exact c0) ?_
    refine WP.load_at (by
      rsimp; rw [show t.reg .r13 + 8 = ew (t.reg .r13) (2 * 0 + 1) by uring]; exact c1) ?_
    fdone
    refine ⟨?_, hF, by rf_tac; exact hf⟩
    rw [eOf_lanes, multilinearEval, ← mleCur_last]
    cases mleCur mle point point.length <;> rfl

end NativeVm.Field
