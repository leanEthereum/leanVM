module

public import NativeVm.Field
public import NativeVm.Equiv.Field
public import NativeVm.Code.Phase7.RingMath

/-!
# The loops ring switching's code shares

Over lists of `E` in memory (`EArr`), a pointer advancing 16 bytes a pass (`ew p (2 i)` at pass
`i`) and a count counting down:

* `eqLoop`: `A := A · eqEval xs ys`, `xs` at `r13`, `ys` at `r14`, `r15` pairs; it leaves `r13`,
  `r14` past the lists (`eeqEval`'s loop with its end pointers);
* `selLoop`: `A := A · eqEval (selectorPoint sel n) ys`, `ys` at `r14`, `n` in `rbp`, `sel` in
  `rsi`, a bit a pass from the lowest;
* `shiftLoop`: `rsi := rsi >>> rdx`, a bit a pass (so any count, `64` and more giving `0`);
* `sqLoop`: each element at `r13` squared in place, `r15` of them;
* `copyLoop`: `r15` elements from `r13` to `r8`.

`WP.blk_map` runs a block of statements one per element of a list by a fold, for the unrolled
loops.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier

variable {s : QState} {F : QState → Prop}

/-! ## Unrolled loops -/

/-- **A block of one statement per element** of `l`, each taking the fold one step. -/
theorem WP.blk_map {α β : Type} (f : α → Stmt) (Inv : β → QState → Prop) (step : β → α → β)
    (hstep : ∀ a b s, Inv b s → WP (f a) s (Inv (step b a)) F) :
    ∀ (l : List α) (b : β) (s : QState), Inv b s → WP (blk (l.map f)) s (Inv (l.foldl step b)) F
  | [], _, _, h => WP.blk_nil h
  | a :: l, b, s, h => WP.blk_cons (WP.mono (hstep a b s h)
      (fun s₁ h₁ ↦ WP.blk_map f Inv step hstep l (step b a) s₁ h₁) fun _ h ↦ h)

/-! ## Counters -/

theorem cond_test_true {r : Reg64} {t : QState} (h : (Cond.test false r (.reg r)).eval t = true) :
    t.reg r ≠ 0 := by simpa [Cond.eval, Rhs.eval] using h

theorem cond_test_false {r : Reg64} {t : QState} (h : (Cond.test false r (.reg r)).eval t = false) :
    t.reg r = 0 := by simpa [Cond.eval, Rhs.eval] using h

theorem cnt_lt {n i : Nat} (h : (n - i).toUInt64 ≠ 0) : i < n := by
  by_contra hc
  exact h (by rw [show n - i = 0 by omega]; rfl)

theorem cnt_eq {n i : Nat} (hn : n < 2 ^ 64) (hi : i ≤ n) (h : (n - i).toUInt64 = 0) : i = n := by
  have := toUInt64_inj (a := n - i) (b := 0) (by omega) (by norm_num) h
  omega

theorem cnt_succ {n i : Nat} (hi : i < n) : (n - i).toUInt64 - 1 = (n - (i + 1)).toUInt64 := by
  rw [show n - i = n - (i + 1) + 1 by omega, toUInt64_succ_sub]

theorem cnt_dec {n i : Nat} (hn : n < 2 ^ 64) (hi : i < n) :
    (n - (i + 1)).toUInt64.toNat < (n - i).toUInt64.toNat := by
  rw [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
  omega

theorem ew_step (p : UInt64) (i : Nat) : ew p (2 * i) + 16 = ew p (2 * (i + 1)) := by uring

theorem ew_one (p : UInt64) (i : Nat) : ew p (2 * i) + 8 = ew p (2 * i + 1) := by uring

theorem ew_zero' (p : UInt64) (i : Nat) : ew p (2 * i) + 0 = ew p (2 * i) := UInt64.add_zero _

/-! ## Lists -/

theorem take_succ_getD (l : List E) {i : Nat} (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

theorem eqEval_take_succ (xs ys : List E) {i : Nat} (hx : i < xs.length) (hy : i < ys.length) :
    eqEval (xs.take (i + 1)) (ys.take (i + 1)) =
      eqEval (xs.take i) (ys.take i) * (1 + xs.getD i 0 + ys.getD i 0) := by
  rw [take_succ_getD xs hx, take_succ_getD ys hy, eqEval_take_drop i,
    List.take_left' (by simp; omega), List.take_left' (by simp; omega),
    List.drop_left' (by simp; omega), List.drop_left' (by simp; omega), eqEval_cons',
    eqEval_nil_left, mul_one]

theorem selectorPoint_getD (sel n i : Nat) (hi : i < n) :
    (selectorPoint sel n).getD i 0 = eOfNat ((sel >>> i) % 2) := by
  simp [selectorPoint, List.getD_eq_getElem?_getD, hi]

/-- The low bit of a word, in limb `0`, is `eOfNat` of it. -/
theorem eOfNat_eq (n : Nat) : eOfNat n = eOf n.toUInt64 0 := by
  rw [← NativeVm.Equiv.EW.toE_ofNat]
  rfl

/-- The low bit of a word, in limb `0`, is `eOfNat` of it. -/
theorem eOf_and_one (w : UInt64) : eOf (w &&& 1) 0 = eOfNat (w.toNat % 2) := by
  rw [eOfNat_eq]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, toNat_toUInt64 (by omega)]
  simp [Nat.and_one_is_mod]

theorem eOf_xor_lo (a b c : UInt64) : eOf (a ^^^ b) c = eOf a c + eOf b 0 := by
  rw [← eOf_add, UInt64.xor_zero]

/-! ## `eqLoop` -/

/-- `A := A · eqEval xs ys`, `xs` at `r13`, `ys` at `r14`, `r15` pairs. -/
def eqLoop : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .r11 (at_ .r13 0)), I (.load .rdx (at_ .r14 0)), I (.xor .r11 .rdx),
  I (.xori .r11 1),
  I (.load .r12 (at_ .r13 8)), I (.load .rdx (at_ .r14 8)), I (.xor .r12 .rdx),
  emul,
  I (.addi .r13 16), I (.addi .r14 16), I (.subi .r15 1)])

/-- **`eqLoop` multiplies by `eqEval`**, leaving `r13` and `r14` past the lists. -/
theorem eqLoop_spec {xs ys : List E} {p q : UInt64} (h13 : s.reg .r13 = p) (h14 : s.reg .r14 = q)
    (hx : EArr s.mem p xs) (hy : EArr s.mem q ys) (hl : ys.length = xs.length)
    (hn : s.reg .r15 = xs.length.toUInt64) (hlen : xs.length < 2 ^ 60) :
    WP eqLoop s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
        eOf (s.reg .r9) (s.reg .r10) * eqEval xs ys ∧
      s'.reg .r13 = ew p (2 * xs.length) ∧ s'.reg .r14 = ew q (2 * xs.length) ∧
      s'.mem = s.mem ∧ RegsFrame eqRegs s s') F := by
  set n := xs.length with hn_def
  set A0 := eOf (s.reg .r9) (s.reg .r10)
  rw [EArr_iff_EW] at hx hy
  unfold eqLoop
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r13 = ew p (2 * i) ∧ t.reg .r14 = ew q (2 * i) ∧
      t.reg .r15 = (n - i).toUInt64 ∧
      eOf (t.reg .r9) (t.reg .r10) = A0 * eqEval (xs.take i) (ys.take i) ∧ t.mem = s.mem ∧
      RegsFrame eqRegs s t)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, rfl, RegsFrame.refl _ _⟩
    · rw [h13, Nat.mul_zero, ew_zero]
    · rw [h14, Nat.mul_zero, ew_zero]
    · rw [hn, Nat.sub_zero]
    · simp only [List.take_zero, eqEval_nil_left, mul_one]; rfl
  · intro t ⟨i, hi, t13, t14, t15, hI, hm, hf⟩ hc
    have hin : i < n := cnt_lt (t15 ▸ cond_test_true hc)
    obtain ⟨x0, x1⟩ := hx i hin
    obtain ⟨y0, y1⟩ := hy i (by omega)
    refine WP.load_at (by rw [hm, t13, int64Zero_toUInt64, ew_zero']; exact x0) ?_
    refine WP.load_at (by rsimp; rw [hm, t14, ew_zero']; exact y0) ?_
    fstep; fstep
    refine WP.load_at (by rsimp; rw [hm, t13, ew_one]; exact x1) ?_
    refine WP.load_at (by rsimp; rw [hm, t14, ew_one]; exact y1) ?_
    fstep
    refine WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1
    have k : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → t₁.reg r = t.reg r := fun r hr h11 h12 ↦ by
      rw [e3 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.2.2.2.1, h11, h12]
    fstep; fstep; fstep; fdone
    refine ⟨⟨i + 1, hin, ?_, ?_, ?_, ?_, e2.trans hm, ?_⟩, ?_⟩
    · rw [k .r13 (by decide) (by decide) (by decide), t13, ew_step]
    · rw [k .r14 (by decide) (by decide) (by decide), t14, ew_step]
    · rw [k .r15 (by decide) (by decide) (by decide), t15, cnt_succ hin]
    · rw [e1, hI, eOf_xor_one, eOf_add, eOf_lanes, eOf_lanes,
        eqEval_take_succ xs ys hin (by omega)]
      ring
    · intro r hr
      have hr' := hr
      simp only [eqRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨_, _, _, _, _, _, _, h11, h12, h13, h14, h15⟩ := hr'
      have hk : r ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setReg_reg, h13, h14, h15, ↓reduceIte, k r hk h11 h12]
      exact hf r hr
    · rw [k .r15 (by decide) (by decide) (by decide), t15, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, t13, t14, t15, hI, hm, hf⟩ hc
    obtain rfl : i = n := cnt_eq (by omega) hi (t15 ▸ cond_test_false hc)
    refine ⟨?_, t13, t14, hm, hf⟩
    rw [hI, List.take_of_length_le (le_refl _), List.take_of_length_le (by omega)]

/-! ## `selLoop` -/

/-- `A := A · eqEval (selectorPoint rsi rbp) ys`, `ys` at `r14`. -/
def selLoop : Stmt := .loop (.test false .rbp (.reg .rbp)) (blk [
  I (.load .r11 (at_ .r14 0)), I (.mov .rax .rsi), I (.andi .rax 1), I (.xor .r11 .rax),
  I (.xori .r11 1), I (.load .r12 (at_ .r14 8)), emul,
  I (.addi .r14 16), I (.shri .rsi 1), I (.subi .rbp 1)])

/-- The registers `selLoop` writes. -/
abbrev selRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r14]

theorem toNat_shr_one (w : UInt64) : (w >>> 1).toNat = w.toNat >>> 1 := by
  rw [UInt64.toNat_shiftRight]
  rfl

/-- **`selLoop` multiplies by a selector's equality weight.** -/
theorem selLoop_spec {ys : List E} {q : UInt64} (h14 : s.reg .r14 = q) (hy : EArr s.mem q ys)
    (hn : s.reg .rbp = ys.length.toUInt64) (hlen : ys.length < 2 ^ 60) :
    WP selLoop s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
        eOf (s.reg .r9) (s.reg .r10) * eqEval (selectorPoint (s.reg .rsi).toNat ys.length) ys ∧
      s'.mem = s.mem ∧ RegsFrame selRegs s s') F := by
  set n := ys.length with hn_def
  set A0 := eOf (s.reg .r9) (s.reg .r10)
  set sel := (s.reg .rsi).toNat
  rw [EArr_iff_EW] at hy
  unfold selLoop
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r14 = ew q (2 * i) ∧ t.reg .rbp = (n - i).toUInt64 ∧
      (t.reg .rsi).toNat = sel >>> i ∧
      eOf (t.reg .r9) (t.reg .r10) = A0 * eqEval ((selectorPoint sel n).take i) (ys.take i) ∧
      t.mem = s.mem ∧ RegsFrame selRegs s t)
    (fun t ↦ (t.reg .rbp).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, rfl, ?_, rfl, RegsFrame.refl _ _⟩
    · rw [h14, Nat.mul_zero, ew_zero]
    · rw [hn, Nat.sub_zero]
    · simp only [List.take_zero, eqEval_nil_left, mul_one]; rfl
  · intro t ⟨i, hi, t14, tbp, tsi, hI, hm, hf⟩ hc
    have hin : i < n := cnt_lt (tbp ▸ cond_test_true hc)
    obtain ⟨y0, y1⟩ := hy i hin
    refine WP.load_at (by rw [hm, t14, int64Zero_toUInt64, ew_zero']; exact y0) ?_
    fstep; fstep; fstep; fstep
    refine WP.load_at (by rsimp; rw [hm, t14, ew_one]; exact y1) ?_
    refine WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1
    have k : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → t₁.reg r = t.reg r := fun r hr h11 h12 ↦ by
      rw [e3 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.1, h11, h12]
    fstep; fstep; fstep; fdone
    refine ⟨⟨i + 1, hin, ?_, ?_, ?_, ?_, e2.trans hm, ?_⟩, ?_⟩
    · rw [k .r14 (by decide) (by decide) (by decide), t14, ew_step]
    · rw [k .rbp (by decide) (by decide) (by decide), tbp, cnt_succ hin]
    · rw [k .rsi (by decide) (by decide) (by decide), toNat_shr_one, tsi, Nat.shiftRight_add]
    · have hb : eOf (t.reg .rsi &&& 1) 0 = (selectorPoint sel n).getD i 0 := by
        rw [eOf_and_one, tsi, selectorPoint_getD _ _ _ hin]
      rw [e1, hI, eOf_xor_one, eOf_xor_lo, eOf_lanes, hb,
        eqEval_take_succ _ _ (by rw [selectorPoint_length]; exact hin) hin]
      ring
    · intro r hr
      have hr' := hr
      simp only [selRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨_, _, _, _, hsi, hbp, _, _, _, h11, h12, h14⟩ := hr'
      have hk : r ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setReg_reg, hsi, hbp, h14, ↓reduceIte, k r hk h11 h12]
      exact hf r hr
    · rw [k .rbp (by decide) (by decide) (by decide), tbp, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, tbp, _, hI, hm, hf⟩ hc
    obtain rfl : i = n := cnt_eq (by omega) hi (tbp ▸ cond_test_false hc)
    refine ⟨?_, hm, hf⟩
    rw [hI, List.take_of_length_le (by rw [selectorPoint_length]), List.take_of_length_le (le_refl _)]

/-! ## `shiftLoop` -/

/-- `rsi := rsi >>> rdx`, a bit a pass. -/
def shiftLoop : Stmt := .loop (.test false .rdx (.reg .rdx)) (blk [I (.shri .rsi 1), I (.subi .rdx 1)])

/-- **`shiftLoop` shifts by any count.** -/
theorem shiftLoop_spec : WP shiftLoop s (fun s' ↦
    (s'.reg .rsi).toNat = (s.reg .rsi).toNat >>> (s.reg .rdx).toNat ∧ s'.mem = s.mem ∧
      RegsFrame [.rsi, .rdx] s s') F := by
  unfold shiftLoop
  apply WP.loop (fun t ↦ (t.reg .rsi).toNat >>> (t.reg .rdx).toNat =
      (s.reg .rsi).toNat >>> (s.reg .rdx).toNat ∧ t.mem = s.mem ∧ RegsFrame [.rsi, .rdx] s t)
    (fun t ↦ (t.reg .rdx).toNat)
  · exact ⟨rfl, rfl, RegsFrame.refl _ _⟩
  · intro t ⟨hI, hm, hf⟩ hc
    have hne := cond_test_true hc
    fstep; fstep; fdone
    refine ⟨⟨?_, hm, by rf_tac; exact hf⟩, ?_⟩
    · rw [toNat_sub_one hne, toNat_shr_one, ← Nat.shiftRight_add, ← hI]
      congr 1
      have : (t.reg .rdx).toNat ≠ 0 := fun h0 ↦ hne (UInt64.toNat_inj.mp (by simpa using h0))
      omega
    · rw [toNat_sub_one hne]
      have : (t.reg .rdx).toNat ≠ 0 := fun h0 ↦ hne (UInt64.toNat_inj.mp (by simpa using h0))
      omega
  · intro t ⟨hI, hm, hf⟩ hc
    have h0 := cond_test_false hc
    refine ⟨?_, hm, hf⟩
    rw [← hI, h0]
    rfl

end NativeVm.Code.Ring
