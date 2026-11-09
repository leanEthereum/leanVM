module

public import LeanVM.Protocol.Extraction.Fast.RothRuckenstein
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic

/-!
# Roth–Ruckenstein's substitution by a butterfly Taylor shift

`substituteFast Q a` (`Fast/RothRuckenstein.lean`) computes row `t` of `Q(X, a + X·Y)` as
`X^t·Σ_{t ≤ y, C(y, t) odd} a^(y−t)·Q_y`: about `ℓ²/2` scaled additions of rows. In characteristic
`2`, `(Y + a)^(2^j) = Y^(2^j) + a^(2^j)`, so the shift `Y ↦ Y + a` is `⌈log₂ ℓ⌉` levels of a
butterfly (`bfLevel`): at level `j`, row `i` (bit `j` of `i` clear) gains `a^(2^j)·row(i + 2^j)`,
at most `ℓ/2` scaled additions per level.

* `taylorShiftBF rows a`: the levels, `h = 1, 2, 4, …` below the number of rows;
* `substituteBF Q a`: row `t` of the shift times `X^t`;
* **`substituteBF_eq`**: `substituteBF Q a = substituteFast Q a`.

The invariant (`ShiftInv`): after the levels below `j`, row `i` is the sum of `a^(y−i)·Q_y` over the
`y` that agree with `i` on the bits from `j` up and hold `i`'s bits below `j` (`Sel j i y`); at the
end, `Sel` is Lucas' parity `chooseOdd y i`.
-/

namespace LeanVM.Extraction.Fast

open CompPoly

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- `u + c·v`, the raw sum trimmed once. -/
@[expose, reducible] def axpyRow (u : CPolynomial F) (c : F) (v : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray (CPolynomial.Raw.addRaw u.val (CPolynomial.Raw.smul c v.val))

/-- **One level of the butterfly**, `h = 2^j`, `c = a^h`: row `i`, bit `j` clear and `i + h` a row,
gains `c·row(i + h)`. -/
@[expose] def bfLevel (rows : Array (CPolynomial F)) (h : ℕ) (c : F) : Array (CPolynomial F) :=
  Array.ofFn fun i : Fin rows.size ↦
    if i.val / h % 2 = 0 ∧ i.val + h < rows.size then
      axpyRow (rows.getD i.val 0) c (rows.getD (i.val + h) 0)
    else rows.getD i.val 0

/-- The levels `h, 2·h, 4·h, …` below the number of rows, at most `fuel` of them. -/
@[expose] def bfLoop (a : F) : ℕ → Array (CPolynomial F) → ℕ → Array (CPolynomial F)
  | 0, rows, _ => rows
  | fuel + 1, rows, h =>
    if h < rows.size then bfLoop a fuel (bfLevel rows h (a ^ h)) (2 * h) else rows

/-- **The Taylor shift `Y ↦ Y + a`** of the rows (characteristic `2`), by the butterfly. -/
@[expose, reducible] def taylorShiftBF (rows : Array (CPolynomial F)) (a : F) : Array (CPolynomial F) :=
  bfLoop a rows.size rows 1

/-- **Roth–Ruckenstein's substitution `Y := a + X·Y`, by the butterfly**: row `t` of the Taylor
shift, times `X^t`. -/
@[expose] def substituteBF (Q : CBivariate F) (a : F) : CBivariate F :=
  let rows := taylorShiftBF Q.val a
  CPolynomial.ofArray (Array.ofFn fun t : Fin Q.val.size ↦ shiftX t.val (rows.getD t.val 0))

/-! ## Bits -/

theorem chooseOdd_iff : ∀ (n k : ℕ),
    chooseOdd n k = true ↔ ∀ b, k.testBit b = true → n.testBit b = true
  | 0, k => by
    rw [chooseOdd]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · obtain ⟨b, hb⟩ := Nat.exists_testBit_of_ne_zero (by omega : k ≠ 0)
      simp only [beq_iff_eq, show k ≠ 0 by omega, false_iff, not_forall]
      exact ⟨b, hb, by simp⟩
  | n + 1, k => by
    rw [chooseOdd, Bool.and_eq_true, chooseOdd_iff ((n + 1) / 2) (k / 2), decide_eq_true_iff]
    have hsplit : ∀ P : ℕ → Prop, (∀ b, P b) ↔ P 0 ∧ ∀ b, P (b + 1) :=
      fun P ↦ ⟨fun h ↦ ⟨h 0, fun b ↦ h (b + 1)⟩, fun ⟨h0, hs⟩ b ↦ by cases b; exacts [h0, hs _]⟩
    rw [hsplit (fun b ↦ k.testBit b = true → (n + 1).testBit b = true)]
    simp only [Nat.testBit_zero, Nat.testBit_add_one, decide_eq_true_eq]
    have hk := Nat.mod_lt k (show 0 < 2 by norm_num)
    have hn := Nat.mod_lt (n + 1) (show 0 < 2 by norm_num)
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun _ ↦ by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by by_cases k % 2 = 1 <;> [have := h1 ‹_›; skip] <;> omega, h2⟩
decreasing_by omega

theorem le_of_chooseOdd {n k : ℕ} (h : chooseOdd n k = true) : k ≤ n :=
  Nat.le_of_testBit ((chooseOdd_iff n k).1 h)

theorem testBit_add_two_pow : ∀ (j x : ℕ), x.testBit j = false →
    ∀ b, (x + 2 ^ j).testBit b = (x.testBit b || decide (b = j))
  | 0, x, hx, b => by
    rw [Nat.testBit_zero, decide_eq_false_iff_not] at hx
    cases b with
    | zero => simp only [Nat.testBit_zero, pow_zero]; simp; omega
    | succ b =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one, show (x + 2 ^ 0) / 2 = x / 2 by simp; omega]
      simp
  | j + 1, x, hx, b => by
    rw [Nat.testBit_add_one] at hx
    cases b with
    | zero =>
      simp only [Nat.testBit_zero, pow_succ]
      rw [show (x + 2 ^ j * 2) % 2 = x % 2 by omega]
      simp
    | succ b =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one,
        show (x + 2 ^ (j + 1)) / 2 = x / 2 + 2 ^ j by rw [pow_succ]; omega,
        testBit_add_two_pow j (x / 2) hx b]
      simp

/-- `y` agrees with `i` on the bits from `j` up and holds `i`'s bits below `j`. -/
@[expose] def Sel (j i y : ℕ) : Prop :=
  (∀ b, j ≤ b → y.testBit b = i.testBit b) ∧ (∀ b, b < j → i.testBit b = true → y.testBit b = true)

theorem Sel.le {j i y : ℕ} (h : Sel j i y) : i ≤ y :=
  Nat.le_of_testBit fun b hb ↦ by
    by_cases hbj : j ≤ b
    · rw [h.1 b hbj]; exact hb
    · exact h.2 b (by omega) hb

theorem sel_zero (i y : ℕ) : Sel 0 i y ↔ y = i :=
  ⟨fun h ↦ Nat.eq_of_testBit_eq fun b ↦ h.1 b (Nat.zero_le b), fun h ↦ h ▸
    ⟨fun _ _ ↦ rfl, fun _ hb ↦ absurd hb (Nat.not_lt_zero _)⟩⟩

theorem sel_succ_of_set {j i y : ℕ} (hi : i.testBit j = true) : Sel (j + 1) i y ↔ Sel j i y := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb ↦ ?_, fun b hb ↦ h2 b (by omega)⟩
    rcases Nat.eq_or_lt_of_le hb with rfl | hb
    · rw [hi]; exact h2 j (by omega) hi
    · exact h1 b hb
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb ↦ h1 b (by omega), fun b hb hib ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
    · exact h2 b hb hib
    · rw [h1 b le_rfl]; exact hib

theorem sel_succ_of_clear {j i y : ℕ} (hi : i.testBit j = false) :
    Sel (j + 1) i y ↔ Sel j i y ∨ Sel j (i + 2 ^ j) y := by
  have ht := testBit_add_two_pow j i hi
  constructor
  · rintro ⟨h1, h2⟩
    cases hy : y.testBit j
    · left
      refine ⟨fun b hb ↦ ?_, fun b hb ↦ h2 b (by omega)⟩
      rcases Nat.eq_or_lt_of_le hb with rfl | hb
      · rw [hy, hi]
      · exact h1 b hb
    · right
      refine ⟨fun b hb ↦ ?_, fun b hb hib ↦ ?_⟩
      · rw [ht b]
        rcases Nat.eq_or_lt_of_le hb with rfl | hb
        · simp [hy]
        · rw [h1 b hb]; simp [show b ≠ j by omega]
      · rw [ht b] at hib
        simp only [show b ≠ j by omega, decide_false, Bool.or_false] at hib
        exact h2 b (by omega) hib
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨fun b hb ↦ h1 b (by omega), fun b hb hib ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · exact h2 b hb hib
      · rw [hi] at hib; exact absurd hib (by simp)
    · refine ⟨fun b hb ↦ ?_, fun b hb hib ↦ ?_⟩
      · rw [h1 b (by omega), ht b]; simp [show b ≠ j by omega]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
        · exact h2 b hb (by rw [ht b]; simp [hib])
        · rw [hi] at hib; exact absurd hib (by simp)

theorem sel_disjoint {j i y : ℕ} (hi : i.testBit j = false) :
    ¬ (Sel j i y ∧ Sel j (i + 2 ^ j) y) := by
  rintro ⟨h1, h2⟩
  have e1 := h1.1 j le_rfl
  have e2 := h2.1 j le_rfl
  rw [testBit_add_two_pow j i hi] at e2
  rw [e1, hi] at e2
  simp at e2

theorem sel_top {L i y : ℕ} (hy : y < 2 ^ L) (hi : i < 2 ^ L) :
    Sel L i y ↔ chooseOdd y i = true := by
  rw [chooseOdd_iff]
  constructor
  · rintro ⟨h1, h2⟩ b hb
    by_cases hbL : L ≤ b
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hbL))] at hb
      exact absurd hb (by simp)
    · exact h2 b (by omega) hb
  · intro h
    refine ⟨fun b hb ↦ ?_, fun b _ hb ↦ h b hb⟩
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hb)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hb))]

/-! ## The butterfly's invariant -/

theorem coeff_axpyRow (u : CPolynomial F) (c : F) (v : CPolynomial F) (x : ℕ) :
    (axpyRow u c v).coeff x = u.coeff x + c * v.coeff x := by
  rw [axpyRow, CPolynomial.coeff_ofArray]
  exact (CPolynomial.Raw.add_coeff? (Q := F) u.val (CPolynomial.Raw.smul c v.val) x).trans
    (by rw [CPolynomial.Raw.smul_equiv])

theorem size_bfLevel (rows : Array (CPolynomial F)) (h : ℕ) (c : F) :
    (bfLevel rows h c).size = rows.size := by
  simp [bfLevel]

theorem getD_bfLevel (rows : Array (CPolynomial F)) (h : ℕ) (c : F) {i : ℕ} (hi : i < rows.size) :
    (bfLevel rows h c).getD i 0 = if i / h % 2 = 0 ∧ i + h < rows.size then
      axpyRow (rows.getD i 0) c (rows.getD (i + h) 0) else rows.getD i 0 := by
  rw [bfLevel, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [hi]

open Classical in
/-- After the levels below `j`: the rows' number kept, row `i` the sum of `a^(y−i)·Q_y` over the
`y` of `Sel j i y` (coefficient by coefficient). -/
@[expose] def ShiftInv (a : F) (rows0 rows : Array (CPolynomial F)) (j : ℕ) : Prop :=
  rows.size = rows0.size ∧ ∀ i < rows0.size, ∀ x, (rows.getD i 0).coeff x =
    ∑ y ∈ Finset.range rows0.size, if Sel j i y then a ^ (y - i) * (rows0.getD y 0).coeff x else 0

omit [BEq F] [LawfulBEq F] in
theorem shiftInv_zero (a : F) (rows0 : Array (CPolynomial F)) : ShiftInv a rows0 rows0 0 := by
  classical
  refine ⟨rfl, fun i hi x ↦ ?_⟩
  simp only [sel_zero]
  rw [Finset.sum_ite_eq' (Finset.range rows0.size) i]
  simp [Finset.mem_range.2 hi]

theorem shiftInv_level {a : F} {rows0 rows : Array (CPolynomial F)} {j : ℕ}
    (h : ShiftInv a rows0 rows j) : ShiftInv a rows0 (bfLevel rows (2 ^ j) (a ^ 2 ^ j)) (j + 1) := by
  classical
  obtain ⟨hs, hr⟩ := h
  refine ⟨by rw [size_bfLevel, hs], fun i hi x ↦ ?_⟩
  rw [getD_bfLevel _ _ _ (by omega), hs]
  have hbit : i / 2 ^ j % 2 = 0 ↔ i.testBit j = false := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have := Nat.mod_lt (i / 2 ^ j) (show 0 < 2 by norm_num)
    simp only [decide_eq_false_iff_not]
    omega
  cases hib : i.testBit j with
  | true =>
    have hc : ¬ (i / 2 ^ j % 2 = 0 ∧ i + 2 ^ j < rows0.size) := fun h ↦ by
      have := hbit.1 h.1; rw [hib] at this; exact absurd this (by simp)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc), hr i hi x]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp only [sel_succ_of_set hib]
  | false =>
    have hpt : ∀ y, (if Sel (j + 1) i y then a ^ (y - i) * (rows0.getD y 0).coeff x else 0) =
        (if Sel j i y then a ^ (y - i) * (rows0.getD y 0).coeff x else 0) +
          a ^ 2 ^ j * (if Sel j (i + 2 ^ j) y then
            a ^ (y - (i + 2 ^ j)) * (rows0.getD y 0).coeff x else 0) := by
      intro y
      have hd := sel_disjoint (y := y) hib
      by_cases h1 : Sel j i y
      · have h2 : ¬ Sel j (i + 2 ^ j) y := fun h2 ↦ hd ⟨h1, h2⟩
        simp [h1, h2, (sel_succ_of_clear hib).2 (Or.inl h1)]
      · by_cases h2 : Sel j (i + 2 ^ j) y
        · have hle := h2.le
          simp only [h1, h2, (sel_succ_of_clear hib).2 (Or.inr h2), ↓reduceIte, zero_add]
          rw [← mul_assoc, ← pow_add, show 2 ^ j + (y - (i + 2 ^ j)) = y - i by
            generalize 2 ^ j = P at hle ⊢; omega]
        · have h3 : ¬ Sel (j + 1) i y := fun h3 ↦ ((sel_succ_of_clear hib).1 h3).elim h1 h2
          simp [h1, h2, h3]
    simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    by_cases hlt : i + 2 ^ j < rows0.size
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hbit.2 hib, hlt⟩), coeff_axpyRow, hr i hi x, hr (i + 2 ^ j) hlt x]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hlt h.2), hr i hi x]
      have : ∑ y ∈ Finset.range rows0.size, (if Sel j (i + 2 ^ j) y then
          a ^ (y - (i + 2 ^ j)) * (rows0.getD y 0).coeff x else 0) = 0 :=
        Finset.sum_eq_zero fun y hy ↦ by
          have := Finset.mem_range.1 hy
          rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ by have hle := h.le; omega)]
      rw [this, mul_zero, add_zero]

theorem shiftInv_loop (a : F) (rows0 : Array (CPolynomial F)) : ∀ (fuel j : ℕ)
    (rows : Array (CPolynomial F)), ShiftInv a rows0 rows j → rows0.size ≤ 2 ^ (j + fuel) →
      ∃ L, ShiftInv a rows0 (bfLoop a fuel rows (2 ^ j)) L ∧ rows0.size ≤ 2 ^ L
  | 0, j, rows, h, hn => ⟨j, by rw [bfLoop]; exact h, by simpa using hn⟩
  | fuel + 1, j, rows, h, hn => by
    rw [bfLoop]
    split
    · rw [show 2 * 2 ^ j = 2 ^ (j + 1) by rw [pow_succ, mul_comm]]
      exact shiftInv_loop a rows0 fuel (j + 1) _ (shiftInv_level h)
        (by rw [show j + 1 + fuel = j + (fuel + 1) by omega]; exact hn)
    · rename_i hlt
      exact ⟨j, h, by rw [h.1] at hlt; omega⟩

theorem coeff_taylorShiftBF (rows0 : Array (CPolynomial F)) (a : F) {t : ℕ}
    (ht : t < rows0.size) (x : ℕ) :
    ((taylorShiftBF rows0 a).getD t 0).coeff x =
      ∑ y ∈ Finset.range rows0.size,
        if chooseOdd y t then a ^ (y - t) * (rows0.getD y 0).coeff x else 0 := by
  classical
  obtain ⟨L, ⟨-, hr⟩, hL⟩ := shiftInv_loop a rows0 rows0.size 0 rows0 (shiftInv_zero a rows0)
    (by simpa using Nat.lt_two_pow_self.le)
  rw [taylorShiftBF, show (1 : ℕ) = 2 ^ 0 from rfl, hr t ht x]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have := Finset.mem_range.1 hy
  simp only [sel_top (show y < 2 ^ L by omega) (show t < 2 ^ L by omega)]

theorem size_taylorShiftBF (rows0 : Array (CPolynomial F)) (a : F) :
    (taylorShiftBF rows0 a).size = rows0.size := by
  obtain ⟨L, ⟨hs, -⟩, -⟩ := shiftInv_loop a rows0 rows0.size 0 rows0 (shiftInv_zero a rows0)
    (by simpa using Nat.lt_two_pow_self.le)
  exact hs

/-- **Row `t` of the butterfly's shift is `taylorCoeff Q a t`.** -/
theorem taylorShiftBF_getD (Q : CBivariate F) (a : F) {t : ℕ} (ht : t < Q.val.size) :
    (taylorShiftBF Q.val a).getD t 0 = taylorCoeff Q a t := by
  refine CPolynomial.eq_iff_coeff.2 fun x ↦ ?_
  rw [coeff_taylorShiftBF _ _ ht, coeff_taylorCoeff,
    ← Finset.sum_range_add_sum_Ico _ ht.le, Finset.sum_Ico_eq_sum_range,
    Finset.sum_eq_zero (s := Finset.range t) fun y hy ↦ ?_, zero_add]
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ by
    have h1 := le_of_chooseOdd h; have h2 := Finset.mem_range.1 hy; omega)]

/-- **The butterfly's substitution is `substituteFast`.** -/
theorem substituteBF_eq (Q : CBivariate F) (a : F) : substituteBF Q a = substituteFast Q a := by
  rw [substituteBF, substituteFast]
  congr 1
  refine Array.ext (by simp) fun t h1 _ ↦ ?_
  simp only [Array.getElem_ofFn]
  rw [taylorShiftBF_getD Q a (by simpa using h1)]

end

end LeanVM.Extraction.Fast
