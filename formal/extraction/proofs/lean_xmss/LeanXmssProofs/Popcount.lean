import LeanXmssProofs.Common

/-!
# `u128::count_ones`, and the digit sum it gives

The library's model of `count_ones` is a loop over a range of `u32`: for each of the 128 bit
positions, shift, mask, and count (`count_ones_eq`). `is_codeword` calls it twice, on the bits at
the even positions and on those at the odd ones, and adds the first count to twice the second:
the sum of the base-4 digits (`popcount_digits`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open Keccak256Proofs

namespace LeanXmssProofs

/-! ## A range of `u32` -/

/-- `next` on a range of `u32`: its start and the range after it, or nothing at the end. -/
theorem range_next_spec_u32 (i e : Std.U32) {Q}
    (h_lt : (h : i.val < e.val) → ∀ (s : Std.U32), s.val = i.val + 1 →
      (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val → (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.IteratorRange.next core.U32.Insts.CoreIterRangeStep { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core.IteratorRange.next core.U32.Insts.CoreIterRangeStep
  by_cases h : i.val < e.val
  · simp_all [compare, compareOfLessAndEq,
      core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd,
      core.U32.Insts.CoreCloneClone.clone,
      core.U32.Insts.CoreIterRangeStep.forward_checked,
      core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from,
      core.num.U32.MAX, core.num.U32.MIN,
      core.num.U32.checked_add, core.num.U32.overflowing_add,
      rust_primitives.arithmetic.overflowing_add_u32]
    have h1 : (UScalar.cast UScalarTy.U32 (1#usize)).val = 1 := by
      rw [UScalar.cast_val_eq]; rfl
    have hov := UScalar.overflowing_add_eq i (UScalar.cast UScalarTy.U32 1#usize)
    have hib := i.hBounds
    have heb := e.hBounds
    have hmax : UScalar.max UScalarTy.U32 = 4294967295 := by scalar_tac
    have hnb : UScalarTy.U32.numBits = 32 := rfl
    rw [hnb] at hib heb
    replace hov : (UScalar.overflowing_add i (UScalar.cast UScalarTy.U32 1#usize)).1.val =
        i.val + 1 ∧ (UScalar.overflowing_add i (UScalar.cast UScalarTy.U32 1#usize)).2 = false := by
      simp only [h1, hmax] at hov
      split at hov
      · omega
      · exact hov
    hax_mvcgen [uncurry]
    case vc1.hQ =>
      rename_i h0
      exfalso
      rw [UScalar.cast_val_eq] at h0
      revert h0
      rcases System.Platform.numBits_eq with hb | hb <;> simp [UScalarTy.numBits, hb, U32.rMax]
    case vc2.hQ =>
      rename_i h0 h2
      exfalso
      rw [UScalar.cast_val_eq] at h2
      simp at h2
    case vc3.hQ =>
      rename_i h0 h2 h3
      rw [hov.2] at h3
      cases h3
    case vc4.hQ =>
      rename_i h0 h2 h3
      exact h_lt _ hov.1
  · have h_ge' := h_ge (Nat.le_of_not_lt h)
    simp_all [core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd]
    hax_mvcgen
    grind

/-- `range_next_spec_u32`, as a specification `step` applies. -/
theorem range_next_u32 (i e : Std.U32) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.U32.Insts.CoreIterRangeStep { start := i, «end» := e } ⦃ r =>
      (i.val < e.val ∧ ∃ s : Std.U32, s.val = i.val + 1 ∧ r = (some i, { start := s, «end» := e })) ∨
      (e.val ≤ i.val ∧ r = (none, { start := i, «end» := e })) ⦄ := by
  have t := range_next_spec_u32 i e
    (Q := PostCond.noThrow fun r => ⌜(i.val < e.val ∧ ∃ s : Std.U32, s.val = i.val + 1 ∧
      r = (some i, { start := s, «end» := e })) ∨ (e.val ≤ i.val ∧ r = (none, { start := i, «end» := e }))⌝)
    (fun h s hs => Or.inl ⟨h, s, hs, rfl⟩) (fun h => Or.inr ⟨h, rfl⟩)
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok t
  have hp := Hax.triple_noThrow_elim t hv
  exact spec_of_exists ⟨v, hv, hp⟩

/-! ## The population count -/

/-- The number of ones among the low `n` bits of `v`. -/
def popcount (v n : ℕ) : ℕ := ∑ j ∈ Finset.range n, v / 2 ^ j % 2

theorem popcount_succ (v n : ℕ) : popcount v (n + 1) = popcount v n + v / 2 ^ n % 2 :=
  Finset.sum_range_succ _ _

theorem popcount_le (v n : ℕ) : popcount v n ≤ n := by
  induction n with
  | zero => simp [popcount]
  | succ n ih => rw [popcount_succ]; omega

/-- **`u128::count_ones`**: the number of ones among the 128 bits. -/
theorem count_ones_eq (x : Std.U128) :
    ∃ r, core.num.U128.count_ones x = ok r ∧ r.val = popcount x.val 128 := by
  apply WP.spec_imp_exists
  unfold core.num.U128.count_ones core.num.U128.count_ones_loop
  apply loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = 128#u32 ∧ p.1.start.val ≤ 128 ∧ p.2.val = popcount x.val p.1.start.val)
  · rintro ⟨⟨i, en⟩, n⟩ ⟨hen, hi, hn⟩
    simp only at hen hi hn
    subst hen
    unfold core.num.U128.count_ones_loop.body
    step with range_next_u32 as ⟨r, it, hnext⟩
    rcases hnext with ⟨hlt, s, hs, rfl, rfl⟩ | ⟨hge, rfl, rfl⟩
    · simp only
      step as ⟨i1, hi1⟩
      simp only [lift, Aeneas.Std.bind_ok]
      have hbit : (i1 &&& 1#u128 = 1#u128) ↔ x.val / 2 ^ i.val % 2 = 1 := by
        rw [UScalar.eq_equiv, UScalar.val_and, hi1, Nat.shiftRight_eq_div_pow]
        show _ &&& 1 = 1 ↔ _
        rw [Nat.and_one_is_mod]
      have hle := popcount_le x.val i.val
      have h128 : (128#u32 : Std.U32).val = 128 := rfl
      split
      · rename_i h1
        step as ⟨n1, hn1⟩
        refine ⟨by omega, ?_, by omega⟩
        rw [hn1, hs, popcount_succ, hn, hbit.mp h1]
      · rename_i h1
        simp only [WP.spec_ok]
        refine ⟨trivial, by omega, ?_, by omega⟩
        have h0 : x.val / 2 ^ i.val % 2 = 0 := by
          have := mt hbit.mpr h1
          omega
        rw [hs, popcount_succ, hn, h0]
        rfl
    · simp only [WP.spec_ok]
      have : i.val = 128 := by omega
      rw [hn, this]
  · exact ⟨rfl, by simp, by simp [popcount]⟩

/-! ## The digits of a number, from two population counts -/

/-- `0b0101…01`, `n` times: the low bit of each of `n` two-bit digits (`LOW`). -/
def lowBits : ℕ → ℕ
  | 0 => 0
  | n + 1 => 4 * lowBits n + 1

theorem testBit_lowBits (n : ℕ) : ∀ j, (lowBits n).testBit j = decide (j % 2 = 0 ∧ j < 2 * n) := by
  induction n with
  | zero => intro j; simp [lowBits]
  | succ n ih =>
    intro j
    match j with
    | 0 => simp [lowBits, Nat.testBit_zero]; omega
    | 1 =>
      rw [lowBits, Nat.testBit_succ, Nat.testBit_zero]
      simp
      omega
    | j + 2 =>
      rw [lowBits, Nat.testBit_succ, Nat.testBit_succ,
        show (4 * lowBits n + 1) / 2 / 2 = lowBits n by omega, ih]
      apply decide_eq_decide.mpr
      omega

theorem bit_and (a b j : ℕ) : (a &&& b) / 2 ^ j % 2 = (a.testBit j && b.testBit j).toNat := by
  rw [← Nat.toNat_testBit, Nat.testBit_and]

/-- The ones of `d` at the positions of one parity below `2 n`, selected by a mask. -/
theorem popcount_and_mask (d m r n : ℕ) (hr : r < 2)
    (hm : ∀ j < 2 * n, m.testBit j = decide (j % 2 = r)) :
    popcount (d &&& m) (2 * n) = ∑ i ∈ Finset.range n, d / 2 ^ (2 * i + r) % 2 := by
  induction n with
  | zero => simp [popcount]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, popcount_succ, popcount_succ,
      ih (fun j hj => hm j (by omega)), Finset.sum_range_succ, bit_and, bit_and,
      hm (2 * n) (by omega), hm (2 * n + 1) (by omega)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n + 1) % 2 = 1 := by omega
    rw [h1, h2]
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · simp [Nat.toNat_testBit]
    · simp [Nat.toNat_testBit]

/-- **The sum of the base-4 digits**: the ones at the even positions, and twice those at the
odd ones. -/
theorem popcount_digits (d lo hi n : ℕ)
    (hlo : ∀ j < 2 * n, lo.testBit j = decide (j % 2 = 0))
    (hhi : ∀ j < 2 * n, hi.testBit j = decide (j % 2 = 1)) :
    popcount (d &&& lo) (2 * n) + 2 * popcount (d &&& hi) (2 * n) =
      ∑ i ∈ Finset.range n, d / 2 ^ (2 * i) % 4 := by
  rw [popcount_and_mask d lo 0 n (by omega) hlo, popcount_and_mask d hi 1 n (by omega) hhi,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_zero, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

end LeanXmssProofs
