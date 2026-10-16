module

public import LeanVMCircuits.ClockSpec
public import LeanVMCircuits.Bus.Memory

@[expose] public section

/-!
# The clock facts from the clock circuit

What the clock circuit's reference (`LeanVMCircuits.Clock`) gives the bus theorems, for a clock below `2^41` with
its five slot bits clear. The clock column plus the step column, a sum in `K`, is the XOR of the two words, which is
the next clock with the verdict `inOrder = !fail` (`clock_next`, fact C2); and when the row does not fail, every access
satisfies the order check `eq:order` (`clock_in_order`, the order part of fact C3).
-/

namespace LeanVMCircuits.Bus

open LeanVMCircuits.Rec

/-- The sum in `K` of two words is their XOR. -/
theorem ofWord_xor {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : ofWord a + ofWord b = ofWord (a ^^^ b) := by
  unfold ofWord
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb), ev_xor]

/-- Below `2^41`, bit 40 is the live bit. -/
theorem testBit_live {t : ℕ} (h : t < 2 ^ 41) : t.testBit 40 = decide (2 ^ 40 ≤ t) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_decide]
  norm_num at h ⊢
  omega

theorem live_iff {t : ℕ} (h : t < 2 ^ 41) : Clock.live t = true ↔ 2 ^ 40 ≤ t := by
  rw [Clock.live, testBit_live h, decide_eq_true_iff]

theorem two_pow_mul_xor (c x : ℕ) : 2 ^ 5 * c ^^^ 2 ^ 5 * x = 2 ^ 5 * (c ^^^ x) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases hj : 5 ≤ j <;> simp [hj]

/-- `ts XOR step` is the next clock. -/
theorem clock_step_xor (slots prev : List ℕ) (ts : ℕ) (ts_lt : ts < 2 ^ 41) (ts_dvd : 2 ^ 5 ∣ ts) :
    ts ^^^ Clock.step slots prev ts = nextClock ts (!Clock.fail slots prev ts) := by
  obtain ⟨ c, rfl ⟩ := ts_dvd
  have c_lt : c < 2 ^ 36 := by norm_num at ts_lt ⊢; omega
  have hlive := live_iff ts_lt
  -- both sides as `2^5 (2^36 f + _)`
  have step_eq : Clock.step slots prev (2 ^ 5 * c) = 2 ^ 5 * (2 ^ 36 * (if Clock.fail slots prev (2 ^ 5 * c) then 1 else 0) +
      ((c + if Clock.live (2 ^ 5 * c) then 1 else 0) ^^^ c) % 2 ^ 36) := by
    unfold Clock.step
    rw [Nat.mul_div_cancel_left c (by norm_num : 0 < 2 ^ 5)]
    split_ifs <;> ring
  have next_eq : nextClock (2 ^ 5 * c) (!Clock.fail slots prev (2 ^ 5 * c)) =
      2 ^ 5 * (2 ^ 36 * (if Clock.fail slots prev (2 ^ 5 * c) then 1 else 0) +
        (c + if Clock.live (2 ^ 5 * c) then 1 else 0) % 2 ^ 36) := by
    unfold nextClock
    by_cases hl : Clock.live (2 ^ 5 * c) = true
    · rw [if_pos (hlive.mp hl), if_pos hl]
      cases Clock.fail slots prev (2 ^ 5 * c) <;> simp <;> omega
    · rw [if_neg (fun h => hl (hlive.mpr h)), if_neg hl]
      cases Clock.fail slots prev (2 ^ 5 * c) <;> simp <;> omega
  have m_lt : ((c + if Clock.live (2 ^ 5 * c) then 1 else 0) ^^^ c) % 2 ^ 36 < 2 ^ 36 := Nat.mod_lt _ (by norm_num)
  have n_lt : (c + if Clock.live (2 ^ 5 * c) then 1 else 0) % 2 ^ 36 < 2 ^ 36 := Nat.mod_lt _ (by norm_num)
  rw [step_eq, next_eq, two_pow_mul_xor]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ m_lt, Nat.testBit_two_pow_mul_add _ n_lt]
  by_cases hj : j < 36
  · simp only [hj, if_true, Nat.testBit_mod_two_pow, Nat.testBit_xor, decide_true, Bool.true_and]
    cases c.testBit j <;> cases (c + if Clock.live (2 ^ 5 * c) then 1 else 0).testBit j <;> rfl
  · simp only [hj, if_false]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le c_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp

/-- Fact C2 from the clock circuit: the clock column plus the step column is the next clock, `inOrder = !fail`. -/
theorem clock_next (slots prev : List ℕ) (ts : ℕ) (ts_lt : ts < 2 ^ 41) (ts_dvd : 2 ^ 5 ∣ ts) :
    ofWord ts + ofWord (Clock.step slots prev ts) = ofWord (nextClock ts (!Clock.fail slots prev ts)) := by
  have step_lt : Clock.step slots prev ts < 2 ^ 64 := by
    have := clock_step_xor slots prev ts ts_lt ts_dvd
    have next_lt := nextClock_lt ts (!Clock.fail slots prev ts)
    have : Clock.step slots prev ts = ts ^^^ nextClock ts (!Clock.fail slots prev ts) := by
      rw [← this, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [this]
    exact Nat.xor_lt_two_pow (by omega) (by omega)
  rw [ofWord_xor (by omega) step_lt, clock_step_xor slots prev ts ts_lt ts_dvd]

/-- The order part of fact C3 from the clock circuit: when the row does not fail, each access's previous timestamp
has the clock's live bit, and on a live row it is below the access's timestamp `ts + slot`. -/
theorem clock_in_order (slots prev : List ℕ) (ts : ℕ) (ts_lt : ts < 2 ^ 41) (ts_dvd : 2 ^ 5 ∣ ts)
    (prev_lt : ∀ p ∈ prev, p < 2 ^ 41) (slot_lt : ∀ s ∈ slots, s < 2 ^ 5) (len : prev.length = slots.length)
    (ok : Clock.fail slots prev ts = false) (i : ℕ) (hi : i < slots.length) :
    (2 ^ 40 ≤ prev[i]'(len ▸ hi) ↔ 2 ^ 40 ≤ ts) ∧ (2 ^ 40 ≤ ts → prev[i]'(len ▸ hi) < ts + slots[i]) := by
  have hi' : i < prev.length := len ▸ hi
  have p_mem := List.getElem_mem hi'
  have p_lt := prev_lt _ p_mem
  have s_lt := slot_lt _ (List.getElem_mem hi)
  simp only [Clock.fail, Bool.or_eq_false_iff, List.any_eq_false, Bool.and_eq_false_iff, Bool.not_eq_false'] at ok
  obtain ⟨ order, agree ⟩ := ok
  have same : (2 ^ 40 ≤ prev[i] ↔ 2 ^ 40 ≤ ts) := by
    have := agree _ p_mem
    simp only [Clock.disagrees, bne_iff_ne, ne_eq, Decidable.not_not] at this
    rw [← decide_eq_decide, ← testBit_live p_lt, ← testBit_live ts_lt]
    simpa using this
  refine ⟨ same, fun live => ?_ ⟩
  have live' : Clock.live ts = true := (live_iff ts_lt).mpr live
  rcases order with h | h
  · rw [live'] at h
    exact absurd h (by simp)
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at h
    have pair_mem : (prev[i], slots[i]) ∈ prev.zip slots := by
      have hz : i < (prev.zip slots).length := by simp [hi, hi']
      have := List.getElem_mem hz
      rwa [List.getElem_zip] at this
    have := h.2 _ pair_mem
    simp only [Clock.ordered, decide_eq_true_eq] at this
    have prev_live := same.mpr live
    norm_num at this prev_live live p_lt ts_lt ⊢
    omega

end LeanVMCircuits.Bus
