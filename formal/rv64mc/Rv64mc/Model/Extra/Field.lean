/-
  Rv64mc.Model.Extra.Field

  `Model.Field`'s values in the forms the compiled code computes them, a word at a time: `spread`'s two words, each
  the last four steps of `spread` on one word (`spreadTail`), from its half of `a` spread by 16.
-/

import Rv64mc.Spec.Field.Basic

namespace Rv64mc.Model

open Rv64mc.Spec.Field

/-- One step of `spread` on a word whose set bits stay inside it: `(x << k | x) & mask`. -/
def spreadStep (k : Nat) (mask x : BitVec 64) : BitVec 64 := (x <<< k ||| x) &&& mask

/-- `spread`'s last four steps on one word. -/
def spreadTail (x : BitVec 64) : BitVec 64 :=
  spreadStep 1 0x5555555555555555#64 (spreadStep 2 0x3333333333333333#64
    (spreadStep 4 0x0F0F0F0F0F0F0F0F#64 (spreadStep 8 0x00FF00FF00FF00FF#64 x)))

section Helpers

/-- After the step of shift `s`, bit `k` (with `k % 2s < s`) holds bit `off + (k / 2s) s + k % 2s` of `a`, and
    the other bits are clear (`Model.Field`'s invariant of `spread`, at any width and offset). -/
private def SpreadInv {w : Nat} (a : BitVec 64) (off s : Nat) (x : BitVec w) : Prop :=
  ∀ k, x.getLsbD k =
    (decide (k < w) && decide (k % (2 * s) < s) && a.getLsbD (off + k / (2 * s) * s + k % (2 * s)))

private theorem spreadInv_step {w : Nat} (a : BitVec 64) (off s : Nat) (x m : BitVec w)
    (hs : s = 32 ∨ s = 16 ∨ s = 8 ∨ s = 4 ∨ s = 2 ∨ s = 1)
    (hm : ∀ k : Fin w, m.getLsbD k = decide (k.val % (2 * s) < s)) (hx : SpreadInv a off (2 * s) x) :
    SpreadInv a off s ((x ||| x <<< s) &&& m) := by
  intro k
  by_cases hk : k < w
  · have hmk := hm ⟨k, hk⟩
    simp only at hmk
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hx, hx, hmk]
    by_cases h1 : k % (2 * s) < s <;> by_cases h2 : k % (2 * (2 * s)) < 2 * s <;>
      by_cases h3 : k < s <;> simp [h1, h2, h3, hk]
    · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
    · have h4 : ¬ (k - s) % (2 * (2 * s)) < 2 * s := by
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp only [h4, decide_false, Bool.and_false, Bool.false_and, Bool.or_false]
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
    · exfalso; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have h4 : (k - s) % (2 * (2 * s)) < 2 * s := by
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp only [h4, decide_true, show k - s < w by omega, Bool.true_and]
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
  · rw [BitVec.getLsbD_of_ge _ k (by omega)]; simp [hk]

private theorem spreadInv_step' (a : BitVec 64) (off s : Nat) (x m : BitVec 64) (hs : s = 8 ∨ s = 4 ∨ s = 2 ∨ s = 1)
    (hm : ∀ k : Fin 64, m.getLsbD k = decide (k.val % (2 * s) < s)) (hx : SpreadInv a off (2 * s) x) :
    SpreadInv a off s (spreadStep s m x) := by
  rw [spreadStep, BitVec.or_comm]
  exact spreadInv_step a off s x m (by omega) hm hx

private theorem m32 : ∀ k : Fin 128, (0x00000000FFFFFFFF00000000FFFFFFFF#128).getLsbD k =
    decide (k.val % (2 * 32) < 32) := by decide +kernel
private theorem m16 : ∀ k : Fin 128, (0x0000FFFF0000FFFF0000FFFF0000FFFF#128).getLsbD k =
    decide (k.val % (2 * 16) < 16) := by decide +kernel
private theorem m8 : ∀ k : Fin 128, (0x00FF00FF00FF00FF00FF00FF00FF00FF#128).getLsbD k =
    decide (k.val % (2 * 8) < 8) := by decide +kernel
private theorem m4 : ∀ k : Fin 128, (0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128).getLsbD k =
    decide (k.val % (2 * 4) < 4) := by decide +kernel
private theorem m2 : ∀ k : Fin 128, (0x33333333333333333333333333333333#128).getLsbD k =
    decide (k.val % (2 * 2) < 2) := by decide +kernel
private theorem m1 : ∀ k : Fin 128, (0x55555555555555555555555555555555#128).getLsbD k =
    decide (k.val % (2 * 1) < 1) := by decide +kernel

private theorem w16 : ∀ k : Fin 64, (0x0000FFFF0000FFFF#64).getLsbD k = decide (k.val % (2 * 16) < 16) := by
  decide +kernel
private theorem w8 : ∀ k : Fin 64, (0x00FF00FF00FF00FF#64).getLsbD k = decide (k.val % (2 * 8) < 8) := by
  decide +kernel
private theorem w4 : ∀ k : Fin 64, (0x0F0F0F0F0F0F0F0F#64).getLsbD k = decide (k.val % (2 * 4) < 4) := by
  decide +kernel
private theorem w2 : ∀ k : Fin 64, (0x3333333333333333#64).getLsbD k = decide (k.val % (2 * 2) < 2) := by
  decide +kernel
private theorem w1 : ∀ k : Fin 64, (0x5555555555555555#64).getLsbD k = decide (k.val % (2 * 1) < 1) := by
  decide +kernel

private theorem spread_inv (a : BitVec 64) : SpreadInv a 0 1 (spread a) := by
  have h0 : SpreadInv a 0 64 (a.setWidth 128) := by
    intro k
    rw [BitVec.getLsbD_setWidth]
    by_cases hk : k < 128
    · rw [show k % (2 * 64) = k by omega, show k / (2 * 64) = 0 by omega]
      by_cases h : k < 64
      · simp [hk, h]
      · simp [hk, h, BitVec.getLsbD_of_ge a k (by omega)]
    · simp [hk, BitVec.getLsbD_of_ge a k (by omega)]
  exact spreadInv_step a 0 1 _ _ (by simp) m1 <| spreadInv_step a 0 2 _ _ (by simp) m2 <|
    spreadInv_step a 0 4 _ _ (by simp) m4 <| spreadInv_step a 0 8 _ _ (by simp) m8 <|
    spreadInv_step a 0 16 _ _ (by simp) m16 <| spreadInv_step a 0 32 _ _ (by simp) m32 h0

private theorem spreadTail_inv {a x : BitVec 64} {off : Nat} (h : SpreadInv a off 16 x) :
    SpreadInv a off 1 (spreadTail x) :=
  spreadInv_step' a off 1 _ _ (by simp) w1 <| spreadInv_step' a off 2 _ _ (by simp) w2 <|
    spreadInv_step' a off 4 _ _ (by simp) w4 <| spreadInv_step' a off 8 _ _ (by simp) w8 h

private theorem lo_start (a : BitVec 64) :
    SpreadInv a 0 16 ((a <<< 16 ||| a <<< 48 >>> 48) &&& 0x0000FFFF0000FFFF#64) := by
  intro k
  by_cases hk : k < 64
  · have hmk := w16 ⟨k, hk⟩
    simp only at hmk
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft, hmk]
    by_cases h1 : k < 16
    · simp [h1, hk, show 48 + k < 64 by omega, Nat.mod_eq_of_lt (show k < 32 by omega),
        Nat.div_eq_of_lt (show k < 32 by omega)]
    · by_cases h2 : k < 32
      · simp [h1, hk, Nat.mod_eq_of_lt h2]
      · by_cases h3 : k < 48
        · simp [h1, hk, show k % 32 = k - 32 by omega, show k / 32 = 1 by omega, show ¬ 48 + k < 64 by omega]
          rw [Bool.and_comm]; congr 2; omega
        · simp [hk, show ¬ k % 32 < 16 by omega]
  · rw [BitVec.getLsbD_of_ge _ k (by omega)]; simp [hk]

private theorem hi_start (a : BitVec 64) :
    SpreadInv a 32 16 ((a >>> 32 <<< 16 ||| a >>> 32) &&& 0x0000FFFF0000FFFF#64) := by
  intro k
  by_cases hk : k < 64
  · have hmk := w16 ⟨k, hk⟩
    simp only at hmk
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ushiftRight, hmk]
    by_cases h1 : k < 16
    · simp [h1, hk, Nat.mod_eq_of_lt (show k < 32 by omega), Nat.div_eq_of_lt (show k < 32 by omega)]
    · by_cases h2 : k < 32
      · simp [h1, hk, Nat.mod_eq_of_lt h2]
      · by_cases h3 : k < 48
        · simp [h1, hk, show k % 32 = k - 32 by omega, show k / 32 = 1 by omega,
            BitVec.getLsbD_of_ge a (32 + k) (by omega)]
          rw [Bool.and_comm]; congr 2; omega
        · simp [hk, show ¬ k % 32 < 16 by omega]
  · rw [BitVec.getLsbD_of_ge _ k (by omega)]; simp [hk]

end Helpers

/-- **`spread`'s low word**, as the code computes it from `a`'s low 32 bits. -/
theorem lo128_spread (a : BitVec 64) :
    lo128 (spread a) = spreadTail ((a <<< 16 ||| a <<< 48 >>> 48) &&& 0x0000FFFF0000FFFF#64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [lo128, BitVec.getLsbD_setWidth, spreadTail_inv (lo_start a) k, spread_inv a k]
  simp [hk, show k < 128 by omega]

/-- **`spread`'s high word**, as the code computes it from `a`'s high 32 bits. -/
theorem hi128_spread (a : BitVec 64) :
    hi128 (spread a) = spreadTail ((a >>> 32 <<< 16 ||| a >>> 32) &&& 0x0000FFFF0000FFFF#64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [hi128, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, spreadTail_inv (hi_start a) k,
    spread_inv a (64 + k)]
  simp only [hk, decide_true, Bool.true_and, show 64 + k < 128 by omega]
  rw [show (64 + k) % (2 * 1) = k % (2 * 1) by omega, show 0 + (64 + k) / (2 * 1) * 1 + k % (2 * 1) =
    32 + k / (2 * 1) * 1 + k % (2 * 1) by omega]

end Rv64mc.Model
