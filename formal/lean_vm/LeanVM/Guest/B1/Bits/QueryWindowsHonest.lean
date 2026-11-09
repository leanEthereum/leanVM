/-
  LeanVM.Guest.B1.Bits.QueryWindowsHonest

  The honest values of `decode_query_windows`: its windows, positions and rest windows as the
  word's bits, and the reconstruction they make.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindows
public import LeanVM.Guest.Word

/-!
# `decode_query_windows`' honest values (lean_ethereum.py:798-909 at 40f877dc)

On a word `w`, the honest run hints each window as `g^n`, `n` the window's bits of the word
(`WindowsExp`, Interp's `execHint`: `n = Σ_{j<width} 2^j·bit(start + j)`, `winHintVal`,
`winHintVal_eq`: the word's integer shifted and cut). So:

* position `j` is `qwPosOf d w j` (its `d` bits from `j·d`), its window `i` `qwVal d cd (qwPosOf d w j) i`
  (`qwVal_hint`: the hint's value at the window's place), and the `wins` run holds `qwRunW`, the
  positions' windows in order (`qwRunList`, `192 / d · qwN` words);
* rest window `r` is `qwRestOf d w r`, the bits `qwRestWin d r` of the word;
* the digits on tiles of an integer sum back to it (`tS_digits`): a position's windows to the
  position (`qw_pos_tS`), the positions and rest windows to the word (`qw_recon`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Digits on tiles -/

/-- **An integer's digits on the tiles `s` sum back to it**, modulo the tiles' end. -/
theorem tS_digits {s v : ℕ → ℕ} {X m : ℕ} (h0 : s 0 = 0) (hs : ∀ t < m, s t ≤ s (t + 1))
    (hv : ∀ t < m, v t = (X >>> s t) % 2 ^ (s (t + 1) - s t)) :
    ∀ n ≤ m, tS s v n = X % 2 ^ s n
  | 0, _ => by simp [tS, h0, Nat.mod_one]
  | n + 1, hn => by
    rw [tS_succ, tS_digits h0 hs hv n (by omega), hv n (by omega), Nat.shiftRight_eq_div_pow]
    have : 2 ^ s (n + 1) = 2 ^ s n * 2 ^ (s (n + 1) - s n) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (hs n (by omega))]
    rw [this, Nat.mod_mul]

theorem qw_eToNat_lt (x : E) : eToNat x < 2 ^ 192 := by
  have h := eToNat_eOfNat192 (eToNat x)
  rw [eOfNat192_eToNat] at h
  rw [h]; exact Nat.mod_lt _ (by positivity)

/-! ## A position's windows -/

theorem qwVal_lt (d cd q i : ℕ) : qwVal d cd q i < 2 ^ (qwWin d cd i).2 :=
  Nat.mod_lt _ (by positivity)

theorem qwVal_tile {d cd : ℕ} (hs : QwShape d cd) {i : ℕ} (hi : i < qwN d cd) (q : ℕ) :
    qwVal d cd q i = (q >>> qwOff d cd i) % 2 ^ (qwOff d cd (i + 1) - qwOff d cd i) := by
  obtain ⟨-, -, he, -⟩ := hs.2.2.2.2.2.1 i hi
  rw [qwVal, ← he, qwOff_lt hi, Nat.add_sub_cancel_left]

/-- **A position's windows sum back to it.** -/
theorem qw_pos_tS {d cd : ℕ} (hs : QwShape d cd) {q : ℕ} (hq : q < 2 ^ d) :
    tS (qwOff d cd) (qwVal d cd q) (qwN d cd) = q := by
  rw [tS_digits hs.2.2.2.1 (fun t ht ↦ by obtain ⟨-, -, he, -⟩ := hs.2.2.2.2.2.1 t ht; omega)
    (fun t ht ↦ qwVal_tile hs ht q) _ le_rfl, qwOff_top, Nat.mod_eq_of_lt hq]

theorem qwPosOf_lt (d : ℕ) (w : E) (j : ℕ) : qwPosOf d w j < 2 ^ d := Nat.mod_lt _ (by positivity)

/-! ## The honest run -/

/-- Rest window `r`'s value of the word. -/
def qwRestOf (d : ℕ) (w : E) (r : ℕ) : ℕ := (eToNat w >>> (qwRestWin d r).1) % 2 ^ (qwRestWin d r).2

theorem qwRestOf_lt (d : ℕ) (w : E) (r : ℕ) : qwRestOf d w r < 2 ^ (qwRestWin d r).2 :=
  Nat.mod_lt _ (by positivity)

/-- Word `x` of the `wins` run: window `x % qwN` of position `x / qwN`. -/
def qwRunW (d cd : ℕ) (w : E) (x : ℕ) : E :=
  gen ^ qwVal d cd (qwPosOf d w (x / qwN d cd)) (x % qwN d cd)

/-- The `wins` run of the honest run: the positions' windows, `192 / d · qwN` words. -/
def qwRunList (d cd : ℕ) (w : E) : List E := (List.range (192 / d * qwN d cd)).map (qwRunW d cd w)

theorem qwRunW_at {d cd : ℕ} (w : E) {j i : ℕ} (hi : i < qwN d cd) :
    qwRunW d cd w (j * qwN d cd + i) = gen ^ qwVal d cd (qwPosOf d w j) i := by
  have hN : 0 < qwN d cd := by omega
  have e1 : (j * qwN d cd + i) / qwN d cd = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hi, Nat.zero_add]
  have e2 : (j * qwN d cd + i) % qwN d cd = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  rw [qwRunW, e1, e2]

/-! ## The word from its digits -/

/-- Digit `t` of the reconstruction: a position, then a rest window. -/
def qwDigit (d : ℕ) (w : E) (t : ℕ) : ℕ :=
  if t < 192 / d then qwPosOf d w t else qwRestOf d w (t - 192 / d)

/-- **The positions and the rest windows sum back to the word.** -/
theorem qw_recon {d cd : ℕ} (hs : QwShape d cd) (w : E) :
    tS (qwTop d) (qwDigit d w) (192 / d + qwRestN d) = eToNat w := by
  have hd14 := hs.1
  have hper : 192 / d * d ≤ 192 := Nat.div_mul_le_self 192 d
  set N := 192 / d
  have htop : ∀ t ≤ N, qwTop d t = t * d := fun t ht ↦ by
    unfold qwTop
    split_ifs with h
    · rfl
    · rw [show t = N by omega, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      exact Nat.min_eq_right hper
  have hrw := hs.2.2.2.2.2.2.1
  have hmono : ∀ t < N + qwRestN d, qwTop d t ≤ qwTop d (t + 1) := fun t ht ↦ by
    by_cases h : t < N
    · rw [htop t h.le, htop (t + 1) h]; exact Nat.mul_le_mul_right _ (by omega)
    · obtain ⟨e1, e2, -⟩ := hrw (t - N) (by omega)
      rw [show N + (t - N) = t by omega] at e1 e2
      omega
  have h0 : qwTop d 0 = 0 := by rw [htop 0 (Nat.zero_le _), Nat.zero_mul]
  rw [tS_digits h0 hmono (fun t ht ↦ ?_) _ le_rfl, hs.2.2.2.2.2.2.2, Nat.mod_eq_of_lt (qw_eToNat_lt w)]
  by_cases h : t < N
  · rw [htop t h.le, htop (t + 1) h, show (t + 1) * d - t * d = d by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]]
    simp only [qwDigit, N, h, ↓reduceIte, qwPosOf]
  · obtain ⟨e1, e2, -⟩ := hrw (t - N) (by omega)
    rw [show N + (t - N) = t by omega] at e1 e2
    rw [← e1, ← e2, Nat.add_sub_cancel_left]
    simp only [qwDigit, N, h, ↓reduceIte, qwRestOf]

/-! ## The hints as the interpreter computes them -/

/-- `WindowsExp`'s value of one window of `width` bits of `x` from bit `start` (Interp's
`execHint`, `count = 1`). -/
def winHintVal (x : E) (start width : ℕ) : ℕ :=
  (List.range width).foldl (fun acc j ↦ acc + if wordBit x (start + 0 * width + j) then 2 ^ j else 0) 0

theorem qw_kToNat_lt (a : K) : kToNat a < 2 ^ 64 := a.toBitVec.isLt

/-- The bit `r < 64` of a limb `c < 2^64` under higher limbs. -/
theorem div_two_pow_mod_two_limb (c H r : ℕ) (hc : c < 2 ^ 64) (hr : r < 64) :
    (c + 2 ^ 64 * H) / 2 ^ r % 2 = c / 2 ^ r % 2 := by
  have hc' := hc
  have : 2 ^ 64 * H = 2 ^ r * (2 * (2 ^ (63 - r) * H)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]
    congr 2; omega
  rw [this, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem limbBit_eq (c0 c1 c2 : ℕ) (h0 : c0 < 2 ^ 64) (h1 : c1 < 2 ^ 64) {i : ℕ}
    (hi : i < 192) :
    (if i / 64 = 0 then c0 else if i / 64 = 1 then c1 else c2) / 2 ^ (i % 64) % 2 =
      (c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2) / 2 ^ i % 2 := by
  have hr : i % 64 < 64 := Nat.mod_lt _ (by decide)
  have hsplit : i = 64 * (i / 64) + i % 64 := (Nat.div_add_mod i 64).symm
  rcases (show i / 64 = 0 ∨ i / 64 = 1 ∨ i / 64 = 2 by omega) with hq | hq | hq
  · rw [ite_pos' hq]
    conv_rhs => rw [hsplit, hq, Nat.mul_zero, Nat.zero_add]
    rw [show c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 = c0 + 2 ^ 64 * (c1 + 2 ^ 64 * c2) by ring,
      div_two_pow_mod_two_limb _ _ _ h0 hr]
  · rw [ite_neg' (by omega), ite_pos' hq]
    conv_rhs => rw [hsplit, hq, Nat.mul_one, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    rw [show c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 = c0 + 2 ^ 64 * (c1 + 2 ^ 64 * c2) by ring,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0, Nat.zero_add,
      div_two_pow_mod_two_limb _ _ _ h1 hr]
  · rw [ite_neg' (by omega), ite_neg' (by omega)]
    conv_rhs => rw [hsplit, hq, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    rw [show c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 = (c0 + 2 ^ 64 * c1) + 2 ^ 128 * c2 by ring,
      Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (show c0 + 2 ^ 64 * c1 < 2 ^ 128 by omega), Nat.zero_add]

/-- **`wordBit` is the integer's bit.** -/
theorem wordBit_eq (x : E) {i : ℕ} (hi : i < 192) :
    wordBit x i = decide ((eToNat x >>> i) % 2 = 1) := by
  have hn := limbBit_eq _ _ (kToNat (x.limb 2)) (qw_kToNat_lt (x.limb 0)) (qw_kToNat_lt (x.limb 1)) hi
  rw [Nat.shiftRight_eq_div_pow]
  exact congrArg (fun n : ℕ ↦ decide (n = 1)) hn

/-- **The interpreter's window value is the word's integer, shifted and cut.** -/
theorem winHintVal_eq (x : E) {start width : ℕ} (h : start + width ≤ 192) :
    winHintVal x start width = (eToNat x >>> start) % 2 ^ width := by
  unfold winHintVal
  simp only [Nat.zero_mul, Nat.add_zero]
  induction width with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [wordBit_eq x (by omega), Nat.pow_succ, Nat.mod_mul, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    have hb := Nat.mod_lt (eToNat x / 2 ^ (start + n)) (show 0 < 2 by decide)
    rcases (show eToNat x / 2 ^ (start + n) % 2 = 0 ∨ eToNat x / 2 ^ (start + n) % 2 = 1 by omega)
      with e | e <;> simp [e]

theorem qw_gpowE_eq {n : ℕ} (h : n < 2 ^ 64) : gpowE n = gen ^ n := by
  rw [gpowE, gpowK_eq (by unfold u128Bound; omega), gen_pow_eq_ofK]

/-- **The honest windows are the interpreter's hints**: window `i` of position `j` is `g^` the
hint's value of the window's bits of the word, at the window's place `j·d + off`. -/
theorem qwVal_hint {d cd : ℕ} (hs : QwShape d cd) (w : E) {j i : ℕ} (hj : j < 192 / d)
    (hi : i < qwN d cd) :
    gen ^ qwVal d cd (qwPosOf d w j) i =
      gpowE (winHintVal w (j * d + (qwWin d cd i).1) (qwWin d cd i).2) := by
  obtain ⟨hw1, hw7, -, hd⟩ := hs.2.2.2.2.2.1 i hi
  have hjd : j * d + d ≤ 192 := by
    have := Nat.div_mul_le_self 192 d
    have : (j + 1) * d ≤ 192 / d * d := Nat.mul_le_mul_right _ hj
    nlinarith
  rw [winHintVal_eq w (by omega), qw_gpowE_eq (lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
    (Nat.pow_le_pow_right (by decide) (by omega)))]
  congr 1
  have hp : 2 ^ d = 2 ^ (qwWin d cd i).1 * 2 ^ (d - (qwWin d cd i).1) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [qwVal, qwPosOf, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, hp, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

end
end LeanVM.Guest.B1
