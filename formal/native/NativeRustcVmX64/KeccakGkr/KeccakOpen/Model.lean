module

public import NativeRustcVm.KeccakGkr.Open
public import NativeRustcVm.KeccakGkr.Rep

/-!
# `keccak_open`'s in-place fold, flat

The rows region holds 64 rows of 64 elements. Entry `z` of row `r` after the first `t` challenges
is `W sl rows t r z`. The region's contents at the start of round `t` (`Fr`): the first
`64 / 2 ^ t` rows those of round `t`, the others left from earlier rounds; during round `t` at row
`i`, entry `j` (`F`): the rows below `i` and the first `j` entries of row `i` already folded.
An entry folded (`F_step`, `W_succ`), a row done (`F_row`), a round done (`F_half`), the end
(`Fr_six`).
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeVm.Model NativeRustcVm.KeccakGkr

@[expose] public section

/-- Entry `z` of row `r` after the first `t` challenges. -/
def W (sl : Array EW) (rows : Array (Array EW)) (t r z : Nat) : EW :=
  ((openRows sl rows t).getD r #[]).getD z 0

/-- The rows round `t` folds into: half of its `64 / 2 ^ t`. -/
def half (t : Nat) : Nat := 32 / 2 ^ t

/-- The rows region's contents at the start of round `t`. -/
def Fr (sl : Array EW) (rows : Array (Array EW)) : Nat → Nat → EW
  | 0, n => (rowsFlat rows).getD n 0
  | t + 1, n => if n / 64 < half t then W sl rows (t + 1) (n / 64) (n % 64) else Fr sl rows t n

/-- The rows region's contents in round `t`, at row `i`, entry `j`. -/
def F (sl : Array EW) (rows : Array (Array EW)) (t i j n : Nat) : EW :=
  if n / 64 < i ∨ (n / 64 = i ∧ n % 64 < j) then W sl rows (t + 1) (n / 64) (n % 64)
  else Fr sl rows t n

/-- A fold's entry: `lo + c (lo + hi)`. -/
def foldE (c : EW) (lo hi : Nat → EW) (z : Nat) : EW := lo z + c * (lo z + hi z)

end

public section

variable {sl : Array EW} {rows : Array (Array EW)}

theorem half_eq (t : Nat) : 64 / 2 ^ (t + 1) = half t := by
  rw [half, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

/-- The rows of every round have 64 entries; round `t` has `64 / 2 ^ t` of them. -/
theorem openRows_shape (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {t : Nat} (ht : t ≤ sl.size) :
    (openRows sl rows t).size = 64 / 2 ^ t ∧
      ∀ r < 64 / 2 ^ t, ((openRows sl rows t).getD r #[]).size = 64 := by
  have h1 := openRows_size sl rows ht
  rw [hsz] at h1
  refine ⟨h1, fun r hr ↦ openRows_row_size sl rows (fun r hr ↦ hrow r (by omega)) ht r
    (by omega)⟩

/-- **A fold's entry**: entry `z` of row `i` after round `t` from rows `2 i`, `2 i + 1`. -/
theorem W_succ (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {t i z : Nat} (ht : t < sl.size) (hi : i < half t) (hz : z < 64) :
    W sl rows (t + 1) i z =
      foldE (sl.getD t 0) (W sl rows t (2 * i)) (W sl rows t (2 * i + 1)) z := by
  obtain ⟨hs, hr⟩ := openRows_shape (sl := sl) hsz hrow (t := t) (by omega)
  have hh : half t = 64 / 2 ^ t / 2 := by
    rw [← half_eq, Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [W, openRows_succ_getD sl rows ht (by rw [hs]; omega),
    foldRow_getD _ (hr _ (by omega)) (hr _ (by omega)) hz]
  rfl

/-- **The contents at the start of a round** are its rows'. -/
theorem Fr_eq (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64) :
    ∀ {t : Nat}, t ≤ sl.size → ∀ {n : Nat}, n / 64 < 64 / 2 ^ t →
      Fr sl rows t n = W sl rows t (n / 64) (n % 64)
  | 0, _, n, hn => by
    have hr : n / 64 < rows.size := by rw [hsz]; simpa using hn
    have := rowsFlat_getElem? rows (fun r hr ↦ hrow r (by omega)) hr (Nat.mod_lt n (by decide))
    rw [show 64 * (n / 64) + n % 64 = n by omega] at this
    rw [Fr, rowsFlat, List.getD_eq_getElem?_getD, this, Option.getD_some, W, openRows_zero]
  | t + 1, _, n, hn => by
    rw [half_eq] at hn
    rw [Fr, ite_eq_left hn]

theorem F_zero (t : Nat) : F sl rows t 0 0 = Fr sl rows t := by
  funext n
  simp [F]

theorem F_row (t i : Nat) : F sl rows t i 64 = F sl rows t (i + 1) 0 := by
  funext n
  unfold F
  have := Nat.mod_lt n (show 64 > 0 by decide)
  split_ifs <;> first | rfl | omega

theorem F_half (t : Nat) : F sl rows t (half t) 0 = Fr sl rows (t + 1) := by
  funext n
  unfold F
  rw [Fr]
  split_ifs <;> first | rfl | omega

/-- A row of `F` before the one being folded: round `t`'s. -/
theorem F_old {t i n : Nat} (h : i < n / 64) : F sl rows t i 0 n = Fr sl rows t n := by
  unfold F
  split_ifs <;> first | rfl | omega

/-- **An entry folded**: entry `j` of row `i`. -/
theorem F_step {t i j : Nat} (hj : j < 64) (n : Nat) :
    F sl rows t i (j + 1) n =
      if n = 64 * i + j then W sl rows (t + 1) i j else F sl rows t i j n := by
  unfold F
  split_ifs <;> first | rfl | omega | rw [show n / 64 = i by omega, show n % 64 = j by omega]

/-- The rows `2 i`, `2 i + 1` of round `t` at row `i`: round `t`'s. -/
theorem F_pair (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {t i : Nat} (ht : t < sl.size) (hi : i < half t) {b z : Nat} (hb : b < 2) (hz : z < 64) :
    F sl rows t i 0 (64 * (2 * i + b) + z) = W sl rows t (2 * i + b) z := by
  have h1 : (64 * (2 * i + b) + z) / 64 = 2 * i + b := by omega
  have h2 : (64 * (2 * i + b) + z) % 64 = z := by omega
  have hh : 2 * i + b < 64 / 2 ^ t := by
    have : half t = 64 / 2 ^ t / 2 := by
      rw [← half_eq, Nat.pow_succ, Nat.div_div_eq_div_mul]
    omega
  have hc : ¬((64 * (2 * i + b) + z) / 64 < i ∨
      ((64 * (2 * i + b) + z) / 64 = i ∧ (64 * (2 * i + b) + z) % 64 < 0)) := by omega
  unfold F
  rw [ite_eq_right hc, Fr_eq hsz hrow (by omega) (by rw [h1]; exact hh), h1, h2]

/-- **The end**: entry `z < 64` after six rounds is row `0`'s of the full fold. -/
theorem Fr_six (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    (hsl : sl.size = 6) {z : Nat} (hz : z < 64) :
    Fr sl rows 6 z = W sl rows 6 0 z := by
  rw [Fr_eq hsz hrow (by omega) (by rw [show z / 64 = 0 by omega]; decide),
    show z / 64 = 0 by omega, Nat.mod_eq_of_lt hz]

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
