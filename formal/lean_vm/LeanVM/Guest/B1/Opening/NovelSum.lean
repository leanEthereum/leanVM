/-
  LeanVM.Guest.B1.Opening.NovelSum

  `novel_eval`'s tree in closed form: the coefficients times the products of the `ws` their bits
  select.
-/

module

public import LeanVM.Guest.B1.Opening.FoldAlg

/-!
# `novel_eval` in closed form

`novelSum_eq`: `novelSum hs ws n nbits = Σ_(c < 2^nbits) hs_c Π_(t < nbits, c_t = 1) ws_t`, the
coefficients past `n` taken as `0` (`hs.take n`). Level `k` of the tree holds, at `m`, the sum over
the `2^k` coefficients from `2^k·m` (`getD_nvTree`), one level folding the pairs
(`getD_nvPair`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters

@[expose] public section

/-- The products of the `ws` from `i` that the bits of `c` below `k` select. -/
def bitProd (ws : ℕ → E) (i k c : ℕ) : E :=
  ∏ t ∈ Finset.range k, if c.testBit t then ws (i + t) else 1

theorem getD_nvPair (w : E) : ∀ (l : List E) (m : ℕ),
    (nvPair w l).getD m 0 = l.getD (2 * m) 0 + w * l.getD (2 * m + 1) 0
  | lo :: hi :: rest, 0 => by simp [nvPair]
  | lo :: hi :: rest, m + 1 => by
    rw [nvPair, List.getD_cons_succ, getD_nvPair w rest m]
    simp only [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.getD_cons_succ]
  | [lo], 0 => by simp [nvPair]
  | [lo], m + 1 => by simp [nvPair, List.getD_eq_getElem?_getD]
  | [], m => by simp [nvPair]

theorem sum_range_two_mul (f : ℕ → E) : ∀ N : ℕ,
    ∑ c ∈ Finset.range (2 * N), f c = ∑ c ∈ Finset.range N, (f (2 * c) + f (2 * c + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul f N, Finset.sum_range_succ, add_assoc]

theorem bitProd_two_mul (ws : ℕ → E) (i k c : ℕ) :
    bitProd ws i (k + 1) (2 * c) = bitProd ws (i + 1) k c := by
  unfold bitProd
  rw [Finset.prod_range_succ']
  have h0 : (2 * c).testBit 0 = false := by simp [Nat.testBit_zero]
  simp only [h0, Bool.false_eq_true, ↓reduceIte, mul_one]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  rw [show (2 * c).testBit (t + 1) = c.testBit t by
    rw [Nat.testBit_succ, show 2 * c / 2 = c by omega], show i + (t + 1) = i + 1 + t by ring]

theorem bitProd_two_mul_add_one (ws : ℕ → E) (i k c : ℕ) :
    bitProd ws i (k + 1) (2 * c + 1) = ws i * bitProd ws (i + 1) k c := by
  unfold bitProd
  rw [Finset.prod_range_succ']
  have h0 : (2 * c + 1).testBit 0 = true := by simp [Nat.testBit_zero]
  simp only [h0, ↓reduceIte, Nat.add_zero]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  rw [show (2 * c + 1).testBit (t + 1) = c.testBit t by
    rw [Nat.testBit_succ, show (2 * c + 1) / 2 = c by omega], show i + (t + 1) = i + 1 + t by ring]

/-- **Level `k` of `novel_eval`'s tree** at `m`: the `2^k` coefficients from `2^k·m`, each times the
`ws` its bits select. -/
theorem getD_nvTree (ws : ℕ → E) : ∀ (k i : ℕ) (l : List E) (m : ℕ),
    (nvTree ws k i l).getD m 0 =
      ∑ c ∈ Finset.range (2 ^ k), l.getD (2 ^ k * m + c) 0 * bitProd ws i k c
  | 0, i, l, m => by simp [nvTree, bitProd]
  | k + 1, i, l, m => by
    rw [nvTree, getD_nvTree ws k (i + 1), pow_succ', sum_range_two_mul]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [getD_nvPair, bitProd_two_mul, bitProd_two_mul_add_one,
      show 2 * (2 ^ k * m + c) = 2 * 2 ^ k * m + 2 * c by ring,
      show 2 * 2 ^ k * m + 2 * c + 1 = 2 * 2 ^ k * m + (2 * c + 1) by ring]
    ring

/-- **`novel_eval` in closed form.** -/
theorem novelSum_eq (hs : List E) (ws : ℕ → E) (n nbits : ℕ) :
    novelSum hs ws n nbits =
      ∑ c ∈ Finset.range (2 ^ nbits), (hs.take n).getD c 0 * bitProd ws 0 nbits c := by
  rw [novelSum, List.headD_eq_getD, getD_nvTree]
  simp only [Nat.mul_zero, Nat.zero_add]

end
end LeanVM.Guest.B1
