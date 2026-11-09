/-
  LeanVM.Guest.B1.Da.VectorMath

  The product trees of `da_vector` compute the dual codeword: the top leaves (`topLeaf_eq`) and a
  column's leaves (`cellLeaf_eq`), from `Ŵ_j`'s additivity over the bits of a point.
-/

module

public import LeanVM.Guest.B1.Da.VectorDefs
public import LeanVM.Parameters.Field
public import LeanVM.Guest.Value.Tower

/-!
# The product trees compute the dual codeword

`wK j x` sums `Ŵ_j(e_c)` over the bits `c ≥ j` of `x` (`wK_congr`: only those bits matter); at a
node splitting bit `j`, the factor's point (the bits above `j`), the shift's (the bits of the
cell index) and the bit `j` itself make up the point (`wK_level`). So leaf `e` of column `h`'s
tree, `da_expand` from the top leaf `h` with the cell factors and the column's shifts, is
`dualAt z (256 h + e)` (`cellLeaf_eq`), and leaf `h` of the tree over the cell index is `topLeaf z h`
(`topLeaf_eq`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Guest.Value

@[expose] public section

/-! ## `wK` on bits -/

theorem omegaK_self : ∀ j < 14, omegaK j j = 1 := by decide +kernel

/-- `wK j` reads only the bits from `j` up. -/
theorem wK_congr {j x x' : ℕ} (h : ∀ c < 15, j ≤ c → x.testBit c = x'.testBit c) :
    wK j x = wK j x' := by
  unfold wK
  refine congrArg _ (List.map_congr_left fun c hc ↦ ?_)
  by_cases hcj : c < j
  · simp [omegaK, hcj]
  · rw [h c (List.mem_range.mp hc) (by omega)]

theorem sum_range_single (f : ℕ → K) {j : ℕ} :
    ∀ n, j < n → ((List.range n).map fun c ↦ if c = j then f c else 0).sum = f j
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.lt_or_ge j n with hj | hj
    · rw [sum_range_single f n hj]
      simp [show n ≠ j by omega]
    · have hz : ((List.range n).map fun c ↦ if c = j then f c else 0).sum = 0 := by
        refine List.sum_eq_zero fun v hv ↦ ?_
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
        simp [show c ≠ j by have := List.mem_range.mp hc; omega]
      rw [hz, show j = n by omega]
      simp

/-- **One level**: the bits of `x` above `j` are those of `A` and `B`, disjoint, both without
bits up to `j`; then `wK j x` is theirs and bit `j` of `x`. -/
theorem wK_level {j x A B : ℕ} (hj : j < 14)
    (hab : ∀ c < 15, j < c → x.testBit c = (A.testBit c || B.testBit c) ∧
      ¬(A.testBit c = true ∧ B.testBit c = true))
    (hA : ∀ c < 15, c ≤ j → A.testBit c = false) (hB : ∀ c < 15, c ≤ j → B.testBit c = false) :
    wK j x = wK j A + wK j B + if x.testBit j then 1 else 0 := by
  have hbit : (if x.testBit j then (1 : K) else 0) =
      ((List.range 15).map fun c ↦ if c = j then (if x.testBit j then omegaK j c else 0) else 0).sum := by
    rw [sum_range_single (fun c ↦ if x.testBit j then omegaK j c else 0) 15 (by omega),
      omegaK_self j hj]
  rw [hbit]
  unfold wK
  rw [← List.sum_map_add, ← List.sum_map_add]
  refine congrArg _ (List.map_congr_left fun c hc ↦ ?_)
  have hc15 := List.mem_range.mp hc
  rcases Nat.lt_trichotomy c j with hcj | rfl | hcj
  · simp [omegaK, hcj, show c ≠ j by omega]
  · simp [hA c hc15 le_rfl, hB c hc15 le_rfl]
  · obtain ⟨hx, hd⟩ := hab c hc15 hcj
    rw [hx]
    cases ha : A.testBit c <;> cases hb : B.testBit c <;> simp_all [show c ≠ j by omega]

theorem testBit_256_mul_add {h e c : ℕ} (he : e < 256) :
    (256 * h + e).testBit c = if c < 8 then e.testBit c else h.testBit (c - 8) := by
  rw [show 256 * h + e = 2 ^ 8 * h + e by norm_num, Nat.testBit_two_pow_mul_add h (by norm_num [he])]

theorem testBit_256_mul {h c : ℕ} :
    (256 * h).testBit c = (decide (c ≥ 8) && h.testBit (c - 8)) := by
  rw [show 256 * h = 2 ^ 8 * h by norm_num, Nat.testBit_two_pow_mul]

theorem testBit_high_mul {m j c : ℕ} :
    (m * 2 ^ (j + 1)).testBit c = (decide (j + 1 ≤ c) && m.testBit (c - (j + 1))) :=
  Nat.testBit_mul_two_pow m c (j + 1)

theorem testBit_lt_eq_false {e c n : ℕ} (he : e < 2 ^ n) (hc : n ≤ c) : e.testBit c = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) hc))

/-! ## The factors -/

theorem log_two_pow_add {k m : ℕ} (hm : m < 2 ^ k) : Nat.log 2 (2 ^ k + m) = k :=
  Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)

theorem factorAt_node (Z : ℕ → E) {top k m : ℕ} (hm : m < 2 ^ k) :
    factorAt Z top (2 ^ k + m) = Z (top - k) * ofK (wK (top - k) (m * 2 ^ (top - k + 1))) + 1 := by
  rw [factorAt, log_two_pow_add hm, Nat.add_sub_cancel_left]

/-! ## A column's leaves -/

/-- The dual codeword's factor `j` at point `x`. -/
def dualFactor (z : E) (x j : ℕ) : E := 1 + z ^ 2 ^ j * ofK (wK j x)

theorem prod_range_reflect' (f : ℕ → E) (n : ℕ) :
    ((List.range n).map fun k ↦ f (n - 1 - k)).prod = ((List.range n).map f).prod := by
  rw [LeanDa.prod_map_range, LeanDa.prod_map_range]
  exact Finset.prod_range_reflect f n

/-- **A column's tree computes the dual codeword**: leaf `e` of `da_expand` from the top leaf
`h`, with the cell factors and the shifts `z_j Ŵ_j(256 h)`, is `dualAt z (256 h + e)`. -/
theorem cellLeaf_eq (z : E) {h e : ℕ} (he : e < 256) :
    expandLeaf (topLeaf z h) (factorAt (zsVal z) 7) (zsVal z)
      (fun j ↦ zsVal z j * ofK (wK j (256 * h))) 7 8 e = dualAt z (256 * h + e) := by
  have hterm : ∀ k < 8, factorAt (zsVal z) 7 (2 ^ k + e >>> (8 - k)) +
      zsVal z (7 - k) * ofK (wK (7 - k) (256 * h)) +
      (if e.testBit (8 - 1 - k) then zsVal z (7 - k) else 0) = dualFactor z (256 * h + e) (7 - k) := by
    intro k hk
    have hm : e >>> (8 - k) < 2 ^ k := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by
        rw [← pow_add, show 8 - k + k = 8 by omega]; exact lt_of_lt_of_eq he (by norm_num))
    rw [factorAt_node _ hm, show 7 - k + 1 = 8 - k by omega, show 8 - 1 - k = 7 - k by omega]
    simp only [zsVal, show 7 - k < 14 by omega, ↓reduceIte]
    have hl := wK_level (j := 7 - k) (x := 256 * h + e) (A := e >>> (8 - k) * 2 ^ (8 - k))
      (B := 256 * h) (by omega) ?_ ?_ ?_
    · rw [dualFactor, hl, testBit_256_mul_add he]
      simp only [show 7 - k < 8 by omega, ↓reduceIte]
      rw [ofK_add, ofK_add]
      split_ifs <;> simp only [ofK_one, ofK_zero] <;> ring
    · intro c hc hjc
      rw [testBit_256_mul_add he, show 8 - k = 7 - k + 1 by omega, testBit_high_mul,
        testBit_256_mul, Nat.testBit_shiftRight]
      by_cases c8 : c < 8
      · simp [c8, show 7 - k + 1 ≤ c by omega, show 7 - k + 1 + (c - (7 - k + 1)) = c by omega]
      · have : e.testBit c = false := testBit_lt_eq_false (n := 8) (by omega) (by omega)
        simp [c8, show 7 - k + 1 ≤ c by omega, show 7 - k + 1 + (c - (7 - k + 1)) = c by omega,
          this, show c ≥ 8 by omega]
    · intro c _ hcj
      rw [show 8 - k = 7 - k + 1 by omega, testBit_high_mul]
      simp [show ¬ (7 - k + 1 ≤ c) by omega]
    · intro c _ hcj
      rw [testBit_256_mul]
      simp [show ¬ (c ≥ 8) by omega]
  have hcell : ((List.range 8).map fun k ↦ factorAt (zsVal z) 7 (2 ^ k + e >>> (8 - k)) +
      (fun j ↦ zsVal z j * ofK (wK j (256 * h))) (7 - k) +
      if e.testBit (8 - 1 - k) then zsVal z (7 - k) else 0).prod =
      ((List.range 8).map (dualFactor z (256 * h + e))).prod := by
    rw [← prod_range_reflect' (dualFactor z (256 * h + e)) 8]
    exact congrArg _ (List.map_congr_left fun k hk ↦ hterm k (List.mem_range.mp hk))
  have htop : topLeaf z h = ((List.range 6).map fun i ↦ dualFactor z (256 * h + e) (8 + i)).prod := by
    unfold topLeaf
    refine congrArg _ (List.map_congr_left fun i hi ↦ ?_)
    have hi6 := List.mem_range.mp hi
    rw [dualFactor, wK_congr (x := 256 * h + e) (x' := 256 * h) fun c _ hc ↦ by
      rw [testBit_256_mul_add he, testBit_256_mul]
      simp [show ¬ c < 8 by omega, show c ≥ 8 by omega]]
  rw [expandLeaf, hcell, htop, dualAt, LeanDa.prod_map_range, LeanDa.prod_map_range,
    LeanDa.prod_map_range, show (14 : ℕ) = 8 + 6 from rfl, Finset.prod_range_add, mul_comm]
  rfl

/-! ## The top leaves -/

/-- **The tree over the cell index computes the top leaves**: leaf `h` of `da_expand` from `1`
with the top factors, no shifts and `z_14 = 0`, is `topLeaf z h`. -/
theorem topLeaf_eq (z : E) {h : ℕ} (hh : h < 128) :
    expandLeaf 1 (factorAt (zsVal z) 14) (zsVal z) (fun _ ↦ 0) 14 7 h = topLeaf z h := by
  have hterm : ∀ k < 6, factorAt (zsVal z) 14 (2 ^ (k + 1) + h >>> (7 - (k + 1))) + 0 +
      (if h.testBit (7 - 1 - (k + 1)) then zsVal z (14 - (k + 1)) else 0) =
      dualFactor z (256 * h) (8 + (6 - 1 - k)) := by
    intro k hk
    have hm : h >>> (7 - (k + 1)) < 2 ^ (k + 1) := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by
        rw [← pow_add, show 7 - (k + 1) + (k + 1) = 7 by omega]; exact lt_of_lt_of_eq hh (by norm_num))
    rw [factorAt_node _ hm, show 14 - (k + 1) = 8 + (6 - 1 - k) by omega,
      show 8 + (6 - 1 - k) + 1 = 7 - (k + 1) + 8 by omega]
    simp only [zsVal, show 8 + (6 - 1 - k) < 14 by omega, ↓reduceIte]
    have hl := wK_level (j := 8 + (6 - 1 - k)) (x := 256 * h)
      (A := h >>> (7 - (k + 1)) * 2 ^ (7 - (k + 1) + 8)) (B := 0) (by omega) ?_ ?_ ?_
    · rw [dualFactor, hl, testBit_256_mul, show 7 - 1 - (k + 1) = 8 + (6 - 1 - k) - 8 by omega]
      simp only [show 8 + (6 - 1 - k) ≥ 8 by omega, decide_true, Bool.true_and]
      have h0 : wK (8 + (6 - 1 - k)) 0 = 0 := by
        unfold wK; refine List.sum_eq_zero fun v hv ↦ ?_
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv; simp
      rw [h0, ofK_add, ofK_add, ofK_zero]
      split_ifs <;> simp only [ofK_one, ofK_zero] <;> ring
    · intro c hc hjc
      rw [show 7 - (k + 1) + 8 = 8 + (6 - 1 - k) + 1 by omega, testBit_high_mul, testBit_256_mul,
        Nat.testBit_shiftRight, Nat.zero_testBit]
      simp [show 8 + (6 - 1 - k) + 1 ≤ c by omega, show c ≥ 8 by omega]
      congr 1
      omega
    · intro c _ hcj
      rw [show 7 - (k + 1) + 8 = 8 + (6 - 1 - k) + 1 by omega, testBit_high_mul]
      simp [show ¬ (8 + (6 - 1 - k) + 1 ≤ c) by omega]
    · intro c _ _
      exact Nat.zero_testBit c
  have hwk : ∀ i < 6, dualFactor z (256 * h) (8 + i) = 1 + z ^ 2 ^ (8 + i) * ofK (wK (8 + i) (256 * h)) :=
    fun _ _ ↦ rfl
  rw [expandLeaf, one_mul, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  have h0 : factorAt (zsVal z) 14 (2 ^ 0 + h >>> (7 - 0)) + (fun _ ↦ (0 : E)) (14 - 0) +
      (if h.testBit (7 - 1 - 0) then zsVal z (14 - 0) else 0) = 1 := by
    have h7 : h >>> 7 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (lt_of_lt_of_eq hh (by norm_num))
    simp [factorAt, zsVal, h7]
  rw [h0, one_mul]
  have hmap : ((List.range 6).map ((fun k ↦ factorAt (zsVal z) 14 (2 ^ k + h >>> (7 - k)) +
      (fun _ ↦ (0 : E)) (14 - k) + if h.testBit (7 - 1 - k) then zsVal z (14 - k) else 0) ∘
      Nat.succ)).prod = ((List.range 6).map fun k ↦ dualFactor z (256 * h) (8 + (6 - 1 - k))).prod :=
    congrArg _ (List.map_congr_left fun k hk ↦ hterm k (List.mem_range.mp hk))
  rw [hmap, prod_range_reflect' (fun i ↦ dualFactor z (256 * h) (8 + i)) 6, topLeaf]
  exact congrArg _ (List.map_congr_left fun i hi ↦ (hwk i (List.mem_range.mp hi)).symm)

end
end LeanVM.Guest.B1.Da
