/-
  LeanVM.Guest.B1.Opening.QueriesRun

  `opening_queries`' value is the Spec's `enforcedSum`: the chain against the powers of `λ`, and a
  row's dot product with the tensor weights against the dot product with `eqKernel`.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning

/-!
# `opening_queries` against `enforcedSum` (V:1694)

* `oqChain_powers`: the chain `h ← (h + d_k)·λ⁻¹` times `λ^Q` is `Σ_k λ^k d_k`, in the order
  `enforcedSum` sums (its weights `powers λ Q`, V:184): `enforcedSum_eq`.
* `eqKernel_getD'`, `eqW_append`: entry `w` of `eqKernel` is the product `eqW`, which splits at
  any coordinate.
* `rowDot_level0`, `rowDot_deeper`: with the weights `opening_row_weights` writes
  (`MeaningOpeningRowWeights 6 1`, `… 4 0`), a row's `rowDot` is `dot (row.reverse.map ofK)
  (eqKernel folds)` at level 0 and `dot (extRow row) (eqKernel folds)` deeper, the Spec's
  `enforcedSum` terms (`whirLevels`, V:1811-1813).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The chain against the powers of `λ` -/

/-- `Σ_{k < n} λ^k d_k`, left to right. -/
def powSum (lam : E) (ds : ℕ → E) (n : ℕ) : E :=
  ((List.range n).map fun k ↦ lam ^ k * ds k).foldl (· + ·) 0

theorem powSum_succ (lam : E) (ds : ℕ → E) (n : ℕ) :
    powSum lam ds (n + 1) = powSum lam ds n + lam ^ n * ds n := by
  simp [powSum, List.range_succ, List.foldl_append]

/-- **The chain is `Σ_k λ^k d_k`** once multiplied by `λ^Q`. -/
theorem oqChain_powers {lam : E} (hlam : lam ≠ 0) {odd base : ℕ} (hodd : odd ≤ 1)
    (hb : base = 1 ∨ (base = 0 ∧ odd = 0)) (ds : ℕ → E) (N : ℕ) :
    oqChain odd base lam⁻¹ ds N * lam ^ oqCount odd base N = powSum lam ds (oqCount odd base N) := by
  have hinv : lam⁻¹ * lam = 1 := by rw [mul_comm]; exact e_mul_inv_cancel hlam
  induction N with
  | zero =>
    rcases hb with hb | ⟨hb, ho⟩
    · subst hb
      rcases Nat.lt_or_ge odd 1 with h | h
      · obtain rfl : odd = 0 := by omega
        rw [show oqCount 0 1 0 = 0 from rfl, show oqChain 0 1 lam⁻¹ ds 0 = 0 from rfl]
        simp [powSum]
      · obtain rfl : odd = 1 := by omega
        simp only [oqChain, oqCount, ↓reduceIte, Nat.mul_zero, Nat.add_zero, pow_one]
        rw [show powSum lam ds 1 = powSum lam ds 0 + lam ^ 0 * ds 0 from powSum_succ _ _ _]
        simp only [powSum, List.range_zero, List.map_nil, List.foldl_nil, pow_zero, one_mul,
          zero_add]
        rw [mul_assoc, hinv, mul_one]
    · subst hb ho
      rw [show oqCount 0 0 0 = 0 from rfl, show oqChain 0 0 lam⁻¹ ds 0 = 0 from rfl]
      simp [powSum]
  | succ N ih =>
    rcases hb with hb | ⟨hb, ho⟩
    · subst hb
      simp only [oqChain, oqCount, ↓reduceIte] at ih ⊢
      rw [show odd + 2 * (N + 1) = odd + 2 * N + 1 + 1 by ring, powSum_succ, powSum_succ, ← ih,
        pow_succ, pow_succ]
      linear_combination ((oqChain odd 1 lam⁻¹ ds N + ds (odd + 2 * N)) * lam ^ (odd + 2 * N) *
        (lam⁻¹ * lam + 1) + ds (odd + 2 * N + 1) * lam ^ (odd + 2 * N) * lam) * hinv
    · subst hb ho
      simp only [oqChain, oqCount, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at ih ⊢
      rw [powSum_succ, ← ih, pow_succ]
      linear_combination ((oqChain 0 0 lam⁻¹ ds N + ds N) * lam ^ N) * hinv

theorem powersFrom_getD (acc base : E) : ∀ (n k : ℕ), k < n →
    (powersFrom acc base n).getD k 0 = acc * base ^ k
  | 0, _, h => absurd h (by omega)
  | n + 1, 0, _ => by simp [powersFrom]
  | n + 1, k + 1, h => by
    simp only [powersFrom, List.getD_cons_succ]
    rw [powersFrom_getD _ _ n k (by omega), pow_succ]
    ring

theorem length_powersFrom (acc base : E) : ∀ n, (powersFrom acc base n).length = n
  | 0 => rfl
  | n + 1 => by simp [powersFrom, length_powersFrom _ _ n]

/-- **`enforcedSum` with the powers of `λ`** (V:1694): `Σ_k λ^k ⟨row_k, eqKernel folds⟩`. -/
theorem enforcedSum_eq (rows : List (List E)) (folds : List E) (lam : E) :
    enforcedSum rows folds (powers lam rows.length) =
      powSum lam (fun k ↦ dot (rows.getD k []) (eqKernel folds)) rows.length := by
  unfold enforcedSum powSum
  have hz : (List.zip (powers lam rows.length) rows) =
      (List.range rows.length).map fun k ↦ (lam ^ k, rows.getD k []) := by
    apply List.ext_getElem
    · simp [powers, length_powersFrom]
    · intro i h1 h2
      simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
      have hi : i < rows.length := by simpa [powers, length_powersFrom] using h1
      have hpl : i < (powers lam rows.length).length := by simp [powers, length_powersFrom, hi]
      have := powersFrom_getD 1 lam rows.length i hi
      rw [one_mul] at this
      rw [List.getD_eq_getElem _ _ hi]
      refine Prod.ext ?_ rfl
      rw [← List.getD_eq_getElem _ 0 hpl]
      exact this
  rw [hz, List.foldl_map, List.foldl_map]

/-! ## The equality weights -/

/-- Entry `w` of the equality kernel: the product over the coordinates of `r` (bit set) or
`1 + r`. -/
def eqW : List E → ℕ → E
  | [], _ => 1
  | r :: rs, w => (if w % 2 = 1 then r else 1 + r) * eqW rs (w / 2)

theorem eqW_mod : ∀ (pt : List E) (w : ℕ), eqW pt w = eqW pt (w % 2 ^ pt.length)
  | [], _ => rfl
  | r :: rs, w => by
    simp only [eqW, List.length_cons, pow_succ, mul_comm (2 ^ rs.length) 2,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self]
    rw [← eqW_mod rs]

theorem eqW_append : ∀ (a b : List E) (w : ℕ), eqW (a ++ b) w = eqW a w * eqW b (w / 2 ^ a.length)
  | [], b, w => by simp [eqW]
  | r :: a, b, w => by
    simp only [List.cons_append, eqW, eqW_append a b, List.length_cons, pow_succ,
      Nat.div_div_eq_div_mul, mul_comm (2 ^ a.length) 2, mul_assoc]

theorem eqKernel_append' (pt : List E) (r : E) :
    eqKernel (pt ++ [r]) = (eqKernel pt).map (· * (1 + r)) ++ (eqKernel pt).map (· * r) := by
  unfold eqKernel
  rw [List.foldl_concat]

theorem length_eqKernel' (pt : List E) : (eqKernel pt).length = 2 ^ pt.length := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernel_append', List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

theorem getD_map_mul' (l : List E) (c : E) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

theorem eqW_snoc (pt : List E) (r : E) (w : ℕ) :
    eqW (pt ++ [r]) w = eqW pt w * (if w / 2 ^ pt.length % 2 = 1 then r else 1 + r) := by
  rw [eqW_append]; simp [eqW]

/-- **`eq_kernel` lists the equality weights.** -/
theorem eqKernel_getD' (pt : List E) (w : ℕ) (hw : w < 2 ^ pt.length) :
    (eqKernel pt).getD w 0 = eqW pt w := by
  induction pt using List.reverseRecOn generalizing w with
  | nil =>
    obtain rfl : w = 0 := by simpa using hw
    rfl
  | append_singleton pt r ih =>
    have hlen := length_eqKernel' pt
    simp only [List.length_append, List.length_singleton] at hw
    rw [eqKernel_append', eqW_snoc]
    by_cases h : w < 2 ^ pt.length
    · rw [List.getD_append _ _ _ _ (by simpa [hlen] using h), getD_map_mul', ih w h,
        Nat.div_eq_of_lt h]
      simp
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega), List.length_map, hlen,
        getD_map_mul', ih _ (by rw [pow_succ] at hw; omega), eqW_mod pt w,
        eqW_mod pt (w - 2 ^ pt.length), ← Nat.mod_eq_sub_mod (by omega),
        show w / 2 ^ pt.length = 1 from Nat.div_eq_of_lt_le (by omega) (by rw [pow_succ] at hw; omega)]
      simp

/-! ## Sums -/

theorem foldl_sum_range (f : ℕ → E) (n : ℕ) :
    ((List.range n).map f).foldl (· + ·) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.foldl_append, ih, Finset.sum_range_succ]; rfl

theorem dot_eq_sum (l r : List E) {n : ℕ} (hl : l.length = n) (hr : r.length = n) :
    dot l r = ∑ i ∈ Finset.range n, l.getD i 0 * r.getD i 0 := by
  have hz : List.zipWith (· * ·) l r = (List.range n).map fun i ↦ l.getD i 0 * r.getD i 0 := by
    apply List.ext_getElem
    · simp [hl, hr]
    · intro i h1 h2
      simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ (by simp at h1; omega), List.getD_eq_getElem _ _ (by simp at h1; omega)]
  rw [dot, hz, foldl_sum_range]

theorem sum_range_mul_split (a b : ℕ) (f : ℕ → E) :
    ∑ j ∈ Finset.range (a * b), f j = ∑ h ∈ Finset.range b, ∑ l ∈ Finset.range a, f (a * h + l) := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem rowDot_sum (base I : ℕ) (row : List K) (w : ℕ → E) :
    rowDot base I row w = ∑ j ∈ Finset.range (rowLo I * (I / rowLo I)),
      rowWord base row j * w (j % rowLo I) * w (rowLo I + j / rowLo I) := by
  set lo := rowLo I with hlo
  rw [rowDot, ← hlo, foldl_sum_range, sum_range_mul_split]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [foldl_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rcases Nat.eq_zero_or_pos lo with h0 | hpos
  · omega
  rw [show (lo * h + l) % lo = l by rw [Nat.add_comm, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hl',
    show (lo * h + l) / lo = h by rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hl', zero_add]]
  ring

/-! ## A row's dot product -/

theorem rowLo_64 : rowLo 64 = 8 := rfl
theorem rowLo_16 : rowLo 16 = 8 := rfl

/-- **Level 0** (`base = 1`, the weights `opening_row_weights__L6_L1` writes, reversed): the row's
dot product is `dot (row.reverse.map ofK) (eqKernel folds)` (`whirLevels`' rows, V:1811). -/
theorem rowDot_level0 {row : List K} (hrow : row.length = 64) {rs : List E} (hrs : rs.length = 6)
    {w : ℕ → E} (hlo : ∀ i < 8, w i = (eqKernel (rs.take 3)).getD (7 - i) 0)
    (hhi : ∀ i < 8, w (8 + i) = (eqKernel (rs.drop 3)).getD (7 - i) 0) :
    rowDot 1 64 row w = dot (row.reverse.map ofK) (eqKernel rs) := by
  have ht : (rs.take 3).length = 3 := by simp [hrs]
  have hd : (rs.drop 3).length = 3 := by simp [hrs]
  rw [rowDot_sum, rowLo_64, dot_eq_sum _ _ (n := 64) (by simp [hrow])
    (by rw [length_eqKernel', hrs]; rfl), show 8 * (64 / 8) = 64 from rfl]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [hlo _ (Nat.mod_lt _ (by decide)), hhi _ (by omega), eqKernel_getD' _ _ (by rw [ht]; omega),
    eqKernel_getD' _ _ (by rw [hd]; omega), eqKernel_getD' _ _ (by rw [hrs]; omega)]
  rw [show rs = rs.take 3 ++ rs.drop 3 from (List.take_append_drop 3 rs).symm, eqW_append, ht,
    eqW_mod (rs.take 3) (64 - 1 - j), ht]
  simp only [List.take_append_drop]
  rw [show (64 - 1 - j) % 2 ^ 3 = 7 - j % 8 by omega, show (64 - 1 - j) / 2 ^ 3 = 7 - j / 8 by omega]
  have hr : (row.reverse.map ofK).getD (64 - 1 - j) 0 = ofK (row.getD j 0) := by
    rw [List.getD_eq_getElem _ _ (by simp [hrow]; omega), List.getElem_map, List.getElem_reverse,
      List.getD_eq_getElem _ _ (by omega)]
    congr 2; omega
  rw [hr]
  simp [rowWord]
  ring

theorem extRow_getD : ∀ (row : List K) (j : ℕ), 3 * j + 2 < row.length →
    (extRow row).getD j 0 = E.ofLimbs (row.getD (3 * j) 0) (row.getD (3 * j + 1) 0)
      (row.getD (3 * j + 2) 0)
  | c0 :: c1 :: c2 :: rest, 0, _ => by simp [extRow]
  | c0 :: c1 :: c2 :: rest, j + 1, h => by
    simp only [extRow, List.getD_cons_succ]
    rw [extRow_getD rest j (by simp at h; omega)]
    simp only [show 3 * (j + 1) = 3 * j + 3 by ring]
    rfl
  | [], _, h | [_], _, h | [_, _], _, h => by
    simp only [List.length_cons, List.length_nil] at h; omega

theorem length_extRow_mul3 : ∀ (row : List K) (n : ℕ), row.length = 3 * n → (extRow row).length = n
  | c0 :: c1 :: c2 :: rest, n + 1, h => by
    simp only [extRow, List.length_cons]
    rw [length_extRow_mul3 rest n (by simp at h; omega)]
  | [], 0, _ => rfl
  | [], _ + 1, h | [_], _, h | [_, _], _, h | _ :: _ :: _ :: _, 0, h => by
    simp only [List.length_cons, List.length_nil] at h; omega

/-- **Deeper levels** (`base = 0`, the weights `opening_row_weights__L4_L0` writes): the row's
dot product is `dot (extRow row) (eqKernel folds)` (`whirLevels`' rows, V:1813). -/
theorem rowDot_deeper {row : List K} (hrow : row.length = 48) {rs : List E} (hrs : rs.length = 4)
    {w : ℕ → E} (hlo : ∀ i < 8, w i = (eqKernel (rs.take 3)).getD i 0)
    (hhi : ∀ i < 2, w (8 + i) = (eqKernel (rs.drop 3)).getD i 0) :
    rowDot 0 16 row w = dot (extRow row) (eqKernel rs) := by
  have ht : (rs.take 3).length = 3 := by simp [hrs]
  have hd : (rs.drop 3).length = 1 := by simp [hrs]
  rw [rowDot_sum, rowLo_16, dot_eq_sum _ _ (n := 16) (length_extRow_mul3 row 16 hrow)
    (by rw [length_eqKernel', hrs]; rfl), show 8 * (16 / 8) = 16 from rfl]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [hlo _ (Nat.mod_lt _ (by decide)), hhi _ (by omega), eqKernel_getD' _ _ (by rw [ht]; omega),
    eqKernel_getD' _ _ (by rw [hd]; omega), eqKernel_getD' _ _ (by rw [hrs]; omega),
    extRow_getD row j (by omega)]
  rw [show rs = rs.take 3 ++ rs.drop 3 from (List.take_append_drop 3 rs).symm, eqW_append, ht,
    eqW_mod (rs.take 3) j, ht]
  simp only [List.take_append_drop, rowWord, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
  rw [show j % 2 ^ 3 = j % 8 from rfl, show j / 2 ^ 3 = j / 8 from rfl]
  ring

end
end LeanVM.Guest.B1
