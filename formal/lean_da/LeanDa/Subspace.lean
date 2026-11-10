module

public import LeanDa.ReedSolomon

/-!
# The normalized subspace polynomials and the dual codeword the guest builds

The facts about `Ŵ_j`, the normalized subspace polynomial of the span of `e_0 … e_(j-1)`
(`normalizedSubspacePolynomial`, CompPoly's `normalizedW`), that the guest program's construction
of the dual codeword rests on (`membership.rs:22-56` at the leanVM commit `formal/leanvm-rev` names):

* **`Ŵ_j` at the basis.** `Ŵ_j(e_c) = 0` for `c < j` (`wHat_two_pow_of_lt`), `Ŵ_j(e_j) = 1`
  (`wHat_two_pow_self`), and `Ŵ_j` is additive (`wHat_add`), so at a point it is the sum of its
  values at the basis elements its bits pick (`wHat_point_eq_sum`, `map_point_mul`).
* **The table.** `subspaceRow i` tabulates `W_i`, the subspace polynomial of the span of
  `e_0 … e_(i-1)`, on `e_i … e_14` by `W_(i+1)(x) = W_i(x) (W_i(x) + W_i(e_i))`
  (`subspaceRow_eq`), so `subspaceEvaluations i` tabulates `Ŵ_i` (`subspaceEvaluations_eq`), and
  its subset sums `subspaceAbove j y` (`subspace_above`, the NTT's twiddles) are `Ŵ_j` at the point
  whose bits above `j` are `y`'s (`subspaceAbove_eq`).
* **The dual codeword.** `subspaceAt j i`, bit `j` of `i` plus `subspaceAbove j (i >> (j + 1))`, is
  `Ŵ_j` at point `i` (`subspaceAt_eq`), so the guest's `dualCodeword z` is `dualCodewordAt z`
  (`dualCodeword_eq_dualCodewordAt`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open Polynomial

namespace LeanDa

@[expose] public section

/-! ## The normalized subspace polynomials -/

/-- `Ŵ_s` as a function on `K`, indexed by a natural number: `normW s` for `s < 14`
(`normW_eval`). -/
noncomputable def wHat (s : ℕ) (x : K) : K :=
  (AdditiveNTT.normalizedW (ZMod 2) basis (Fin.ofNat 16 s)).eval x

/-- `W_s` as a function on `K`. -/
noncomputable def wSub (s : ℕ) (x : K) : K :=
  (AdditiveNTT.W (ZMod 2) basis (Fin.ofNat 16 s)).eval x

/-- `e_c = point (2^c)`. -/
theorem basis_ofNat {c : ℕ} (hc : c < 16) : basis (Fin.ofNat 16 c) = point (2 ^ c) := by
  simp [basis, point, Nat.mod_eq_of_lt hc]

/-- `normW j` is `Ŵ_j`. -/
theorem normW_eval (j : Fin 14) (x : K) : (normalizedSubspacePolynomial j).eval x = wHat j x := by
  have h : Fin.castLE (by omega) j = Fin.ofNat 16 j :=
    Fin.ext (by simp [Nat.mod_eq_of_lt (by omega : (j : ℕ) < 16)])
  rw [normalizedSubspacePolynomial, wHat, h]

/-- `Ŵ_s` as an additive map. -/
noncomputable def wHatHom (s : ℕ) : K →+ K :=
  ((AdditiveNTT.normalizedW_is_additive (ZMod 2) basis (Fin.ofNat 16 s)).mk' _).toAddMonoidHom

/-- `wHatHom s` is `Ŵ_s`. -/
theorem wHatHom_apply (s : ℕ) (x : K) : wHatHom s x = wHat s x := rfl

/-- `Ŵ_s` is additive. -/
theorem wHat_add (s : ℕ) (x y : K) : wHat s (x + y) = wHat s x + wHat s y :=
  map_add (wHatHom s) x y

/-- `Ŵ_s(0) = 0`. -/
theorem wHat_zero (s : ℕ) : wHat s 0 = 0 := map_zero (wHatHom s)

/-- The point of index `0` is `0`. -/
theorem point_zero : point 0 = 0 := ofBits_zero

/-- `Ŵ_s(x) = W_s(x) / W_s(e_s)`. -/
theorem wHat_eq (s : ℕ) (hs : s < 16) (x : K) :
    wHat s x = wSub s x * (wSub s (point (2 ^ s)))⁻¹ := by
  rw [wHat, AdditiveNTT.normalizedW, eval_mul, eval_C, wSub, wSub, basis_ofNat hs, one_div,
    mul_comm]

/-- `Ŵ_s` vanishes at `e_k` for `k < s`. -/
theorem wHat_two_pow_of_lt {s k : ℕ} (hs : s < 16) (hk : k < s) : wHat s (point (2 ^ k)) = 0 :=
  AdditiveNTT.normalizedWᵢ_vanishing (ZMod 2) basis _ _
    (AdditiveNTT.β_lt_mem_U (ZMod 2) basis (Fin.ofNat 16 s)
      ⟨k, by simp [Nat.mod_eq_of_lt hs, hk]⟩)

/-- `Ŵ_s(e_s) = 1`. -/
theorem wHat_two_pow_self {s : ℕ} (hs : s < 16) : wHat s (point (2 ^ s)) = 1 := by
  rw [wHat, ← basis_ofNat hs]
  exact AdditiveNTT.normalizedWᵢ_eval_βᵢ_eq_1 (ZMod 2) basis

/-! ## Points as sums of basis elements -/

/-- A point whose index has disjoint high and low bits is the sum of the two points. -/
theorem point_mul_add {q n r : ℕ} (hr : r < 2 ^ n) :
    point (q * 2 ^ n + r) = point (q * 2 ^ n) + point r := by
  rw [point_add]
  congr 1
  refine Nat.eq_of_testBit_eq fun j ↦ ?_
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hr, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases hj : j < n
  · simp [hj, Nat.not_le.mpr hj]
  · have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hj, Nat.le_of_not_lt hj, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hr hle)]

/-- An additive map at `point (a · 2^o)` is its sum at the `e_(o+k)` over the bits `k` of `a`. -/
theorem map_point_mul {M : Type*} [AddCommMonoid M] (f : K →+ M) (o : ℕ) :
    ∀ n a, a < 2 ^ n → f (point (a * 2 ^ o)) =
      (((List.range n).filter a.testBit).map fun k ↦ f (point (2 ^ (o + k)))).sum
  | 0, a, ha => by simp [show a = 0 by omega, point_zero]
  | n + 1, a, ha => by
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ^ n ∧ a = q * 2 ^ n + r :=
      ⟨a / 2 ^ n, a % 2 ^ n, Nat.mod_lt _ (by positivity), (Nat.div_add_mod' a (2 ^ n)).symm⟩
    have hq : q < 2 := by
      by_contra h
      have : 2 * 2 ^ n ≤ q * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ] at ha
      omega
    have hro : r * 2 ^ o < 2 ^ (o + n) := by
      rw [pow_add, mul_comm (2 ^ o)]
      exact Nat.mul_lt_mul_of_pos_right hr (by positivity)
    have hbit : ∀ k, (q * 2 ^ n + r).testBit k = if k < n then r.testBit k else q.testBit (k - n) :=
      fun k ↦ by rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hr]
    have hfilt : (List.range n).filter (q * 2 ^ n + r).testBit = (List.range n).filter r.testBit :=
      List.filter_congr fun k hk ↦ by simp [hbit, List.mem_range.mp hk]
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, hfilt,
      ← map_point_mul f o n r hr,
      show (q * 2 ^ n + r) * 2 ^ o = q * 2 ^ (o + n) + r * 2 ^ o by ring, point_mul_add hro,
      map_add, add_comm]
    congr 1
    interval_cases q
    · simp [point_zero, Nat.testBit_eq_false_of_lt hr]
    · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hr]

/-- `Ŵ_s` vanishes on the span of `e_0 … e_(s-1)`. -/
theorem wHat_of_lt {s y : ℕ} (hs : s < 16) (hy : y < 2 ^ s) : wHat s (point y) = 0 := by
  have h := map_point_mul (wHatHom s) 0 s y hy
  simp only [pow_zero, mul_one, zero_add, wHatHom_apply] at h
  rw [h]
  refine List.sum_eq_zero fun x hx ↦ ?_
  simp only [List.mem_map, List.mem_filter, List.mem_range] at hx
  obtain ⟨k, ⟨hk, _⟩, rfl⟩ := hx
  exact wHat_two_pow_of_lt hs hk

/-! ## The twiddles -/

/-- `W_0 = X`. -/
theorem wSub_zero (x : K) : wSub 0 x = x := by
  rw [wSub, show Fin.ofNat 16 0 = 0 from rfl, AdditiveNTT.W₀_eq_X, eval_X]

/-- `W_(i+1)(x) = W_i(x) (W_i(x) + W_i(e_i))`. -/
theorem wSub_succ {i : ℕ} (hi : i < 15) (x : K) :
    wSub (i + 1) x = wSub i x * (wSub i x + wSub i (point (2 ^ i))) := by
  have h := AdditiveNTT.W_linear_comp_decomposition (ZMod 2) basis (Fin.ofNat 16 i)
    (by simp [Nat.mod_eq_of_lt (by omega : i < 16)]; omega) X
  have hi1 : Fin.ofNat 16 i + 1 = Fin.ofNat 16 (i + 1) :=
    Fin.ext (by simp [Fin.val_add])
  rw [comp_X, comp_X, ZMod.card, hi1] at h
  rw [← basis_ofNat (by omega)]
  simp only [wSub, h, eval_add, eval_pow, eval_mul, eval_C, CharTwo.sub_eq_add]
  ring

/-- `subspaceRow i` is `W_i` at `e_i … e_14`. -/
theorem subspaceRow_eq : ∀ {i : ℕ}, i ≤ 14 →
    subspaceRow i = (List.range (15 - i)).map fun k ↦ wSub i (point (2 ^ (i + k)))
  | 0, _ => by simp [subspaceRow, logM, wSub_zero, point]
  | i + 1, hi => by
    rw [subspaceRow, subspaceRow_eq (by omega), show 15 - i = 14 - i + 1 by omega,
      List.range_succ_eq_map, show 15 - (i + 1) = 14 - i by omega]
    simp only [List.map_cons, List.map_map, List.headD_cons, List.drop_succ_cons, List.drop_zero,
      add_zero]
    refine List.map_congr_left fun k _ ↦ ?_
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [wSub_succ (by omega), show i + (k + 1) = i + 1 + k by ring]

/-- `subspaceEvaluations i` is `Ŵ_i` at `e_i … e_14`. -/
theorem subspaceEvaluations_eq {i : ℕ} (hi : i ≤ 14) :
    subspaceEvaluations i = (List.range (15 - i)).map fun k ↦ wHat i (point (2 ^ (i + k))) := by
  rw [subspaceEvaluations, subspaceRow_eq hi, show 15 - i = 14 - i + 1 by omega,
    List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.headD_cons, add_zero]
  rw [wHat_eq i (by omega)]
  refine congrArg _ (List.map_congr_left fun k _ ↦ ?_)
  simp only [Function.comp]
  rw [wHat_eq i (by omega)]

/-- A sum accumulated by a left fold. -/
theorem foldl_add_eq_sum {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ (l : List ℕ) (c : M), l.foldl (fun t k ↦ t + g k) c = c + (l.map g).sum
  | [], c => by simp
  | k :: l, c => by
    rw [List.foldl_cons, foldl_add_eq_sum g l, List.map_cons, List.sum_cons, add_assoc]

/-- **`subspaceAbove j y` is `Ŵ_j` at the point whose bits above `j` are `y`'s**: the twiddle of
block `y` of layer `14 - j` is `Ŵ_j` at the block's first point. -/
theorem subspaceAbove_eq {s b : ℕ} (hs : s ≤ 14) (hb : b < 2 ^ (14 - s)) :
    subspaceAbove s b = wHat s (point (b * 2 ^ (s + 1))) := by
  rw [subspaceAbove, show logK - s = 14 - s from rfl, foldl_add_eq_sum, zero_add, ← wHatHom_apply,
    map_point_mul (wHatHom s) (s + 1) (14 - s) b hb]
  refine congrArg _ (List.map_congr_left fun k hk ↦ ?_)
  simp only [List.mem_filter, List.mem_range] at hk
  rw [subspaceEvaluations_eq hs, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (by omega), Option.map_some, Option.getD_some,
    wHatHom_apply, show s + (1 + k) = s + 1 + k by ring]

/-- `Ŵ_s` at a point of index below `2^n`: the sum of its values at the basis elements `e_c`
over the bits `c` of the index. -/
theorem wHat_point_eq_sum (s : ℕ) {n b : ℕ} (hb : b < 2 ^ n) :
    wHat s (point b) = (((List.range n).filter b.testBit).map fun c ↦ wHat s (point (2 ^ c))).sum := by
  have h := map_point_mul (wHatHom s) 0 n b hb
  simpa only [pow_zero, mul_one, zero_add, wHatHom_apply] using h

/-- `Ŵ_j` at the low `j + 1` bits of `i`: bit `j` of `i`. -/
theorem wHat_point_mod {j : ℕ} (hj : j < 16) (i : ℕ) :
    wHat j (point (i % 2 ^ (j + 1))) = if i.testBit j then 1 else 0 := by
  have hlow : i % 2 ^ (j + 1) = i / 2 ^ j % 2 * 2 ^ j + i % 2 ^ j := by
    rw [pow_succ, Nat.mod_mul, add_comm, mul_comm (2 ^ j)]
  rw [hlow, point_mul_add (Nat.mod_lt _ (by positivity)), wHat_add,
    wHat_of_lt hj (Nat.mod_lt _ (by positivity)), add_zero, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ j) with h | h
  · rw [h, zero_mul, point_zero, wHat_zero]
    simp
  · rw [h, one_mul, wHat_two_pow_self hj]
    simp

/-- **`subspaceAt j i` is `Ŵ_j` at point `i`.** -/
theorem subspaceAt_eq {j i : ℕ} (hj : j < 14) (hi : i < 2 ^ 15) :
    subspaceAt j i = wHat j (point i) := by
  have hy : i >>> (j + 1) < 2 ^ (14 - j) := by
    rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul (lt_of_lt_of_eq hi ?_)
    rw [← pow_add]
    congr 1
    omega
  have hsplit : i = i >>> (j + 1) * 2 ^ (j + 1) + i % 2 ^ (j + 1) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_add_mod' i _).symm
  conv_rhs => rw [hsplit]
  rw [point_mul_add (Nat.mod_lt _ (by positivity)), wHat_add, wHat_point_mod (by omega),
    subspaceAt, subspaceAbove_eq (by omega) hy, add_comm]

/-- A product accumulated by a left fold. -/
theorem foldl_mul_eq_prod {M : Type*} [CommMonoid M] (g : ℕ → M) :
    ∀ (l : List ℕ) (c : M), l.foldl (fun t k ↦ t * g k) c = c * (l.map g).prod
  | [], c => by simp
  | k :: l, c => by
    rw [List.foldl_cons, foldl_mul_eq_prod g l, List.map_cons, List.prod_cons, mul_assoc]

/-- The guest's dual codeword has `2^15` entries. -/
theorem length_dualCodeword (z : E) : (dualCodeword z).length = 2 ^ 15 := by
  simp [dualCodeword, logM]

/-- A product over `List.range` is one over `Finset.range`. -/
theorem prod_map_range {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_map_range f n,
      Finset.prod_range_succ]
    simp

/-- **The guest's dual codeword is the dual codeword of `z`** (`membership.rs:41-56`). -/
theorem dualCodeword_eq_dualCodewordAt (z : E) (b : Fin (2 ^ 15)) :
    (dualCodeword z).getD b 0 = dualCodewordAt z b := by
  have hfac : ∀ j : Fin 14,
      1 + z ^ 2 ^ (j : ℕ) * ι ((normalizedSubspacePolynomial j).eval (point b)) =
        (fun j : ℕ ↦ 1 + z ^ 2 ^ j * ι (wHat j (point b))) j := fun j ↦ by
    rw [normW_eval]
  rw [dualCodewordAt, Finset.prod_congr rfl fun j _ ↦ hfac j,
    Fin.prod_univ_eq_prod_range (fun j : ℕ ↦ 1 + z ^ 2 ^ j * ι (wHat j (point b))) 14,
    ← prod_map_range, dualCodeword, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show (b : ℕ) < 2 ^ logM from b.isLt), Option.map_some, Option.getD_some,
    foldl_mul_eq_prod, one_mul, show logK = 14 from rfl]
  refine congrArg _ (List.map_congr_left fun j hj ↦ ?_)
  have hj : j < 14 := List.mem_range.mp hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some, subspaceAt_eq hj b.isLt]
  rfl

end

end LeanDa
