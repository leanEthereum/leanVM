/-
  LeanVM.Protocol.Whir.Sound.Novel

  The verifier's novel-basis evaluation as the evaluation of a polynomial: `novelBasis` of the
  subspace polynomials is the novel basis at a point, `novelEval` the polynomial of the
  coefficients there, and a lane of `2^μ + ℓ` coefficients is its low part plus `Ŵ_μ` times its
  high part.
-/

module

public import LeanVM.Protocol.Whir.Sound.Escape
public import LeanVM.Protocol.Whir.SubspaceAt

/-!
# The novel basis in the verifier

`novel_basis` and `novel_eval` (`crates/verifier/src/whir.rs:133-155`,
`LeanVM.Protocol.Verifier.novelBasis`, `novelEval`) evaluate a polynomial given by its
novel-basis coefficients at a domain point from the values `Ŵ_i(x)` (`subspaceAt`):

* `novel_add_two_pow`: `X_(c + 2^k) = X_c Ŵ_k` for `c < 2^k`;
* `novelBasis_subspaceAt`: `novelBasis (subspaceAt μ x) count = [X_0(x), …, X_(count−1)(x)]` for
  `count ≤ 2^(μ+1)`;
* `polyOf cs = Σ_c cs_c X_c` and `novelEval_eq`: `novelEval cs (subspaceAt μ x) = (polyOf cs)(x)`;
* `polyOf_split`: a list of `2^μ + ℓ` coefficients, `ℓ ≤ 2^μ`, is
  `P_low + Ŵ_μ · polyOf(high)`, `P_low` the message polynomial of the first `2^μ`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset Polynomial

@[expose] public section

/-! ## Doubling the basis -/

theorem testBit_add_two_pow {c k i : ℕ} (hc : c < 2 ^ k) :
    (c + 2 ^ k).testBit i = (c.testBit i || i = k) := by
  rw [Nat.add_comm, two_pow_add_eq_xor hc, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : i = k
  · subst hi
    rw [Nat.testBit_lt_two_pow hc]
    simp
  · simp [hi, Ne.symm hi]

/-- `X_(c + 2^k) = X_c Ŵ_k` for `c < 2^k`, `k < 64`. -/
theorem novelAt_add_two_pow {c k : ℕ} (hc : c < 2 ^ k) (hk : k < 64) (a : K) :
    novelAt (c + 2 ^ k) a = novelAt c a * normVanishingAt k a := by
  have hmem : k ∈ Finset.range 64 := Finset.mem_range.mpr hk
  rw [novelAt, novelAt, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
    testBit_add_two_pow hc, Nat.testBit_lt_two_pow hc]
  simp only [Bool.false_or, decide_true, ite_true, Bool.false_eq_true, ite_false, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [testBit_add_two_pow hc]
  simp [Finset.ne_of_mem_erase hi]

theorem novel_add_two_pow {c k : ℕ} (hc : c < 2 ^ k) (hk : k < 64) :
    novel (c + 2 ^ k) = novel c * normVanishing k := by
  have hmem : k ∈ Finset.range 64 := Finset.mem_range.mpr hk
  rw [novel, novel, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
    testBit_add_two_pow hc, Nat.testBit_lt_two_pow hc]
  simp only [Bool.false_or, decide_true, ite_true, Bool.false_eq_true, ite_false, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [testBit_add_two_pow hc]
  simp [Finset.ne_of_mem_erase hi]

/-- The invariant of `novel_basis`'s loop after `k` values. -/
private theorem novelBasis_loop (x : K) (count : ℕ) : ∀ (n k : ℕ) (L : List K),
    k + n ≤ 64 →
    L = (List.range L.length).map (fun c ↦ novelAt c x) → (L.length = 2 ^ k ∨ count ≤ L.length) →
    ∃ L', ((List.range' k n).map fun i ↦ normVanishingAt i x).foldl (fun basis value ↦
        if count ≤ basis.length then basis else basis ++ basis.map (· * value)) L = L' ∧
      L' = (List.range L'.length).map (fun c ↦ novelAt c x) ∧
      (L'.length = 2 ^ (k + n) ∨ count ≤ L'.length)
  | 0, k, L, _, hL, hlen => ⟨L, rfl, hL, by simpa using hlen⟩
  | n + 1, k, L, hkn, hL, hlen => by
    rw [List.range'_succ, List.map_cons, List.foldl_cons]
    by_cases hc : count ≤ L.length
    · simp only [hc, ↓reduceIte]
      exact novelBasis_loop x count n (k + 1) L (by omega) hL (Or.inr hc) |>.imp
        fun L' h ↦ ⟨h.1, h.2.1, by rw [show k + (n + 1) = k + 1 + n by omega]; exact h.2.2⟩
    · simp only [hc, ↓reduceIte]
      have hk : L.length = 2 ^ k := hlen.resolve_right hc
      refine novelBasis_loop x count n (k + 1) _ (by omega) ?_ (Or.inl ?_) |>.imp
        fun L' h ↦ ⟨h.1, h.2.1, by rw [show k + (n + 1) = k + 1 + n by omega]; exact h.2.2⟩
      · rw [List.length_append, List.length_map, hk, List.range_add, List.map_append, List.map_map]
        congr 1
        · rw [← hk]; exact hL
        · conv_lhs => rw [hL, hk, List.map_map]
          refine List.map_congr_left fun i hi ↦ ?_
          simp only [Function.comp_apply]
          rw [show 2 ^ k + i = i + 2 ^ k by omega,
            novelAt_add_two_pow (List.mem_range.mp hi) (by omega)]
      · rw [List.length_append, List.length_map, hk, ← two_mul, ← pow_succ']

/-- **`novel_basis` of the subspace polynomials** is the novel basis at the point. -/
theorem novelBasis_subspaceAt {mu count : ℕ} (hmu : mu < 64) (hc : count ≤ 2 ^ (mu + 1))
    (x : K) : novelBasis (subspaceAt mu x) count = (List.range count).map fun c ↦ novelAt c x := by
  have h1 : ([1] : List K) = (List.range [1].length).map fun c ↦ novelAt c x := by
    simp [novelAt]
  obtain ⟨L', hfold, hL', hlen⟩ := novelBasis_loop x count (mu + 1) 0 [1] (by omega) h1
    (Or.inl (by simp))
  rw [novelBasis, subspaceAt_eq, List.range_eq_range', hfold]
  have hcount : count ≤ L'.length := by
    rcases hlen with h | h
    · rw [h]; simpa using hc
    · exact h
  rw [hL', ← List.map_take, List.take_range, min_eq_left hcount]

/-! ## Polynomials of coefficient lists -/

/-- The polynomial `Σ_c cs_c X_c` of a coefficient list. -/
noncomputable def polyOf (cs : List E) : E[X] :=
  ∑ c ∈ Finset.range cs.length, cs.getD c 0 • novelE c

theorem eval_polyOf (cs : List E) (x : K) :
    (polyOf cs).eval (ofK x) = ∑ c ∈ Finset.range cs.length, cs.getD c 0 * ofK (novelAt c x) := by
  rw [polyOf, eval_finsetSum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [eval_smul, smul_eq_mul, novelE, eval_map, show ofK x = algebraMap K E x from rfl,
    eval₂_hom, eval_novel]
  rfl

/-- **`novel_eval`** of the subspace polynomials is the polynomial's value. -/
theorem novelEval_eq {mu : ℕ} (hmu : mu < 64) (cs : List E) (hc : cs.length ≤ 2 ^ (mu + 1))
    (x : K) : novelEval cs (subspaceAt mu x) = (polyOf cs).eval (ofK x) := by
  rw [novelEval, novelBasis_subspaceAt hmu hc, eval_polyOf, sumE, foldl_add_eq, zero_add]
  have hz : List.zipWith (fun p b ↦ p * ofK b) cs
      ((List.range cs.length).map fun c ↦ novelAt c x) =
      (List.range cs.length).map fun c ↦ cs.getD c 0 * ofK (novelAt c x) := by
    refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h₂)]
  rw [hz, Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.sum_coe]

theorem novelE_add_two_pow {c k : ℕ} (hc : c < 2 ^ k) (hk : k < 64) :
    novelE (c + 2 ^ k) = novelE c * hatE k := by
  rw [novelE, novel_add_two_pow hc hk, Polynomial.map_mul]
  rfl

/-- The message polynomial as a sum over the integers below `2^μ`. -/
theorem msgPoly_eq_sum_range (mu : ℕ) (cs : List E) :
    msgPoly mu (fun u ↦ cs.getD (bitsToNat u) 0) =
      ∑ c ∈ Finset.range (2 ^ mu), cs.getD c 0 • novelE c := by
  rw [msgPoly, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_range]
  exact Fintype.sum_equiv (bitsEquiv mu) _ _ fun u ↦ by rw [bitsEquiv_val]

/-- **The low and high parts of a lane** of `2^μ + ℓ` coefficients, `ℓ ≤ 2^μ`. -/
theorem polyOf_split {mu : ℕ} (hmu : mu < 64) (cs : List E) {ℓ : ℕ}
    (hlen : cs.length = 2 ^ mu + ℓ) (hℓ : ℓ ≤ 2 ^ mu) :
    polyOf cs = msgPoly mu (fun u ↦ cs.getD (bitsToNat u) 0) + hatE mu * polyOf (cs.drop (2 ^ mu)) := by
  rw [polyOf, hlen, Finset.sum_range_add, msgPoly_eq_sum_range, polyOf, List.length_drop, hlen,
    Nat.add_sub_cancel_left, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j < 2 ^ mu := lt_of_lt_of_le (Finset.mem_range.mp hj) hℓ
  rw [show 2 ^ mu + j = j + 2 ^ mu by omega, novelE_add_two_pow hj' hmu, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_drop, Polynomial.smul_eq_C_mul,
    Polynomial.smul_eq_C_mul, show j + 2 ^ mu = 2 ^ mu + j by omega]
  ring

/-- The degree of `polyOf`: below its length. -/
theorem natDegree_polyOf_le (cs : List E) (hcs : cs.length ≤ 2 ^ 64) :
    (polyOf cs).natDegree + 1 ≤ max cs.length 1 := by
  rcases Nat.eq_zero_or_pos cs.length with h0 | hpos
  · simp [polyOf, h0]
  have : (polyOf cs).natDegree ≤ cs.length - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun c hc ↦ ?_
    refine (natDegree_smul_le _ _).trans ?_
    rw [novelE, natDegree_map, natDegree_novel (by have := Finset.mem_range.mp hc; omega)]
    have := Finset.mem_range.mp hc
    omega
  omega

end
end LeanVM.Protocol.Whir.Sound
