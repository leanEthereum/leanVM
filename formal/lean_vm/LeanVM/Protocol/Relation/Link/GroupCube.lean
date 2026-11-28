/-
  LeanVM.Protocol.Relation.Link.GroupCube

  The link's row-side pieces at the Boolean points of the cube: sums over the cube as sums over
  integers, the pointer columns' `eq(q, ·)`, a table's corner and its row weight `ω`.
-/

module

public import LeanVM.Protocol.Relation.Link.Cube
public import LeanVM.Protocol.Relation.Link.Fold
public import LeanVM.Protocol.Relation.Link.GroupPoly
import LeanVM.Parameters.Field

/-!
# The cube's Boolean points

* `sumTail_split`, `sumTail_eq_sum`: `cube`'s partial sums as sums over the integers' Boolean points
  (`boolL`, the first coordinate the lowest bit);
* `eqKernel_boolL`: `eq(q, ·)` at a Boolean `q` selects one entry;
* `take_boolL`, `prodE_drop_boolL`: a table's row point and its corner at a Boolean row point;
* `prefixSum_eq`: `prefix_sum(low, high, n) = Σ_{g < n} Π_h e_h(g_h)`, `prod_add_eq_sum`;
* `omegaAt_boolL`: `ω_F` at a Boolean row point `u` is `θ_F·eq(τ, u)·[u < n]`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-! ## Boolean points -/

theorem boolL_succ (n c j : ℕ) (hc : c < 2) :
    boolL (n + 1) (c + 2 * j) = (if c = 1 then 1 else 0) :: boolL n j := by
  simp only [boolL, List.ofFn_succ, boolPt, Fin.val_zero, Fin.val_succ, List.cons.injEq]
  refine ⟨?_, ?_⟩
  · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simp
  · congr 1
    funext i
    simp only [boolPt, Nat.testBit_succ, show (c + 2 * j) / 2 = j by omega]

theorem boolL_zero (j : ℕ) : boolL 0 j = [] := rfl

theorem boolL_even (n j : ℕ) : boolL (n + 1) (2 * j) = 0 :: boolL n j := by
  have := boolL_succ n 0 j (by omega)
  simpa using this

theorem boolL_odd (n j : ℕ) : boolL (n + 1) (2 * j + 1) = 1 :: boolL n j := by
  have := boolL_succ n 1 j (by omega)
  rw [Nat.add_comm 1 (2 * j)] at this
  simpa using this

/-- `Σ_{b ∈ {0,1}^{a+b}} f (p ++ b)` splits at `a`. -/
theorem sumTail_split (f : List E → E) (b : ℕ) : ∀ (a : ℕ) (p : List E),
    sumTail f (a + b) p = ∑ j ∈ range (2 ^ a), sumTail f b (p ++ boolL a j)
  | 0, p => by simp [boolL_zero]
  | a + 1, p => by
    rw [show a + 1 + b = (a + b) + 1 by omega, sumTail, sumTail_split f b a, sumTail_split f b a,
      pow_succ, mul_comm, sum_range_two_mul, ← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [boolL_even, boolL_odd]
    simp

/-- **`cube`'s full sum over the integers.** -/
theorem sumTail_eq_sum (f : List E → E) (a : ℕ) (p : List E) :
    sumTail f a p = ∑ j ∈ range (2 ^ a), f (p ++ boolL a j) := by
  rw [← Nat.add_zero a, sumTail_split f 0 a p]
  rfl

/-- `eq(q, ·)` at a Boolean point selects its entry. -/
theorem eqKernel_boolL {n jq : ℕ} (hq : jq < 2 ^ n) (j : ℕ) :
    (eqKernel (boolL n jq)).getD j 0 = if j = jq then 1 else 0 := by
  rw [eqKernel_getD, length_boolL]
  split_ifs with h1 h2 h2
  · rw [eqAt_boolL h1 hq]; simp [h2]
  · rw [eqAt_boolL h1 hq]; simp [h2]
  · exact absurd (h2 ▸ hq) h1
  · rfl

theorem take_boolL {m h : ℕ} (hh : h ≤ m) (j : ℕ) : (boolL m j).take h = boolL h (j % 2 ^ h) := by
  refine List.ext_getElem (by simp [length_boolL]; omega) fun i hi _ ↦ ?_
  simp only [List.getElem_take, boolL, List.getElem_ofFn, boolPt]
  rw [Nat.testBit_mod_two_pow]
  simp only [List.length_take] at hi
  simp [show i < h by omega]

theorem prodE_eq_prod (l : List E) : prodE l = l.prod := by
  rw [prodE, List.prod_eq_foldl]

theorem drop_boolL (m h j : ℕ) : (boolL m j).drop h = boolL (m - h) (j / 2 ^ h) := by
  refine List.ext_getElem (by simp [length_boolL]) fun i hi _ ↦ ?_
  simp only [List.getElem_drop, boolL, List.getElem_ofFn, boolPt, Nat.testBit_div_two_pow]
  rw [Nat.add_comm i h]

theorem prod_one_add_boolL : ∀ (n k : ℕ), k < 2 ^ n →
    ((boolL n k).map (1 + ·)).prod = if k = 0 then 1 else 0
  | 0, k, hk => by simp [boolL_zero]; omega
  | n + 1, k, hk => by
    have hk2 : k = k % 2 + 2 * (k / 2) := by omega
    rw [hk2, boolL_succ n (k % 2) (k / 2) (Nat.mod_lt _ (by norm_num)), List.map_cons, List.prod_cons,
      prod_one_add_boolL n (k / 2) (by rw [pow_succ] at hk; omega)]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · simp only [h, zero_ne_one, ↓reduceIte, add_zero]
      split_ifs <;> first | omega | simp
    · simp only [h, ↓reduceIte, CharTwo.add_self_eq_zero, zero_mul]
      split_ifs <;> first | rfl | omega

/-- A table's corner at a Boolean row point: `1` on the rows of its height. -/
theorem prodE_drop_boolL {m h j : ℕ} (hh : h ≤ m) (hj : j < 2 ^ m) :
    prodE (((boolL m j).drop h).map (1 + ·)) = if j < 2 ^ h then 1 else 0 := by
  rw [prodE_eq_prod, drop_boolL, prod_one_add_boolL _ _ ?_]
  · simp [Nat.div_eq_zero_iff]
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h), ← pow_add, Nat.sub_add_cancel hh]
    exact hj

/-! ## `prefix_sum` and the row weight -/

/-- `e_h(g_h)`: `high[h]` where bit `h` of `g` is set, `low[h]` where it is not. -/
def selBit (low high : List E) (g h : ℕ) : E := if g.testBit h then high.getD h 0 else low.getD h 0

theorem shift_mod_two_iff (n h : ℕ) : (n >>> h % 2 = 1) ↔ n.testBit h = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  simp

/-- `Π_{h < L} (low_h + high_h) = Σ_{g < 2^L} Π_{h < L} e_h(g_h)`. -/
theorem prod_add_eq_sum (low high : List E) : ∀ L : ℕ,
    ∏ h ∈ range L, (low.getD h 0 + high.getD h 0) = ∑ g ∈ range (2 ^ L), ∏ h ∈ range L, selBit low high g h
  | 0 => by simp
  | L + 1 => by
    rw [prod_range_succ, prod_add_eq_sum low high L, pow_succ, mul_two, sum_range_add, mul_add,
      sum_mul, sum_mul]
    congr 1
    · refine sum_congr rfl fun g hg ↦ ?_
      rw [prod_range_succ, selBit]
      simp only [Nat.testBit_lt_two_pow (mem_range.mp hg), Bool.false_eq_true, ↓reduceIte]
    · refine sum_congr rfl fun g hg ↦ ?_
      rw [prod_range_succ, selBit]
      simp only [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (mem_range.mp hg), Bool.not_false,
        ↓reduceIte]
      congr 1
      refine prod_congr rfl fun h hh ↦ ?_
      simp only [selBit, Nat.testBit_two_pow_add_gt (mem_range.mp hh)]

theorem full_getD (low high : List E) : ∀ (k h : ℕ), h ≤ k →
    ((List.range k).foldl (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)])
      [(1 : E)]).getD h 0 = ∏ h' ∈ range h, (low.getD h' 0 + high.getD h' 0) ∧
    ((List.range k).foldl (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)])
      [(1 : E)]).length = k + 1
  | 0, h, hh => by simp [show h = 0 by omega]
  | k + 1, h, hh => by
    obtain ⟨-, hlen⟩ := full_getD low high k k le_rfl
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨?_, by rw [List.length_append, hlen]; rfl⟩
    rcases Nat.lt_or_ge h (k + 1) with hlt | hge
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact (full_getD low high k h (by omega)).1
    · rw [show h = k + 1 by omega, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self,
        List.getD_cons_zero, (full_getD low high k k le_rfl).1, prod_range_succ]

/-- The top-down walk of `prefix_sum` from `(a, b)` over the low `k` bits. -/
theorem prefix_walk (low high : List E) (n : ℕ) (fl : ℕ → E)
    (K : ℕ) (hfl : ∀ h < K, fl h = ∏ h' ∈ range h, (low.getD h' 0 + high.getD h' 0)) :
    ∀ (k : ℕ), k ≤ K → ∀ (a b : E), (List.range k).foldr (fun h (acc : E × E) ↦
      if n >>> h % 2 = 1 then (acc.1 + acc.2 * low.getD h 0 * fl h, acc.2 * high.getD h 0)
      else (acc.1, acc.2 * low.getD h 0)) (a, b) =
      (a + b * ∑ g ∈ range (n % 2 ^ k), ∏ h ∈ range k, selBit low high g h,
        b * ∏ h ∈ range k, selBit low high n h)
  | 0, _, a, b => by simp [Nat.mod_one]
  | k + 1, hk, a, b => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have hmod : n % 2 ^ (k + 1) = n % 2 ^ k + 2 ^ k * (n / 2 ^ k % 2) := Nat.mod_pow_succ
    by_cases hb : n.testBit k = true
    · simp only [(shift_mod_two_iff n k).mpr hb, ↓reduceIte]
      rw [prefix_walk low high n fl K hfl k (by omega)]
      have hbit : n / 2 ^ k % 2 = 1 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simpa using hb
      rw [hmod, hbit, mul_one, Nat.add_comm, sum_range_add]
      simp only [Prod.mk.injEq]
      constructor
      · have h1 : ∑ x ∈ range (2 ^ k), ∏ h ∈ range (k + 1), selBit low high x h =
            low.getD k 0 * ∑ g ∈ range (2 ^ k), ∏ h ∈ range k, selBit low high g h := by
          rw [mul_sum]
          refine sum_congr rfl fun g hg ↦ ?_
          rw [prod_range_succ, selBit]
          simp only [Nat.testBit_lt_two_pow (mem_range.mp hg), Bool.false_eq_true, ↓reduceIte]
          ring
        have h2 : ∑ x ∈ range (n % 2 ^ k), ∏ h ∈ range (k + 1), selBit low high (2 ^ k + x) h =
            high.getD k 0 * ∑ g ∈ range (n % 2 ^ k), ∏ h ∈ range k, selBit low high g h := by
          rw [mul_sum]
          refine sum_congr rfl fun g hg ↦ ?_
          have hg' : g < 2 ^ k := (mem_range.mp hg).trans (Nat.mod_lt _ (Nat.two_pow_pos k))
          rw [prod_range_succ, selBit]
          simp only [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hg', Bool.not_false, ↓reduceIte]
          rw [show ∏ h ∈ range k, selBit low high (2 ^ k + g) h = ∏ h ∈ range k, selBit low high g h from
            prod_congr rfl fun h hh ↦ by
              simp only [selBit, Nat.testBit_two_pow_add_gt (mem_range.mp hh)]]
          ring
        rw [h1, h2, hfl k (by omega), prod_add_eq_sum]
        ring
      · rw [prod_range_succ, selBit]
        simp only [hb, ↓reduceIte]
        ring
    · have hb' : n.testBit k = false := by simpa using hb
      have hc : ¬ (n >>> k % 2 = 1) := fun h ↦ hb ((shift_mod_two_iff n k).mp h)
      simp only [hc, ↓reduceIte]
      rw [prefix_walk low high n fl K hfl k (by omega)]
      have hbit : n / 2 ^ k % 2 = 0 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at hb'; simpa using hb'
      rw [hmod, hbit, mul_zero, add_zero]
      simp only [Prod.mk.injEq]
      constructor
      · have h3 : ∑ g ∈ range (n % 2 ^ k), ∏ h ∈ range (k + 1), selBit low high g h =
            low.getD k 0 * ∑ g ∈ range (n % 2 ^ k), ∏ h ∈ range k, selBit low high g h := by
          rw [mul_sum]
          refine sum_congr rfl fun g hg ↦ ?_
          have hg' : g < 2 ^ k := (mem_range.mp hg).trans (Nat.mod_lt _ (Nat.two_pow_pos k))
          rw [prod_range_succ, selBit]
          simp only [Nat.testBit_lt_two_pow hg', Bool.false_eq_true, ↓reduceIte]
          ring
        rw [h3]
        ring
      · rw [prod_range_succ, selBit]
        simp only [hb', Bool.false_eq_true, ↓reduceIte]
        ring

/-- **`prefix_sum`**: `Σ_{g < n} Π_h e_h(g_h)`, for `n ≤ 2^len`. -/
theorem prefixSum_eq (low high : List E) {n : ℕ} (hn : n ≤ 2 ^ low.length) :
    prefixSum low high n = ∑ g ∈ range n, ∏ h ∈ range low.length, selBit low high g h := by
  unfold prefixSum
  simp only
  split_ifs with h2
  · rw [show n = 2 ^ low.length by omega, (full_getD low high _ _ le_rfl).1, prod_add_eq_sum]
  · generalize hF : (List.range low.length).foldl
      (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)]) [(1 : E)] = F
    have hw := prefix_walk low high n (fun h ↦ F.getD h 0) low.length
      (fun h hh ↦ hF ▸ (full_getD low high _ _ hh.le).1) low.length le_rfl 0 1
    rw [List.foldl_reverse]
    refine (congrArg Prod.fst hw).trans ?_
    rw [Nat.mod_eq_of_lt (by omega)]
    simp

theorem getD_boolL {h u k : ℕ} (hk : k < h) :
    (boolL h u).getD k 0 = if u.testBit k then 1 else 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [length_boolL]; exact hk)]
  simp [boolL, boolPt]

/-- `eq(τ, u)` as a product over the coordinates. -/
theorem eqAt_eq_prod (τ : List E) (u : ℕ) :
    eqAt τ u = ∏ k ∈ range τ.length, if u.testBit k then τ.getD k 0 else 1 + τ.getD k 0 := by
  have h := eqAt_ofFn (fun i : Fin τ.length ↦ τ.getD i 0) u
  rw [show List.ofFn (fun i : Fin τ.length ↦ τ.getD i 0) = τ from
    List.ext_getElem (by simp) fun i h1 h2 ↦ by simp] at h
  rw [h, ← Fin.prod_univ_eq_prod_range (fun k ↦ if u.testBit k then τ.getD k 0 else 1 + τ.getD k 0)]
  refine prod_congr rfl fun k _ ↦ ?_
  rw [CharTwo.sub_eq_add]

theorem eq_of_testBit_lt {g u h : ℕ} (hg : g < 2 ^ h) (hu : u < 2 ^ h)
    (hb : ∀ k < h, g.testBit k = u.testBit k) : g = u := by
  refine Nat.eq_of_testBit_eq fun k ↦ ?_
  rcases Nat.lt_or_ge k h with hk | hk
  · exact hb k hk
  · rw [Nat.testBit_lt_two_pow (hg.trans_le (Nat.pow_le_pow_right (by norm_num) hk)),
      Nat.testBit_lt_two_pow (hu.trans_le (Nat.pow_le_pow_right (by norm_num) hk))]

/-- **The row weight at a Boolean row point** `u`: `θ_F·eq(τ, u)·[u < n]`. -/
theorem omegaAt_boolL (theta : E) {h u n : ℕ} (τ : List E) (hτ : τ.length = h) (hu : u < 2 ^ h)
    (hn : n ≤ 2 ^ h) :
    omegaAt theta τ (boolL h u) n = theta * if u < n then eqAt τ u else 0 := by
  unfold omegaAt
  have hlen : (List.zipWith (fun t x ↦ (1 + t) * (1 + x)) τ (boolL h u)).length = h := by
    simp [length_boolL, hτ]
  rw [prefixSum_eq _ _ (by rw [hlen]; exact hn), hlen]
  congr 1
  have hsel : ∀ g < 2 ^ h, ∏ k ∈ range h, selBit (List.zipWith (fun t x ↦ (1 + t) * (1 + x)) τ (boolL h u))
      (List.zipWith (fun t x ↦ t * x) τ (boolL h u)) g k = if g = u then eqAt τ u else 0 := by
    intro g hg
    have hentry : ∀ k < h, selBit (List.zipWith (fun t x ↦ (1 + t) * (1 + x)) τ (boolL h u))
        (List.zipWith (fun t x ↦ t * x) τ (boolL h u)) g k =
        if g.testBit k then τ.getD k 0 * (if u.testBit k then 1 else 0)
        else (1 + τ.getD k 0) * (1 + if u.testBit k then 1 else 0) := by
      intro k hk
      have hk1 : k < τ.length := by omega
      have hk2 : k < (boolL h u).length := by rw [length_boolL]; exact hk
      unfold selBit
      rw [List.getD_eq_getElem _ _ (by simp [hk1, hk2]), List.getD_eq_getElem _ _ (by simp [hk1, hk2]),
        List.getElem_zipWith, List.getElem_zipWith, ← List.getD_eq_getElem _ 0 hk1,
        ← List.getD_eq_getElem _ 0 hk2, getD_boolL hk]
    split_ifs with hgu
    · subst hgu
      rw [eqAt_eq_prod, hτ]
      refine prod_congr rfl fun k hk ↦ ?_
      rw [hentry k (mem_range.mp hk)]
      split_ifs <;> simp
    · have : ∃ k < h, g.testBit k ≠ u.testBit k := by
        by_contra hc
        push Not at hc
        exact hgu (eq_of_testBit_lt hg hu hc)
      obtain ⟨k, hk, hne⟩ := this
      refine prod_eq_zero (mem_range.mpr hk) ?_
      rw [hentry k hk]
      cases hgk : g.testBit k <;> cases huk : u.testBit k <;> simp_all [CharTwo.add_self_eq_zero]
  rw [sum_congr rfl fun g hg ↦ hsel g ((mem_range.mp hg).trans_le hn), sum_ite_eq']
  simp [mem_range]

end

end LeanVM.Protocol.Relation
