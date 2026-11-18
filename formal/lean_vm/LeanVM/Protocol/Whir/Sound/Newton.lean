/-
  LeanVM.Protocol.Whir.Sound.Newton

  Newton interpolation, and the location of one error from its top two coefficients.
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# Newton interpolation with one error

`nCoeffs pts`: the Newton coefficients of the points `pts`, each added as
`a = (y − P(x)) / ∏(x − xᵢ)` (`O(k²)` for `k` points). The polynomial `nP` of the nodes and the
coefficients interpolates the points (`nCoeffs_spec`), and its top two coefficients are the last
coefficient and the one before less the last times the sum of the nodes before the last
(`coeff_nP_top`, `coeff_nP_sub_two`).

**One error** (`locate`): if a polynomial `T` of degree at most `d` disagrees with at most one of
`d + 3` points of distinct nodes, the interpolant is `T` when its top coefficient is zero, and
otherwise the error's node is `x_{d+2} + a_{d+1}/a_{d+2}`.
-/

namespace LeanVM.Protocol.Whir.Sound.Newton

open Polynomial Finset

@[expose] public section

variable {F : Type*} [Field F]

/-- The Newton form: `Σ_k a_k ∏_{i<k} (X − x_i)`. -/
noncomputable def nP (xs as : List F) : F[X] :=
  ∑ k ∈ range as.length, C (as.getD k 0) * ((xs.take k).map fun x ↦ X - C x).prod

/-- The Newton form evaluated, nested. -/
def nEval : List F → List F → F → F
  | x :: xs, a :: as, z => a + (z - x) * nEval xs as z
  | [], a :: _, _ => a
  | _, [], _ => 0

/-- `∏ (z − x_i)`. -/
def nodal (xs : List F) (z : F) : F := (xs.map fun x ↦ z - x).prod

/-- One point added. -/
def nStep (st : List F × List F) (p : F × F) : List F × List F :=
  (st.1 ++ [p.1], st.2 ++ [(p.2 - nEval st.1 st.2 p.1) * (nodal st.1 p.1)⁻¹])

/-- **The Newton coefficients** of the points, with their nodes. -/
def nForm (pts : List (F × F)) : List F × List F := pts.foldl nStep ([], [])

theorem nEval_eq : ∀ (xs as : List F) (z : F), xs.length + 1 ≥ as.length →
    (nP xs as).eval z = nEval xs as z
  | x :: xs, a :: as, z, h => by
    rw [nEval, ← nEval_eq xs as z (by simp at h; omega), nP, nP, List.length_cons,
      sum_range_succ', eval_add, eval_finsetSum, eval_finsetSum, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.prod_cons,
      List.getD_cons_zero, List.take_zero, List.map_nil, List.prod_nil, mul_one, eval_mul, eval_C,
      eval_sub, eval_X]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun k _ ↦ by ring
  | [], [a], z, _ => by simp [nP, nEval]
  | [], _ :: _ :: _, z, h => by simp at h
  | [], [], z, _ => by simp [nP, nEval]
  | _ :: _, [], z, _ => by simp [nP, nEval]

theorem nP_append {xs as : List F} (h : xs.length = as.length) (x a : F) :
    nP (xs ++ [x]) (as ++ [a]) = nP xs as + C a * (xs.map fun x ↦ X - C x).prod := by
  rw [nP, List.length_append, List.length_singleton, sum_range_succ, nP]
  congr 1
  · refine sum_congr rfl fun k hk ↦ ?_
    have hk' : k < as.length := mem_range.mp hk
    rw [List.take_append_of_le_length (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk']
  · rw [← h, List.take_append_of_le_length le_rfl, List.take_length, h]
    simp [List.getD_eq_getElem?_getD]

theorem natDegree_prod_take (xs : List F) (k : ℕ) :
    (((xs.take k).map fun x ↦ X - C x).prod).natDegree ≤ k := by
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  refine (List.sum_le_length_nsmul _ 1 fun n hn ↦ ?_).trans ?_
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hn
    simp
  · simp only [List.length_map, List.length_take, smul_eq_mul, mul_one]
    omega

theorem natDegree_nP (xs as : List F) : (nP xs as).natDegree ≤ as.length - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
  have hk' := mem_range.mp hk
  exact (natDegree_C_mul_le _ _).trans ((natDegree_prod_take xs k).trans (by omega))

/-- The state after the points: as many nodes as coefficients, the nodes the points'. -/
theorem nForm_fst (pts : List (F × F)) : (nForm pts).1 = pts.map (·.1) ∧
    (nForm pts).2.length = pts.length := by
  unfold nForm
  induction pts using List.reverseRecOn with
  | nil => simp
  | append_singleton pts p ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [nStep, List.map_append, List.map_cons, List.map_nil, List.length_append,
      List.length_singleton, ih.1, ih.2, and_self]

/-- **The Newton form interpolates the points**, when their nodes are distinct. -/
theorem nForm_eval (pts : List (F × F)) (hd : (pts.map (·.1)).Nodup) :
    ∀ p ∈ pts, (nP (nForm pts).1 (nForm pts).2).eval p.1 = p.2 := by
  induction pts using List.reverseRecOn with
  | nil => simp
  | append_singleton pts q ih =>
    have hd' : (pts.map (·.1)).Nodup := by
      rw [List.map_append] at hd; exact hd.sublist (List.sublist_append_left _ _)
    have hq : q.1 ∉ pts.map (·.1) := by
      rw [List.map_append, List.nodup_append] at hd
      intro hm
      exact hd.2.2 _ hm _ (List.mem_singleton_self _) rfl
    have hs := nForm_fst pts
    have hlen : (nForm pts).1.length = (nForm pts).2.length := by
      rw [hs.1, hs.2, List.length_map]
    unfold nForm at ih hs hlen ⊢
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [nStep]
    rw [nP_append hlen]
    have hnod : nodal (List.foldl nStep ([], []) pts).1 q.1 ≠ 0 := by
      rw [nodal]
      intro h0
      obtain ⟨z, hz, h0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
      rw [sub_eq_zero] at h0
      subst h0
      exact hq (hs.1 ▸ hz)
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rw [eval_add, ih hd' p hp, eval_mul, eval_list_prod]
      have : (((List.foldl nStep ([], []) pts).1.map fun x ↦ X - C x).map (eval p.1)).prod = 0 := by
        rw [List.prod_eq_zero_iff]
        refine List.mem_map.mpr ⟨X - C p.1, List.mem_map.mpr ⟨p.1, ?_, rfl⟩, by simp⟩
        rw [hs.1]
        exact List.mem_map_of_mem hp
      rw [this, mul_zero, add_zero]
    · rw [List.mem_singleton] at hp
      subst hp
      rw [eval_add, nEval_eq _ _ _ (by omega), eval_mul, eval_C, eval_list_prod, List.map_map]
      have hn : ((List.foldl nStep ([], []) pts).1.map (eval p.1 ∘ fun x ↦ X - C x)).prod =
          nodal (List.foldl nStep ([], []) pts).1 p.1 := by
        simp [nodal, Function.comp_def]
      rw [hn, mul_assoc, inv_mul_cancel₀ hnod, mul_one]
      ring

/-! ## The top two coefficients -/

theorem coeff_prod_take_of_lt (xs : List F) {k j : ℕ} (h : k < j) :
    (((xs.take k).map fun x ↦ X - C x).prod).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_prod_take xs k).trans_lt h)

theorem prod_eq_multiset (l : List F) :
    (l.map fun x ↦ X - C x).prod = ((l : Multiset F).map fun x ↦ X - C x).prod := by
  simp

theorem coeff_prod_top (l : List F) : ((l.map fun x ↦ X - C x).prod).coeff l.length = 1 := by
  have hm : ((l : Multiset F).map fun x ↦ X - C x).prod.Monic := monic_multiset_prod_of_monic _ _
    fun _ _ ↦ monic_X_sub_C _
  have hd : ((l : Multiset F).map fun x ↦ X - C x).prod.natDegree = l.length := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card]; simp
  rw [prod_eq_multiset, ← hd]
  exact hm

theorem coeff_prod_next (l : List F) (hl : 0 < l.length) :
    ((l.map fun x ↦ X - C x).prod).coeff (l.length - 1) = -l.sum := by
  have hd : ((l : Multiset F).map fun x ↦ X - C x).prod.natDegree = l.length := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card]; simp
  have := multiset_prod_X_sub_C_nextCoeff (l : Multiset F)
  rw [nextCoeff_of_natDegree_pos (by omega), hd] at this
  rw [prod_eq_multiset, this]
  simp

/-- The top coefficient of the Newton form of `n + 1` coefficients is the last. -/
theorem coeff_nP_top (xs as : List F) (n : ℕ) (hn : as.length = n + 1) (hx : n ≤ xs.length) :
    (nP xs as).coeff n = as.getD n 0 := by
  rw [nP, finsetSum_coeff, hn, sum_range_succ, Finset.sum_eq_zero fun k hk ↦ by
    rw [coeff_C_mul, coeff_prod_take_of_lt xs (mem_range.mp hk), mul_zero], zero_add,
    coeff_C_mul]
  have := coeff_prod_top (xs.take n)
  rw [List.length_take, Nat.min_eq_left hx] at this
  rw [this, mul_one]

/-- The coefficient below the top: the one before the last, less the last times the sum of the
nodes before the last. -/
theorem coeff_nP_sub (xs as : List F) (n : ℕ) (hn : as.length = n + 2) (hx : n + 1 ≤ xs.length) :
    (nP xs as).coeff n = as.getD n 0 - as.getD (n + 1) 0 * (xs.take (n + 1)).sum := by
  rw [nP, finsetSum_coeff, hn, sum_range_succ, sum_range_succ, Finset.sum_eq_zero fun k hk ↦ by
    rw [coeff_C_mul, coeff_prod_take_of_lt xs (mem_range.mp hk), mul_zero], zero_add,
    coeff_C_mul, coeff_C_mul]
  have h1 := coeff_prod_top (xs.take n)
  rw [List.length_take, Nat.min_eq_left (by omega)] at h1
  have h2 := coeff_prod_next (xs.take (n + 1)) (by simp; omega)
  rw [List.length_take, Nat.min_eq_left hx, Nat.add_sub_cancel] at h2
  rw [h1, h2]
  ring

/-! ## One error -/

/-- A polynomial of degree at most `k` vanishing on `k + 1` distinct points is zero. -/
theorem eq_zero_of_roots [DecidableEq F] {Q : F[X]} {k : ℕ} (hQ : Q.natDegree ≤ k) (s : Finset F)
    (hs : k + 1 ≤ s.card) (h0 : ∀ x ∈ s, Q.eval x = 0) : Q = 0 := by
  by_contra hne
  have := Polynomial.card_le_degree_of_subset_roots (p := Q) (Z := s) fun x hx ↦
    (mem_roots hne).mpr (h0 x hx)
  omega

/-- A polynomial of degree at most `k` vanishing on the `k` distinct points of `l` is its
coefficient `k` times their nodal polynomial. -/
theorem eq_C_mul_prod [DecidableEq F] {Q : F[X]} (l : List F) (hl : l.Nodup) (hQ : Q.natDegree ≤ l.length)
    (h0 : ∀ x ∈ l, Q.eval x = 0) :
    Q = C (Q.coeff l.length) * (l.map fun x ↦ X - C x).prod := by
  by_cases hz : Q = 0
  · simp [hz]
  have hdvd : ((l : Multiset F).map fun x ↦ X - C x).prod ∣ Q := by
    rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hz]
    refine (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hl)).mpr fun x hx ↦ ?_
    exact (mem_roots hz).mpr (h0 x hx)
  obtain ⟨R, hR⟩ := hdvd
  rw [← prod_eq_multiset] at hR
  have hm : (l.map fun x ↦ X - C x).prod.Monic := by
    rw [prod_eq_multiset]; exact monic_multiset_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _
  have hdp : (l.map fun x ↦ X - C x).prod.natDegree = l.length := by
    rw [prod_eq_multiset, natDegree_multiset_prod_X_sub_C_eq_card]; simp
  have hR0 : R ≠ 0 := fun h ↦ hz (by rw [hR, h, mul_zero])
  have hdR : R.natDegree = 0 := by
    have := natDegree_mul' (p := (l.map fun x ↦ X - C x).prod) (q := R) (by
      rw [hm.leadingCoeff, one_mul]; exact leadingCoeff_ne_zero.mpr hR0)
    rw [← hR, hdp] at this
    omega
  rw [eq_C_of_natDegree_eq_zero hdR] at hR
  have hc : Q.coeff l.length = R.coeff 0 := by
    rw [hR, mul_comm, coeff_C_mul, ← hdp, ← Polynomial.leadingCoeff, hm.leadingCoeff, mul_one]
  rw [hc, hR, mul_comm]

/-- **One error, located**: the interpolant of `d + 3` points of distinct nodes, less a
polynomial `T` of degree at most `d` that agrees with every point but the `e`-th, is zero when
its top coefficient is, and otherwise the `e`-th point is an error at node
`x_{d+2} + a_{d+1}/a_{d+2}`. -/
theorem locate [DecidableEq F] {d : ℕ} {pts : List (F × F)} (hl : pts.length = d + 3)
    (hd : (pts.map (·.1)).Nodup) {T : F[X]} (hT : T.natDegree ≤ d) {e : ℕ} (he : e < d + 3)
    (hag : ∀ i (hi : i < pts.length), i ≠ e → T.eval pts[i].1 = pts[i].2) :
    ((nForm pts).2.getD (d + 2) 0 = 0 → nP (nForm pts).1 (nForm pts).2 = T) ∧
    ((nForm pts).2.getD (d + 2) 0 ≠ 0 → T.eval (pts[e]'(by omega)).1 ≠ (pts[e]'(by omega)).2 ∧
      (pts[e]'(by omega)).1 = (pts[d + 2]'(by omega)).1 +
        (nForm pts).2.getD (d + 1) 0 / (nForm pts).2.getD (d + 2) 0) := by
  obtain ⟨hxs, hlen⟩ := nForm_fst pts
  set xs := (nForm pts).1
  set as := (nForm pts).2
  have hev := nForm_eval pts hd
  set Q := nP xs as - T with hQ
  have hlx : xs.length = d + 3 := by rw [hxs, List.length_map, hl]
  have hdQ : Q.natDegree ≤ d + 2 :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_nP xs as).trans (by omega)) (by omega))
  have hc2 : Q.coeff (d + 2) = as.getD (d + 2) 0 := by
    rw [hQ, coeff_sub, coeff_nP_top xs as (d + 2) (by rw [hlen, hl]) (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega : T.natDegree < d + 2), sub_zero]
  have hc1 : Q.coeff (d + 1) = as.getD (d + 1) 0 - as.getD (d + 2) 0 * (xs.take (d + 2)).sum := by
    rw [hQ, coeff_sub, coeff_nP_sub xs as (d + 1) (by rw [hlen, hl]) (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega : T.natDegree < d + 1), sub_zero]
  have hQi : ∀ i (hi : i < pts.length), i ≠ e → Q.eval pts[i].1 = 0 := fun i hi hie ↦ by
    rw [hQ, eval_sub, hev _ (List.getElem_mem hi), hag i hi hie, sub_self]
  have hpe : e < pts.length := by omega
  set l := (pts.eraseIdx e).map (·.1) with hldef
  have hll : l.length = d + 2 := by
    rw [hldef, List.length_map, List.length_eraseIdx_of_lt hpe, hl]; rfl
  have hlnd : l.Nodup := by
    rw [hldef, ← List.eraseIdx_map]
    exact hd.sublist (List.eraseIdx_sublist _ _)
  have hl0 : ∀ x ∈ l, Q.eval x = 0 := fun x hx ↦ by
    rw [hldef, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    rw [List.getElem_eraseIdx]
    have hjl : j < pts.length - 1 := by
      rw [List.length_eraseIdx_of_lt hpe] at hj; exact hj
    split_ifs with hje
    · exact hQi j (by omega) (by omega)
    · exact hQi (j + 1) (by omega) (by omega)
  have hQeq := eq_C_mul_prod l hlnd (by rw [hll]; exact hdQ) hl0
  rw [hll, hc2] at hQeq
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · rw [h0, C_0, zero_mul, hQ, sub_eq_zero] at hQeq
    exact hQeq
  · refine ⟨fun hok ↦ h0 ?_, ?_⟩
    · have hall : ∀ i (hi : i < pts.length), Q.eval pts[i].1 = 0 := fun i hi ↦ by
        by_cases hie : i = e
        · subst hie; rw [hQ, eval_sub, hev _ (List.getElem_mem hi), hok, sub_self]
        · exact hQi i hi hie
      have hz := eq_zero_of_roots hdQ (pts.map (·.1)).toFinset
        (by rw [List.toFinset_card_of_nodup hd, List.length_map, hl]) fun x hx ↦ by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
          simp only [List.getElem_map]
          exact hall i (by simpa using hi)
      rw [← hc2, hz, coeff_zero]
    · have hcoef := congrArg (·.coeff (d + 1)) hQeq
      rw [coeff_C_mul, show d + 1 = l.length - 1 by omega, coeff_prod_next l (by omega),
        show l.length - 1 = d + 1 by omega, hc1] at hcoef
      have hsplit : pts.map (·.1) = (pts.take e).map (·.1) ++ [(pts[e]'hpe).1] ++
          (pts.drop (e + 1)).map (·.1) := by
        rw [List.map_take, List.map_drop, List.append_assoc, List.singleton_append]
        conv_lhs => rw [← List.take_append_drop e (pts.map (·.1)),
          List.drop_eq_getElem_cons (by simpa using hpe)]
        rw [List.getElem_map]
      have hlsum : l.sum + (pts[e]'hpe).1 = (pts.map (·.1)).sum := by
        rw [hsplit, hldef, List.eraseIdx_eq_take_drop_succ, List.map_append, List.sum_append,
          List.sum_append, List.sum_append, List.sum_singleton]
        ring
      have htake : (xs.take (d + 2)).sum + (pts[d + 2]'(by omega)).1 = (pts.map (·.1)).sum := by
        have hx2 : xs = xs.take (d + 2) ++ [(pts[d + 2]'(by omega)).1] := by
          conv_lhs => rw [← List.take_append_drop (d + 2) xs]
          congr 1
          rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
          simp [xs, hxs]
        rw [← hxs]
        conv_rhs => rw [hx2]
        rw [List.sum_append, List.sum_singleton]
      have key : as.getD (d + 2) 0 * ((pts[e]'hpe).1 - (pts[d + 2]'(by omega)).1) =
          as.getD (d + 1) 0 := by
        linear_combination (-1 : F) * hcoef + as.getD (d + 2) 0 * hlsum -
          as.getD (d + 2) 0 * htake
      rw [← key, mul_div_cancel_left₀ _ h0]
      ring

/-- **Decoding one error** among `d + 3` points: the interpolant if its top two coefficients are
zero; otherwise the interpolant of the points but the first whose node `x` has
`a_{d+2}·(x − x_{d+2}) = a_{d+1}` (the located node, found without a division), if there is one
and its top coefficient is zero. -/
def decode1 [DecidableEq F] (d : ℕ) (pts : List (F × F)) : Option (List F × List F) :=
  let f := nForm pts
  if f.2.getD (d + 2) 0 = 0 then
    if f.2.getD (d + 1) 0 = 0 then some f else none
  else
    let x2 := (pts.getD (d + 2) (0, 0)).1
    let pts' := pts.eraseIdx (pts.findIdx fun p ↦
      decide (f.2.getD (d + 2) 0 * (p.1 - x2) = f.2.getD (d + 1) 0))
    if pts'.length = d + 2 ∧ (nForm pts').2.getD (d + 1) 0 = 0 then some (nForm pts') else none

theorem natDegree_le_of_top {P : F[X]} {d : ℕ} (hP : P.natDegree ≤ d + 2) (h2 : P.coeff (d + 2) = 0)
    (h1 : P.coeff (d + 1) = 0) : P.natDegree ≤ d := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rcases (show n = d + 1 ∨ n = d + 2 ∨ d + 2 < n by omega) with rfl | rfl | h
  · exact h1
  · exact h2
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem natDegree_nForm_top {d : ℕ} (q : List (F × F)) (hq : q.length = d + 2)
    (h : (nForm q).2.getD (d + 1) 0 = 0) : (nP (nForm q).1 (nForm q).2).natDegree ≤ d := by
  obtain ⟨hxs, hlen⟩ := nForm_fst q
  refine natDegree_le_of_top ((natDegree_nP _ _).trans (by omega)) ?_ ?_
  · exact coeff_eq_zero_of_natDegree_lt ((natDegree_nP _ _).trans_lt (by omega))
  · rw [coeff_nP_top (nForm q).1 (nForm q).2 (d + 1) (by omega) (by rw [hxs]; simp; omega), h]

/-- **What one-error decoding returns has degree at most `d`.** -/
theorem natDegree_decode1 [DecidableEq F] {d : ℕ} {pts : List (F × F)} (hl : pts.length = d + 3)
    {f : List F × List F} (h : decode1 d pts = some f) : (nP f.1 f.2).natDegree ≤ d := by
  unfold decode1 at h
  obtain ⟨hxs, hlen⟩ := nForm_fst pts
  simp only at h
  split_ifs at h with h2 h1 h'
  · rw [Option.some.injEq] at h
    subst h
    refine natDegree_le_of_top ((natDegree_nP _ _).trans (by omega)) ?_ ?_
    · rw [coeff_nP_top _ _ (d + 2) (by omega) (by rw [hxs]; simp; omega), h2]
    · rw [coeff_nP_sub _ _ (d + 1) (by omega) (by rw [hxs]; simp; omega), h1, h2, zero_mul,
        sub_zero]
  · rw [Option.some.injEq] at h
    subst h
    exact natDegree_nForm_top _ h'.1 h'.2

/-- **One-error decoding returns the polynomial** of degree at most `d` that agrees with all of
`d + 3` points of distinct nodes but one. -/
theorem decode1_eq [DecidableEq F] {d : ℕ} {pts : List (F × F)} (hl : pts.length = d + 3)
    (hd : (pts.map (·.1)).Nodup) {T : F[X]} (hT : T.natDegree ≤ d) {e : ℕ} (he : e < d + 3)
    (hag : ∀ i (hi : i < pts.length), i ≠ e → T.eval pts[i].1 = pts[i].2) :
    ∃ f, decode1 d pts = some f ∧ nP f.1 f.2 = T := by
  obtain ⟨hA, hB⟩ := locate hl hd hT he hag
  obtain ⟨hxs, hlen⟩ := nForm_fst pts
  unfold decode1
  simp only
  by_cases h2 : (nForm pts).2.getD (d + 2) 0 = 0
  · have hPT := hA h2
    have h1 : (nForm pts).2.getD (d + 1) 0 = 0 := by
      have := coeff_nP_sub (nForm pts).1 (nForm pts).2 (d + 1) (by omega)
        (by rw [hxs]; simp; omega)
      rw [hPT, h2, zero_mul, sub_zero, coeff_eq_zero_of_natDegree_lt (by omega)] at this
      exact this.symm
    rw [ite_eq_left h2, ite_eq_left h1]
    exact ⟨_, rfl, hPT⟩
  · obtain ⟨-, hxe⟩ := hB h2
    have hpe : e < pts.length := by omega
    have hg : (pts.getD (d + 2) (0, 0)).1 = (pts[d + 2]'(by omega)).1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hsol : ∀ j (hj : j < pts.length), (nForm pts).2.getD (d + 2) 0 *
        ((pts[j]).1 - (pts.getD (d + 2) (0, 0)).1) = (nForm pts).2.getD (d + 1) 0 ↔ j = e := by
      intro j hj
      rw [hg]
      constructor
      · intro h
        have hx : (pts[j]).1 = (pts[e]'hpe).1 := by
          have h' : (pts[j]).1 - (pts[d + 2]'(by omega)).1 = (nForm pts).2.getD (d + 1) 0 /
              (nForm pts).2.getD (d + 2) 0 := by
            rw [← h, mul_div_cancel_left₀ _ h2]
          rw [hxe, ← h']
          ring
        have hnd := List.Nodup.getElem_inj_iff hd (i := j) (j := e) (hi := by simpa using hj)
          (hj := by simpa using hpe)
        simp only [List.getElem_map] at hnd
        exact hnd.mp hx
      · rintro rfl
        rw [hxe, add_sub_cancel_left, mul_div_cancel₀ _ h2]
    have hidx : pts.findIdx (fun p ↦ decide ((nForm pts).2.getD (d + 2) 0 *
        (p.1 - (pts.getD (d + 2) (0, 0)).1) = (nForm pts).2.getD (d + 1) 0)) = e := by
      rw [List.findIdx_eq hpe]
      refine ⟨decide_eq_true ((hsol e hpe).mpr rfl), fun j hj ↦ ?_⟩
      rw [decide_eq_false_iff_not]
      exact fun h ↦ absurd ((hsol j (by omega)).mp h) (by omega)
    rw [ite_eq_right h2, hidx]
    have hl' : (pts.eraseIdx e).length = d + 2 := by rw [List.length_eraseIdx_of_lt hpe, hl]; rfl
    have hd' : ((pts.eraseIdx e).map (·.1)).Nodup := by
      rw [← List.eraseIdx_map]; exact hd.sublist (List.eraseIdx_sublist _ _)
    obtain ⟨hxs', hlen'⟩ := nForm_fst (pts.eraseIdx e)
    have hev' := nForm_eval (pts.eraseIdx e) hd'
    have hPT : nP (nForm (pts.eraseIdx e)).1 (nForm (pts.eraseIdx e)).2 = T := by
      have hz := eq_zero_of_roots
        (Q := nP (nForm (pts.eraseIdx e)).1 (nForm (pts.eraseIdx e)).2 - T) (k := d + 1)
        ((natDegree_sub_le _ _).trans (max_le ((natDegree_nP _ _).trans (by omega)) (by omega)))
        ((pts.eraseIdx e).map (·.1)).toFinset
        (by rw [List.toFinset_card_of_nodup hd', List.length_map, hl'])
        fun x hx ↦ by
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
          have hj' : j < (pts.eraseIdx e).length := by simpa using hj
          simp only [List.getElem_map]
          rw [eval_sub, hev' _ (List.getElem_mem hj'), List.getElem_eraseIdx]
          have hj'' : j < pts.length - 1 := by rw [List.length_eraseIdx_of_lt hpe] at hj'; exact hj'
          split_ifs with hje
          · rw [hag j (by omega) (by omega), sub_self]
          · rw [hag (j + 1) (by omega) (by omega), sub_self]
      exact sub_eq_zero.mp hz
    have h1 : (nForm (pts.eraseIdx e)).2.getD (d + 1) 0 = 0 := by
      rw [← coeff_nP_top (nForm (pts.eraseIdx e)).1 (nForm (pts.eraseIdx e)).2 (d + 1) (by omega)
        (by rw [hxs']; simp; omega), hPT]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    rw [ite_eq_left ⟨hl', h1⟩]
    exact ⟨_, rfl, hPT⟩

end

end LeanVM.Protocol.Whir.Sound.Newton
