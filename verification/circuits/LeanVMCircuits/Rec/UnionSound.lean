module

public import Clean.Air.ProductCheck
public import LeanVMCircuits.Rec.ExtField
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

@[expose] public section

/-!
Soundness of the claim union's coverage check (`rec::tree::union`).

Each slot of a pool carries a claim's tuple `t = (1, label[0..6], member[0..4], 0, ...)` in `E^16` and a bit `on`
(the slot's selection bit times its validity on the children's side, its validity on the declared side). At the
point `(X, A)` the rows multiply `1 + on · (X + 1 + fp_A(t))` over each side's slots, `fp_A(t) = ∑_k eq(A, k) t_k`
with `eq(A, k) = ∏_j (A_j if bit j of k else 1 + A_j)`, and test the two products equal.

- `slots_eq`: with Boolean bits, a side's product is `∏ (X + fp_A(t))` over the multiset of its claims that are on
  (`E` has characteristic two).
- `poly_injective`: as polynomials in `(X, A)`, that product determines the multiset (`lem:gp`, through Clean's
  `eq_of_fingerprintProduct_eq`).
- `coverage_sound`: if the two multisets differ, the test holds on at most a `4N/|S|` fraction of the points
  `(X, A)` of `S^5`, `N` bounding both sides' slot counts (Schwartz-Zippel, the products being distinct polynomials
  of total degree at most `4N`). With `S = E` that is at most `4N/|E|`, within the `5N/|E|` the protocol budgets.
  The point is squeezed after the digests and the begin and selection bits, which fix both multisets
  (`Bind.tests_determined`), so the multisets do not depend on it.
- `chain_unique`: two chains of compressions from one chaining value, each with the start marker on its first block
  only, that end in one digest are the same chain, unless two of their compressions collide. A run's items carry the
  start in their counter word, so under collision resistance a digest has one parse.
-/

namespace LeanVMCircuits.Rec.UnionSound

open MvPolynomial

/-- A claim's tuple. -/
abbrev Tuple := Fin 16 → E

theorem one_add_one_E : (1 : E) + 1 = 0 := by rw [← two_E]; norm_num

/-! Fingerprints. -/

/-- `eq(A, k)` as a polynomial in `A`, bit `j` of `k` choosing `A_j` over `1 + A_j`. -/
noncomputable def eqW4 (k : Fin 16) : MvPolynomial (Fin 4) E :=
  ∏ j : Fin 4, if (k : ℕ).testBit j then X j else 1 + X j

/-- `fp_A(t)` as a polynomial in `A`. -/
noncomputable def fp4 (t : Tuple) : MvPolynomial (Fin 4) E := ∑ k : Fin 16, eqW4 k * C (t k)

/-- `eq(A, k)` as a polynomial in `(X, A)`, `A_j = X (j + 1)`. -/
noncomputable def eqW (k : Fin 16) : MvPolynomial (Fin 5) E :=
  ∏ j : Fin 4, if (k : ℕ).testBit j then X j.succ else 1 + X j.succ

/-- `fp_A(t)` as a polynomial in `(X, A)`. -/
noncomputable def fp (t : Tuple) : MvPolynomial (Fin 5) E := ∑ k : Fin 16, eqW k * C (t k)

/-- `∏ (X + fp_A(t))` over a multiset of claims. -/
noncomputable def poly (P : Multiset Tuple) : MvPolynomial (Fin 5) E := (P.map fun t => X 0 + fp t).prod

/-- `eq(a, k)` at a point. -/
noncomputable def eqAt (a : Fin 4 → E) (k : Fin 16) : E := ∏ j : Fin 4, if (k : ℕ).testBit j then a j else 1 + a j

/-- `fp_a(t)` at a point. -/
noncomputable def fpAt (a : Fin 4 → E) (t : Tuple) : E := ∑ k : Fin 16, eqAt a k * t k

/-- `∏ (x + fp_a(t))` at a point. -/
noncomputable def prodAt (P : Multiset Tuple) (x : E) (a : Fin 4 → E) : E := (P.map fun t => x + fpAt a t).prod

theorem eval_poly (P : Multiset Tuple) (f : Fin 5 → E) : eval f (poly P) = prodAt P (f 0) (Fin.tail f) := by
  simp only [poly, prodAt, map_multiset_prod, Multiset.map_map, Function.comp_def, map_add, eval_X, fp, fpAt,
    map_sum, map_mul, eval_C, eqW, eqAt, map_prod, apply_ite, map_one, Fin.tail]

/-- The Boolean point naming slot `k`. -/
noncomputable def point (k : Fin 16) (j : Fin 4) : E := if (k : ℕ).testBit j then 1 else 0

theorem testBit_eq_iff : ∀ k k' : Fin 16, (∀ j : Fin 4, (k' : ℕ).testBit j = (k : ℕ).testBit j) ↔ k' = k := by
  decide

theorem eval_eqW4 (k k' : Fin 16) : eval (point k) (eqW4 k') = if k' = k then 1 else 0 := by
  have factor : ∀ j : Fin 4,
      eval (point k) (if (k' : ℕ).testBit j then X j else 1 + X j) =
        if (k' : ℕ).testBit j = (k : ℕ).testBit j then 1 else 0 := by
    intro j
    by_cases h' : (k' : ℕ).testBit j <;> by_cases h : (k : ℕ).testBit j <;> simp [point, h, h', one_add_one_E]
  simp only [eqW4, map_prod, factor, Finset.prod_boole, Finset.mem_univ, true_implies]
  simp only [testBit_eq_iff]

theorem eval_fp4 (t : Tuple) (k : Fin 16) : eval (point k) (fp4 t) = t k := by
  simp only [fp4, map_sum, map_mul, eval_eqW4, eval_C, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem fp4_injective : Function.Injective fp4 := by
  intro s t h
  funext k
  have := congrArg (eval (point k)) h
  rwa [eval_fp4, eval_fp4] at this

theorem finSuccEquiv_C' (c : E) : finSuccEquiv E 4 (C c) = Polynomial.C (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem finSuccEquiv_fp (t : Tuple) : finSuccEquiv E 4 (fp t) = Polynomial.C (fp4 t) := by
  simp only [fp, fp4, eqW, eqW4, map_sum, map_mul, map_prod, apply_ite, map_add, map_one, finSuccEquiv_X_succ,
    finSuccEquiv_C']

theorem finSuccEquiv_poly (P : Multiset Tuple) :
    finSuccEquiv E 4 (poly P) = fingerprintProduct (fun t => -fp4 t) P := by
  simp only [poly, fingerprintProduct, map_multiset_prod, Multiset.map_map, Function.comp_def, map_add,
    finSuccEquiv_X_zero, finSuccEquiv_fp, Polynomial.C_neg, sub_neg_eq_add]

/-- Lemma `lem:gp` for the union: `∏ (X + fp_A(t))` determines the multiset. -/
theorem poly_injective {P Q : Multiset Tuple} (h : poly P = poly Q) : P = Q := by
  classical
  have hinj : Function.Injective fun t => -fp4 t := fun s t hst => fp4_injective (neg_inj.mp hst)
  apply eq_of_fingerprintProduct_eq hinj.injOn
  rw [← finSuccEquiv_poly, ← finSuccEquiv_poly, h]

theorem totalDegree_factor (t : Tuple) : (X 0 + fp t : MvPolynomial (Fin 5) E).totalDegree ≤ 4 := by
  refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_X]; norm_num) ?_)
  refine totalDegree_finsetSum_le fun k _ => (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, add_zero]
  refine (totalDegree_finsetProd _ _).trans ?_
  have : ∀ j : Fin 4, (if (k : ℕ).testBit j then X j.succ else 1 + X j.succ :
      MvPolynomial (Fin 5) E).totalDegree ≤ 1 := by
    intro j
    split
    · rw [totalDegree_X]
    · exact (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; norm_num) (by rw [totalDegree_X]))
  calc ∑ j : Fin 4, _ ≤ ∑ _j : Fin 4, 1 := Finset.sum_le_sum fun j _ => this j
    _ = 4 := by simp

theorem totalDegree_poly (P : Multiset Tuple) : (poly P).totalDegree ≤ 4 * Multiset.card P := by
  refine (totalDegree_multiset_prod _).trans ?_
  rw [Multiset.map_map]
  calc (P.map _).sum ≤ (P.map fun _ => 4).sum := Multiset.sum_map_le_sum_map _ _ fun t _ => totalDegree_factor t
    _ = 4 * Multiset.card P := by simp [mul_comm]

open Finset in
/-- If the multisets differ, `∏ (x + fp_a(t))` agrees on at most a `4N/|S|` fraction of the points `(x, a)` of
`S^5`. -/
theorem coverage_sound (P Q : Multiset Tuple) (N : ℕ) (hP : Multiset.card P ≤ N) (hQ : Multiset.card Q ≤ N)
    (hne : P ≠ Q) (S : Finset E) :
    (#{f ∈ Fintype.piFinset fun _ : Fin 5 => S | prodAt P (f 0) (Fin.tail f) = prodAt Q (f 0) (Fin.tail f)} :
      ℚ≥0) / (#S ^ 5 : ℚ≥0) ≤ 4 * N / #S := by
  have hp : poly P - poly Q ≠ 0 := sub_ne_zero.mpr fun h => hne (poly_injective h)
  have sz := schwartz_zippel_totalDegree hp S
  have hset : {f ∈ Fintype.piFinset fun _ : Fin 5 => S | eval f (poly P - poly Q) = 0} =
      {f ∈ Fintype.piFinset fun _ : Fin 5 => S | prodAt P (f 0) (Fin.tail f) = prodAt Q (f 0) (Fin.tail f)} := by
    apply Finset.filter_congr
    intro f _
    rw [map_sub, eval_poly, eval_poly, sub_eq_zero]
  rw [hset] at sz
  refine sz.trans ?_
  have hdeg : ((poly P - poly Q).totalDegree : ℚ≥0) ≤ 4 * N := by
    have := (totalDegree_sub _ _).trans (max_le ((totalDegree_poly P).trans (Nat.mul_le_mul_left 4 hP))
      ((totalDegree_poly Q).trans (Nat.mul_le_mul_left 4 hQ)))
    exact_mod_cast this
  exact div_le_div_of_nonneg_right hdeg (by positivity)

/-! The rows' products. -/

/-- A side's product at a point: `∏ (1 + on · (x1 + fp_a(t)))` over its slots, `x1 = x + 1`. -/
noncomputable def slotsAt (slots : List (E × Tuple)) (x1 : E) (a : Fin 4 → E) : E :=
  (slots.map fun p => 1 + p.1 * (x1 + fpAt a p.2)).prod

open Classical in
/-- The claims of the slots that are on. -/
noncomputable def onClaims (slots : List (E × Tuple)) : Multiset Tuple :=
  ((slots.filter fun p => p.1 = 1).map (·.2) : List Tuple)

theorem card_onClaims (slots : List (E × Tuple)) : Multiset.card (onClaims slots) ≤ slots.length := by
  classical
  simp only [onClaims, Multiset.coe_card, List.length_map]
  exact List.length_filter_le _ _

/-- With Boolean bits a side's product is `∏ (x + fp_a(t))` over its claims that are on. -/
theorem slots_eq (slots : List (E × Tuple)) (hb : ∀ p ∈ slots, p.1 = 0 ∨ p.1 = 1) (x : E) (a : Fin 4 → E) :
    slotsAt slots (x + 1) a = prodAt (onClaims slots) x a := by
  classical
  induction slots with
  | nil => simp [slotsAt, prodAt, onClaims]
  | cons p ps ih =>
    have ih := ih fun q hq => hb q (List.mem_cons_of_mem _ hq)
    simp only [slotsAt, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    rcases hb p (List.mem_cons_self ..) with h | h
    · simp [onClaims, h]
    · simp only [onClaims, List.filter_cons, h, decide_true, ↓reduceIte, List.map_cons, prodAt] at ih ⊢
      rw [← Multiset.cons_coe, Multiset.map_cons, Multiset.prod_cons, one_mul]
      congr 1
      linear_combination one_add_one_E

/-- The coverage test: if the selected child claims and the declared claims are different multisets, the two
sides' products agree on at most a `4N/|S|` fraction of the points `(x, a)` of `S^5`, each side at most `N`
slots with Boolean bits. -/
theorem union_coverage_sound (child declared : List (E × Tuple)) (N : ℕ) (hc : child.length ≤ N)
    (hd : declared.length ≤ N) (hbc : ∀ p ∈ child, p.1 = 0 ∨ p.1 = 1) (hbd : ∀ p ∈ declared, p.1 = 0 ∨ p.1 = 1)
    (hne : onClaims child ≠ onClaims declared) (S : Finset E) :
    (Finset.card {f ∈ Fintype.piFinset fun _ : Fin 5 => S |
        slotsAt child (f 0 + 1) (Fin.tail f) = slotsAt declared (f 0 + 1) (Fin.tail f)} : ℚ≥0) /
      (S.card ^ 5 : ℚ≥0) ≤ 4 * N / S.card := by
  have hset : {f ∈ Fintype.piFinset fun _ : Fin 5 => S |
      slotsAt child (f 0 + 1) (Fin.tail f) = slotsAt declared (f 0 + 1) (Fin.tail f)} =
      {f ∈ Fintype.piFinset fun _ : Fin 5 => S |
        prodAt (onClaims child) (f 0) (Fin.tail f) = prodAt (onClaims declared) (f 0) (Fin.tail f)} := by
    apply Finset.filter_congr
    intro f _
    rw [slots_eq child hbc, slots_eq declared hbd]
  rw [hset]
  exact coverage_sound _ _ N ((card_onClaims child).trans hc) ((card_onClaims declared).trans hd) hne S

/-! Parse uniqueness. -/

section Chains

variable {H B : Type} (F : H × B → H) (h0 : H)

/-- The chaining value after blocks `bs`, listed last first: `back (b :: bs) = F (back bs, b)`. -/
def back : List B → H
  | [] => h0
  | b :: bs => F (back bs, b)

/-- The compressions' inputs. -/
def inputs : List B → List (H × B)
  | [] => []
  | b :: bs => (back F h0 bs, b) :: inputs bs

/-- Blocks listed last first whose start marker is on the first block only. -/
def StartsOnce (start : B → Prop) (bs : List B) : Prop :=
  bs ≠ [] ∧ (∀ b ∈ bs.getLast?, start b) ∧ ∀ b ∈ bs.dropLast, ¬ start b

theorem StartsOnce.tail {start : B → Prop} {b : B} {bs : List B} (h : StartsOnce start (b :: bs)) (hbs : bs ≠ []) :
    StartsOnce start bs ∧ ¬ start b := by
  obtain ⟨-, hl, hd⟩ := h
  rw [List.getLast?_cons_of_ne_nil hbs] at hl
  rw [List.dropLast_cons_of_ne_nil hbs] at hd
  exact ⟨⟨hbs, hl, fun c hc => hd c (List.mem_cons_of_mem _ hc)⟩, hd b (List.mem_cons_self ..)⟩

theorem StartsOnce.single {start : B → Prop} {b : B} (h : StartsOnce start [b]) : start b :=
  h.2.1 b (by simp)

/-- Two chains from `h0` with the start marker on their first blocks only that end in one chaining value are the
same, unless a compression of one collides with a compression of the other. -/
theorem chain_unique {start : B → Prop} :
    ∀ (bs bs' : List B), StartsOnce start bs → StartsOnce start bs' →
      (∀ x ∈ inputs F h0 bs, ∀ y ∈ inputs F h0 bs', F x = F y → x = y) →
      back F h0 bs = back F h0 bs' → bs = bs'
  | [], _, h, _, _, _ => absurd rfl h.1
  | _, [], _, h', _, _ => absurd rfl h'.1
  | b :: bs, b' :: bs', h, h', hcr, heq => by
    have hx := hcr _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) heq
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hback, rfl⟩ := hx
    by_cases hbs : bs = []
    · subst hbs
      by_cases hbs' : bs' = []
      · rw [hbs']
      · exact absurd h.single (h'.tail hbs').2
    · by_cases hbs' : bs' = []
      · subst hbs'
        exact absurd h'.single (h.tail hbs).2
      · rw [chain_unique bs bs' (h.tail hbs).1 (h'.tail hbs').1
          (fun x hx y hy => hcr x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hback]

end Chains

end LeanVMCircuits.Rec.UnionSound
