/-
Subspace polynomials: the first statement of Proposition 3.3 of the paper (`L_V` is linearized),
and the locator of a flat used in the proof of Proposition 3.4(c).

For a finite additive subgroup `V` of a field `K`, `subPoly V = ∏_{v ∈ V} (X - v)`. It is additive
over any field (`subPoly_comp_add`, `subPoly_eval_add`) and vanishes exactly on `V`
(`subPoly_eval_eq_zero`). In characteristic two a finite additive subgroup is an `𝔽₂`-subspace, its
size is a power of two (`exists_card_eq_two_pow`), and `subPoly V` is linearized: its only nonzero
coefficients are at exponents that are powers of two (`subPoly_isLinearized`), so
`subPoly V - X ^ |V|` has degree at most `|V| / 2` (`natDegree_subPoly_sub_le`).
-/
import Mathlib

open Polynomial
open scoped Classical

namespace Constructions

variable {K : Type*} [Field K]

/-! ### Locators of finite sets -/

/-- The locator `∏_{s ∈ S} (X - s)` of a finite set. -/
noncomputable def locator (S : Finset K) : K[X] := ∏ s ∈ S, (X - C s)

theorem locator_monic (S : Finset K) : (locator S).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C s

theorem locator_ne_zero (S : Finset K) : locator S ≠ 0 := (locator_monic S).ne_zero

theorem locator_natDegree (S : Finset K) : (locator S).natDegree = S.card := by
  rw [locator, natDegree_prod_of_monic _ _ fun s _ => monic_X_sub_C s]
  simp

theorem locator_degree (S : Finset K) : (locator S).degree = S.card := by
  rw [degree_eq_natDegree (locator_ne_zero S), locator_natDegree]

theorem locator_eval (S : Finset K) (x : K) : (locator S).eval x = ∏ s ∈ S, (x - s) := by
  simp [locator, eval_prod]

theorem locator_eval_eq_zero {S : Finset K} {x : K} : (locator S).eval x = 0 ↔ x ∈ S := by
  rw [locator_eval, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    rwa [sub_eq_zero.mp h]
  · intro h
    exact ⟨x, h, sub_self x⟩

theorem locator_injective : Function.Injective (locator : Finset K → K[X]) := by
  intro S T h
  ext x
  rw [← locator_eval_eq_zero, h, locator_eval_eq_zero]

theorem locator_union {S T : Finset K} (h : Disjoint S T) :
    locator (S ∪ T) = locator S * locator T :=
  Finset.prod_union h

/-- The locator of a translate `S + a`. -/
theorem locator_image_add (S : Finset K) (a : K) :
    locator (S.image (· + a)) = (locator S).comp (X - C a) := by
  rw [locator, Finset.prod_image (fun x _ y _ h => add_right_cancel h), locator, prod_comp]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [C_add, sub_comp, X_comp, C_comp]
  ring

/-! ### Finite additive subgroups -/

/-- The points of an additive subgroup as a finset (empty when the subgroup is infinite). -/
noncomputable def pts (V : AddSubgroup K) : Finset K :=
  if h : (V : Set K).Finite then h.toFinset else ∅

theorem mem_pts {V : AddSubgroup K} [Finite V] {x : K} : x ∈ pts V ↔ x ∈ V := by
  have h : (V : Set K).Finite := Set.toFinite _
  simp [pts, h]

theorem card_pts (V : AddSubgroup K) [Finite V] : (pts V).card = Nat.card V := by
  have h : (V : Set K).Finite := Set.toFinite _
  rw [pts, dite_eq_left h, ← Set.ncard_eq_toFinset_card _ h]
  exact (Nat.card_coe_set_eq (V : Set K)).symm

theorem pts_injective {V W : AddSubgroup K} [Finite V] [Finite W] (h : pts V = pts W) : V = W := by
  ext x
  rw [← mem_pts, h, mem_pts]

theorem card_pts_pos (V : AddSubgroup K) [Finite V] : 0 < (pts V).card :=
  Finset.card_pos.mpr ⟨0, mem_pts.mpr V.zero_mem⟩

/-- The subspace polynomial `L_V = ∏_{v ∈ V} (X - v)`. -/
noncomputable def subPoly (V : AddSubgroup K) : K[X] := locator (pts V)

theorem subPoly_monic (V : AddSubgroup K) : (subPoly V).Monic := locator_monic _

theorem subPoly_natDegree (V : AddSubgroup K) [Finite V] : (subPoly V).natDegree = Nat.card V := by
  rw [subPoly, locator_natDegree, card_pts]

/-- `L_V` vanishes exactly on `V`. -/
theorem subPoly_eval_eq_zero {V : AddSubgroup K} [Finite V] {x : K} :
    (subPoly V).eval x = 0 ↔ x ∈ V := by
  rw [subPoly, locator_eval_eq_zero, mem_pts]

theorem subPoly_injective {V W : AddSubgroup K} [Finite V] [Finite W]
    (h : subPoly V = subPoly W) : V = W :=
  pts_injective (locator_injective h)

/-- `L_V` is invariant under translation by `V`. -/
theorem subPoly_eval_add_mem (V : AddSubgroup K) [Finite V] {v : K} (hv : v ∈ V) (b : K) :
    (subPoly V).eval (b + v) = (subPoly V).eval b := by
  rw [subPoly, locator_eval, locator_eval]
  refine Finset.prod_nbij' (fun s => s - v) (fun s => s + v) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    exact mem_pts.mpr (V.sub_mem (mem_pts.mp hs) hv)
  · intro s hs
    exact mem_pts.mpr (V.add_mem (mem_pts.mp hs) hv)
  · intro s _
    ring
  · intro s _
    ring
  · intro s _
    ring

/-- Additivity of `L_V`, as an identity of polynomials: `L_V(X + b) = L_V(X) + L_V(b)`. It holds
over every field: the difference has degree below `|V|` and vanishes on `V`. -/
theorem subPoly_comp_add (V : AddSubgroup K) [Finite V] (b : K) :
    (subPoly V).comp (X + C b) = subPoly V + C ((subPoly V).eval b) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero (pts V) ?_ ?_
  · have e : (subPoly V).comp (X + C b) = locator ((pts V).image (· + -b)) := by
      rw [locator_image_add, subPoly, C_neg, sub_neg_eq_add]
    have hcard : ((pts V).image (· + -b)).card = (pts V).card :=
      Finset.card_image_of_injective _ fun x y h => add_right_cancel h
    have h1 : ((subPoly V).comp (X + C b) - subPoly V).degree < ((pts V).card : WithBot ℕ) := by
      rw [e]
      have := degree_sub_lt_left (p := locator ((pts V).image (· + -b))) (q := subPoly V)
        (by rw [subPoly, locator_degree, locator_degree, hcard]) (locator_ne_zero _)
        (by rw [(locator_monic _).leadingCoeff, (subPoly_monic V).leadingCoeff])
      rwa [locator_degree, hcard] at this
    have h2 : (C ((subPoly V).eval b)).degree < ((pts V).card : WithBot ℕ) :=
      lt_of_le_of_lt degree_C_le (by exact_mod_cast card_pts_pos V)
    rw [← sub_sub]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt h1 h2)
  · intro v hv
    have hv' : v ∈ V := mem_pts.mp hv
    have h0 : (subPoly V).eval v = 0 := subPoly_eval_eq_zero.mpr hv'
    simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C, h0, zero_add]
    rw [add_comm v b, subPoly_eval_add_mem V hv' b, sub_self]

/-- Additivity of `L_V` on values. -/
theorem subPoly_eval_add (V : AddSubgroup K) [Finite V] (a b : K) :
    (subPoly V).eval (a + b) = (subPoly V).eval a + (subPoly V).eval b := by
  have h := congrArg (eval a) (subPoly_comp_add V b)
  simpa [eval_comp] using h

/-- `L_V` as an additive map of `K`. -/
noncomputable def subPolyHom (V : AddSubgroup K) [Finite V] : K →+ K where
  toFun x := (subPoly V).eval x
  map_zero' := subPoly_eval_eq_zero.mpr V.zero_mem
  map_add' := subPoly_eval_add V

@[simp] theorem subPolyHom_apply (V : AddSubgroup K) [Finite V] (x : K) :
    subPolyHom V x = (subPoly V).eval x := rfl

/-- The locator of a coset: `L_{a + V}(X) = L_V(X) - L_V(a)`. -/
theorem locator_coset (V : AddSubgroup K) [Finite V] (a : K) :
    locator ((pts V).image (· + a)) = subPoly V - C ((subPoly V).eval a) := by
  have h := subPoly_comp_add V (-a)
  have hneg : (subPoly V).eval (-a) = -(subPoly V).eval a := by
    have := subPoly_eval_add V a (-a)
    rw [add_neg_cancel, subPoly_eval_eq_zero.mpr V.zero_mem] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  rw [locator_image_add, ← subPoly, sub_eq_add_neg X, ← C_neg, h, hneg, C_neg, sub_eq_add_neg]

theorem disjoint_pts_image (W : AddSubgroup K) [Finite W] {a : K} (ha : a ∉ W) :
    Disjoint (pts W) ((pts W).image (· + a)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
  apply ha
  have := W.sub_mem (mem_pts.mp hx) (mem_pts.mp hy)
  rwa [add_sub_cancel_left] at this

/-! ### Linearized polynomials -/

/-- A linearized polynomial (characteristic two): the only nonzero coefficients are at exponents
that are powers of two, `p = ∑_i c_i X ^ 2 ^ i`. -/
def IsLinearized (p : K[X]) : Prop := ∀ n, p.coeff n ≠ 0 → ∃ i : ℕ, n = 2 ^ i

theorem IsLinearized.add {p q : K[X]} (hp : IsLinearized p) (hq : IsLinearized q) :
    IsLinearized (p + q) := by
  intro n hn
  rw [coeff_add] at hn
  by_cases h : p.coeff n = 0
  · exact hq n (by rwa [h, zero_add] at hn)
  · exact hp n h

theorem IsLinearized.C_mul {p : K[X]} (hp : IsLinearized p) (c : K) : IsLinearized (C c * p) := by
  intro n hn
  rw [coeff_C_mul] at hn
  exact hp n (right_ne_zero_of_mul hn)

theorem isLinearized_X : IsLinearized (X : K[X]) := by
  intro n hn
  rw [coeff_X] at hn
  exact ⟨0, by rw [pow_zero]; by_contra h; exact hn (ite_eq_right (Ne.symm h))⟩

/-- A monic linearized polynomial of degree `2 ^ s` is `X ^ 2 ^ s` plus terms of degree at most
`2 ^ s / 2`. -/
theorem IsLinearized.natDegree_sub_le {p : K[X]} (hp : IsLinearized p) (hm : p.Monic) {s : ℕ}
    (hd : p.natDegree = 2 ^ s) : (p - X ^ 2 ^ s).natDegree ≤ 2 ^ s / 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_sub, coeff_X_pow]
  by_cases hN2 : N = 2 ^ s
  · rw [ite_eq_left hN2, hN2, ← hd, hm.coeff_natDegree, sub_self]
  · rw [ite_eq_right hN2, sub_zero]
    by_contra hc
    obtain ⟨i, hi⟩ := hp N hc
    have hle : N ≤ 2 ^ s := hd ▸ le_natDegree_of_ne_zero hc
    have hlt : N < 2 ^ s := lt_of_le_of_ne hle hN2
    have his : i < s := by
      rw [hi] at hlt
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    have : 2 ^ i ≤ 2 ^ s / 2 := by
      obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
      rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-! ### Characteristic two: the induction on the dimension -/

section CharTwo

variable [CharP K 2]

/-- `W + {0, a}`: the subgroup generated by `W` and `a` in characteristic two. -/
def adjoin (W : AddSubgroup K) (a : K) : AddSubgroup K where
  carrier := {x | x ∈ W ∨ x + a ∈ W}
  zero_mem' := Or.inl W.zero_mem
  add_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (W.add_mem hx hy)
    · refine Or.inr ?_
      have := W.add_mem hx hy
      rwa [← add_assoc] at this
    · refine Or.inr ?_
      have := W.add_mem hx hy
      rwa [add_right_comm] at this
    · refine Or.inl ?_
      have h := W.add_mem hx hy
      have e : x + a + (y + a) = x + y := by
        linear_combination CharTwo.add_self_eq_zero a
      rwa [e] at h
  neg_mem' := by
    intro x hx
    rw [CharTwo.neg_eq]
    exact hx

theorem mem_adjoin {W : AddSubgroup K} {a x : K} : x ∈ adjoin W a ↔ x ∈ W ∨ x + a ∈ W := Iff.rfl

theorem le_adjoin (W : AddSubgroup K) (a : K) : W ≤ adjoin W a := fun _ hx => Or.inl hx

theorem self_mem_adjoin (W : AddSubgroup K) (a : K) : a ∈ adjoin W a :=
  Or.inr (by rw [CharTwo.add_self_eq_zero]; exact W.zero_mem)

theorem coe_adjoin_subset (W : AddSubgroup K) [Finite W] (a : K) :
    (adjoin W a : Set K) ⊆ ↑(pts W ∪ (pts W).image (· + a)) := by
  intro x hx
  rcases hx with hx | hx
  · exact Finset.mem_coe.mpr (Finset.mem_union_left _ (mem_pts.mpr hx))
  · refine Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x + a, mem_pts.mpr hx, ?_⟩))
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

instance adjoin_finite (W : AddSubgroup K) [Finite W] (a : K) : Finite (adjoin W a) :=
  Set.finite_coe_iff.mpr ((Finset.finite_toSet _).subset (coe_adjoin_subset W a))

theorem pts_adjoin (W : AddSubgroup K) [Finite W] (a : K) :
    pts (adjoin W a) = pts W ∪ (pts W).image (· + a) := by
  ext x
  rw [mem_pts, mem_adjoin, Finset.mem_union, mem_pts, Finset.mem_image]
  refine or_congr Iff.rfl ⟨fun h => ⟨x + a, mem_pts.mpr h, ?_⟩, ?_⟩
  · rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rintro ⟨y, hy, rfl⟩
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    exact mem_pts.mp hy

theorem card_adjoin (W : AddSubgroup K) [Finite W] {a : K} (ha : a ∉ W) :
    Nat.card (adjoin W a) = 2 * Nat.card W := by
  rw [← card_pts, pts_adjoin, Finset.card_union_of_disjoint (disjoint_pts_image W ha),
    Finset.card_image_of_injective _ fun x y h => add_right_cancel h, card_pts, two_mul]

/-- The recursion on the dimension: `L_{W + {0, a}} = L_W² + L_W(a) L_W`. -/
theorem subPoly_adjoin (W : AddSubgroup K) [Finite W] {a : K} (ha : a ∉ W) :
    subPoly (adjoin W a) = subPoly W ^ 2 + C ((subPoly W).eval a) * subPoly W := by
  rw [subPoly, pts_adjoin, locator_union (disjoint_pts_image W ha), locator_coset, ← subPoly,
    sub_eq_add_neg, ← C_neg, CharTwo.neg_eq]
  ring

/-- Induction on finite additive subgroups in characteristic two (that is, on `𝔽₂`-subspaces of
finite dimension): from `{0}`, adjoining one element outside at a time. -/
theorem addSubgroup_induction {P : AddSubgroup K → Prop} (h0 : P ⊥)
    (hstep : ∀ (W : AddSubgroup K) (a : K) [Finite W], a ∉ W → P W → P (adjoin W a))
    (V : AddSubgroup K) [Finite V] : P V := by
  have key : ∀ S : Finset K, Finite (AddSubgroup.closure (S : Set K)) ∧
      P (AddSubgroup.closure (S : Set K)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty, AddSubgroup.closure_empty]
      exact ⟨inferInstance, h0⟩
    | insert a S _ ih =>
      obtain ⟨hfin, hP⟩ := ih
      by_cases ha : a ∈ AddSubgroup.closure (S : Set K)
      · have e : AddSubgroup.closure ((insert a S : Finset K) : Set K) =
            AddSubgroup.closure (S : Set K) := by
          refine le_antisymm ?_ (AddSubgroup.closure_mono (by simp))
          rw [AddSubgroup.closure_le, Finset.coe_insert]
          exact Set.insert_subset ha AddSubgroup.subset_closure
        rw [e]
        exact ⟨hfin, hP⟩
      · have e : AddSubgroup.closure ((insert a S : Finset K) : Set K) =
            adjoin (AddSubgroup.closure (S : Set K)) a := by
          refine le_antisymm ?_ ?_
          · rw [AddSubgroup.closure_le, Finset.coe_insert]
            refine Set.insert_subset (self_mem_adjoin _ a) ?_
            exact AddSubgroup.subset_closure.trans (le_adjoin _ a)
          · have hle : AddSubgroup.closure (S : Set K) ≤
                AddSubgroup.closure ((insert a S : Finset K) : Set K) :=
              AddSubgroup.closure_mono (by simp)
            have haS : a ∈ AddSubgroup.closure ((insert a S : Finset K) : Set K) :=
              AddSubgroup.subset_closure (by simp)
            rintro x (hx | hx)
            · exact hle hx
            · have := AddSubgroup.sub_mem _ (hle hx) haS
              rwa [add_sub_cancel_right] at this
        rw [e]
        exact ⟨inferInstance, hstep _ a ha hP⟩
  have e : AddSubgroup.closure ((pts V : Finset K) : Set K) = V := by
    have : ((pts V : Finset K) : Set K) = (V : Set K) := by
      ext x
      exact mem_pts
    rw [this, AddSubgroup.closure_eq]
  rw [← e]
  exact (key (pts V)).2

/-- A finite additive subgroup of a field of characteristic two has `2 ^ s` elements. -/
theorem exists_card_eq_two_pow (V : AddSubgroup K) [Finite V] : ∃ s : ℕ, Nat.card V = 2 ^ s := by
  induction V using addSubgroup_induction with
  | h0 => exact ⟨0, by simp⟩
  | hstep W a ha ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s + 1, by rw [card_adjoin W ha, hs, pow_succ']⟩

/-- The square of a linearized polynomial is linearized. -/
theorem IsLinearized.sq {p : K[X]} (hp : IsLinearized p) : IsLinearized (p ^ 2) := by
  intro n hn
  rw [← map_frobenius_expand (p := 2), coeff_map, coeff_expand (by norm_num)] at hn
  by_cases h2 : 2 ∣ n
  · rw [ite_eq_left h2] at hn
    have hc : p.coeff (n / 2) ≠ 0 := by
      intro h0
      exact hn (by rw [h0, map_zero])
    obtain ⟨i, hi⟩ := hp _ hc
    exact ⟨i + 1, by rw [pow_succ, ← hi, Nat.div_mul_cancel h2]⟩
  · rw [ite_eq_right h2, map_zero] at hn
    exact absurd rfl hn

/-- `L_V` is linearized. -/
theorem subPoly_isLinearized (V : AddSubgroup K) [Finite V] : IsLinearized (subPoly V) := by
  induction V using addSubgroup_induction with
  | h0 =>
    have : subPoly (⊥ : AddSubgroup K) = X := by
      have hp : pts (⊥ : AddSubgroup K) = {0} := by
        ext x
        rw [mem_pts, AddSubgroup.mem_bot, Finset.mem_singleton]
      rw [subPoly, hp, locator, Finset.prod_singleton, C_0, sub_zero]
    rw [this]
    exact isLinearized_X
  | hstep W a ha ih =>
    rw [subPoly_adjoin W ha]
    exact ih.sq.add (ih.C_mul _)

/-- A linearized polynomial is additive on every commutative `K`-algebra:
`p(x + y) = p(x) + p(y)`. With `A` a polynomial ring in two variables over `K` this is the identity
`p(X + Y) = p(X) + p(Y)` of polynomials. -/
theorem IsLinearized.aeval_add {p : K[X]} (hp : IsLinearized p) {A : Type*} [CommRing A]
    [Algebra K A] (x y : A) : aeval (x + y) p = aeval x p + aeval y p := by
  have h2 : (2 : A) = 0 := by
    have := congrArg (algebraMap K A) (CharTwo.two_eq_zero (R := K))
    rwa [map_ofNat, map_zero] at this
  have hpow : ∀ i : ℕ, (x + y) ^ 2 ^ i = x ^ 2 ^ i + y ^ 2 ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, pow_mul, ih, pow_mul, pow_mul]
      linear_combination (x ^ 2 ^ i * y ^ 2 ^ i) * h2
  rw [aeval_eq_sum_range, aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : p.coeff n = 0
  · rw [hn, zero_smul, zero_smul, zero_smul, add_zero]
  · obtain ⟨i, rfl⟩ := hp n hn
    rw [hpow, smul_add]

/-- `L_V(x + y) = L_V(x) + L_V(y)` in every commutative `K`-algebra, in particular as an identity
of polynomials in two variables. -/
theorem subPoly_aeval_add (V : AddSubgroup K) [Finite V] {A : Type*} [CommRing A] [Algebra K A]
    (x y : A) : aeval (x + y) (subPoly V) = aeval x (subPoly V) + aeval y (subPoly V) :=
  (subPoly_isLinearized V).aeval_add x y

/-- `L_V = X ^ |V| + (degree at most |V| / 2)`: the gap of a flat is half its size. -/
theorem natDegree_subPoly_sub_le (V : AddSubgroup K) [Finite V] :
    (subPoly V - X ^ Nat.card V).natDegree ≤ Nat.card V / 2 := by
  obtain ⟨s, hs⟩ := exists_card_eq_two_pow V
  rw [hs]
  exact (subPoly_isLinearized V).natDegree_sub_le (subPoly_monic V)
    (by rw [subPoly_natDegree, hs])

end CharTwo

end Constructions
