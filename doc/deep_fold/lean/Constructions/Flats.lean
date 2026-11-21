/-
The flats lemma (Proposition 3.3 of the paper): the Johnson bound is tight at rate 1/4 on subspace
domains.

For a subspace `V` of size `2 ^ s`, `s ≥ 1`, the polynomial `Q_V = (X ^ 2 ^ s - L_V) / X` has
degree below `2 ^ (s - 1)` and takes the value `x ^ (2 ^ s - 1)` at every nonzero `x ∈ V`. So the
single word `x ↦ x ^ (2 ^ s - 1)` has one list member per subspace of size `2 ^ s` of the domain
(`flats_list`), and at least `|D| - 1` of them when `2 ^ s = |D| / 2` (`flats_quarter`): `n - 1`
polynomials of degree below `n / 4` at agreement `n / 2 - 1`.
-/
import Constructions.Subspace

open Polynomial
open scoped Classical

namespace Constructions

variable {K : Type*} [Field K]

/-! ### Lists -/

/-- The points of `D` where the polynomial `P` takes the value of the word `w`. -/
noncomputable def agree (D : Finset K) (w : K → K) (P : K[X]) : Finset K :=
  D.filter (fun x => P.eval x = w x)

/-- The list of the word `w` on the domain `D`: the polynomials of degree below `k` that agree
with `w` on at least `T` points of `D`. -/
def RSList (D : Finset K) (w : K → K) (k T : ℕ) : Set K[X] :=
  {P | P.degree < (k : WithBot ℕ) ∧ T ≤ (agree D w P).card}

/-! ### The polynomial of a flat -/

/-- `Q_V = (X ^ |V| - L_V) / X`. In characteristic two this is the `(L_V - X ^ |V|) / X` of
Proposition 3.3 of the paper. -/
noncomputable def flatPoly (V : AddSubgroup K) : K[X] := divX (X ^ Nat.card V - subPoly V)

theorem flatPoly_mul_X (V : AddSubgroup K) [Finite V] :
    flatPoly V * X = X ^ Nat.card V - subPoly V := by
  have h := divX_mul_X_add (X ^ Nat.card V - subPoly V)
  have h0 : (X ^ Nat.card V - subPoly V).coeff 0 = 0 := by
    have hpos : Nat.card V ≠ 0 := by
      rw [← card_pts]
      exact (card_pts_pos V).ne'
    rw [coeff_sub, coeff_X_pow, ite_eq_right (Ne.symm hpos), coeff_zero_eq_eval_zero,
      subPoly_eval_eq_zero.mpr V.zero_mem, sub_zero]
  rw [h0, C_0, add_zero] at h
  exact h

/-- `Q_V(x) = x ^ (|V| - 1)` at every nonzero point of `V`. -/
theorem flatPoly_eval (V : AddSubgroup K) [Finite V] {x : K} (hx : x ∈ V) (hx0 : x ≠ 0) :
    (flatPoly V).eval x = x ^ (Nat.card V - 1) := by
  have h := congrArg (eval x) (flatPoly_mul_X V)
  rw [eval_mul, eval_X, eval_sub, eval_pow, eval_X, subPoly_eval_eq_zero.mpr hx, sub_zero] at h
  have hpos : 0 < Nat.card V := by
    rw [← card_pts]
    exact card_pts_pos V
  have e : x ^ Nat.card V = x ^ (Nat.card V - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  rw [e] at h
  exact mul_right_cancel₀ hx0 h

/-- `Q_V = X ^ (|V| - 1) - ∏_{v ∈ V, v ≠ 0} (X - v)`. -/
theorem flatPoly_eq (V : AddSubgroup K) [Finite V] :
    flatPoly V = X ^ (Nat.card V - 1) - locator ((pts V).erase 0) := by
  have hpos : 0 < Nat.card V := by
    rw [← card_pts]
    exact card_pts_pos V
  have h0 : (0 : K) ∈ pts V := mem_pts.mpr V.zero_mem
  have hL : subPoly V = locator ((pts V).erase 0) * X := by
    rw [subPoly, locator, ← Finset.mul_prod_erase _ _ h0, C_0, sub_zero, mul_comm]
    rfl
  have h := flatPoly_mul_X V
  have e : X ^ Nat.card V - subPoly V =
      (X ^ (Nat.card V - 1) - locator ((pts V).erase 0)) * X := by
    rw [hL, sub_mul, ← pow_succ, Nat.sub_add_cancel hpos]
  rw [e] at h
  exact mul_right_cancel₀ X_ne_zero h

/-- `Q_V` agrees with the word `x ↦ x ^ (|V| - 1)` exactly on the nonzero points of `V`
(for `|V| ≥ 2`). -/
theorem agree_flatPoly (D : Finset K) (V : AddSubgroup K) [Finite V] (hVD : ∀ x ∈ V, x ∈ D)
    (hV : 2 ≤ Nat.card V) :
    agree D (fun x => x ^ (Nat.card V - 1)) (flatPoly V) = (pts V).erase 0 := by
  ext x
  rw [agree, Finset.mem_filter, Finset.mem_erase, mem_pts]
  constructor
  · rintro ⟨-, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [flatPoly_eq, eval_sub, eval_pow, eval_X, sub_eq_self, locator_eval_eq_zero] at hx
      exact (Finset.mem_erase.mp hx).1 rfl
    refine ⟨hx0, ?_⟩
    have h := congrArg (eval x) (flatPoly_mul_X V)
    rw [eval_mul, eval_X, eval_sub, eval_pow, eval_X, hx, ← pow_succ,
      Nat.sub_add_cancel (by omega), eq_comm, sub_eq_self] at h
    exact subPoly_eval_eq_zero.mp h
  · rintro ⟨hx0, hx⟩
    exact ⟨hVD x hx, flatPoly_eval V hx hx0⟩

/-- Distinct subspaces give distinct polynomials. -/
theorem flatPoly_injective {V W : AddSubgroup K} [Finite V] [Finite W]
    (hc : Nat.card V = Nat.card W) (h : flatPoly V = flatPoly W) : V = W := by
  apply subPoly_injective
  have hV := flatPoly_mul_X V
  have hW := flatPoly_mul_X W
  rw [h, hW, hc] at hV
  exact (sub_right_injective hV).symm

section CharTwo

variable [CharP K 2]

/-- `deg Q_V ≤ 2 ^ (s - 1) - 1` for `|V| = 2 ^ s`, `s ≥ 1`. -/
theorem flatPoly_natDegree_le (V : AddSubgroup K) [Finite V] :
    (flatPoly V).natDegree ≤ Nat.card V / 2 - 1 := by
  rw [flatPoly, natDegree_divX_eq_natDegree_tsub_one]
  have h := natDegree_subPoly_sub_le V
  rw [← natDegree_neg, neg_sub] at h
  exact Nat.sub_le_sub_right h 1

theorem flatPoly_degree_lt (V : AddSubgroup K) [Finite V] {s : ℕ} (hs : 1 ≤ s)
    (hV : Nat.card V = 2 ^ s) : (flatPoly V).degree < ((2 ^ (s - 1) : ℕ) : WithBot ℕ) := by
  have h := flatPoly_natDegree_le V
  obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
  rw [hV, pow_succ, Nat.mul_div_cancel _ (by norm_num)] at h
  rw [Nat.add_sub_cancel]
  have hpos : 0 < 2 ^ j := by positivity
  refine lt_of_le_of_lt degree_le_natDegree ?_
  exact_mod_cast (by omega : (flatPoly V).natDegree < 2 ^ j)

/-- The flats lemma, one subspace: `Q_V` is in the list of the word `x ↦ x ^ (2 ^ s - 1)` at
degree below `2 ^ (s - 1)` and agreement `2 ^ s - 1`, on any domain containing `V`. -/
theorem flatPoly_mem_RSList (D : Finset K) (V : AddSubgroup K) [Finite V] (hVD : ∀ x ∈ V, x ∈ D)
    {s : ℕ} (hs : 1 ≤ s) (hV : Nat.card V = 2 ^ s) :
    flatPoly V ∈ RSList D (fun x => x ^ (2 ^ s - 1)) (2 ^ (s - 1)) (2 ^ s - 1) := by
  refine ⟨flatPoly_degree_lt V hs hV, ?_⟩
  have hsub : (pts V).erase 0 ⊆ agree D (fun x => x ^ (2 ^ s - 1)) (flatPoly V) := by
    intro x hx
    obtain ⟨hx0, hxV⟩ := Finset.mem_erase.mp hx
    have hxV' : x ∈ V := mem_pts.mp hxV
    rw [agree, Finset.mem_filter]
    exact ⟨hVD x hxV', by rw [flatPoly_eval V hxV' hx0, hV]⟩
  have hcard : ((pts V).erase 0).card = 2 ^ s - 1 := by
    rw [Finset.card_erase_of_mem (mem_pts.mpr V.zero_mem), card_pts, hV]
  have h := Finset.card_le_card hsub
  rwa [hcard] at h

/-- The flats lemma: the word `x ↦ x ^ (2 ^ s - 1)` has at least as many polynomials of degree
below `2 ^ (s - 1)` agreeing with it on at least `2 ^ s - 1` points of `D` as `D` contains
subspaces of size `2 ^ s`. -/
theorem flats_list (D : Finset K) {s : ℕ} (hs : 1 ≤ s) :
    {V : AddSubgroup K | (∀ x ∈ V, x ∈ D) ∧ Nat.card V = 2 ^ s}.encard ≤
      (RSList D (fun x => x ^ (2 ^ s - 1)) (2 ^ (s - 1)) (2 ^ s - 1)).encard := by
  refine Set.encard_le_encard_of_injOn (f := flatPoly) ?_ ?_
  · rintro V ⟨hVD, hV⟩
    have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; positivity)
    exact flatPoly_mem_RSList D V hVD hs hV
  · rintro V ⟨_, hV⟩ W ⟨_, hW⟩ h
    have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; positivity)
    have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; positivity)
    exact flatPoly_injective (hV.trans hW.symm) h

/-! ### Counting hyperplanes -/

/-- A finite subspace `D` has at least `|D| - 1` subspaces of index two: the kernels of its
nonzero `𝔽₂`-linear functionals. -/
theorem card_hyperplanes_ge (D : AddSubgroup K) [Finite D] :
    ((Nat.card D - 1 : ℕ) : ℕ∞) ≤
      {V : AddSubgroup K | V ≤ D ∧ 2 * Nat.card V = Nat.card D}.encard := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  set M : Submodule (ZMod 2) K := AddSubgroup.toZModSubmodule 2 D with hM
  have : Finite M := ‹Finite D›
  have hmem : ∀ x : K, x ∈ M ↔ x ∈ D := fun x => Iff.rfl
  -- the kernel of a functional, as a subgroup of `K`
  let ker : Module.Dual (ZMod 2) M → AddSubgroup K := fun f =>
    { carrier := {x | ∃ h : x ∈ M, f ⟨x, h⟩ = 0}
      zero_mem' := ⟨M.zero_mem, map_zero f⟩
      add_mem' := by
        rintro x y ⟨hx, fx⟩ ⟨hy, fy⟩
        refine ⟨M.add_mem hx hy, ?_⟩
        have : (⟨x + y, M.add_mem hx hy⟩ : M) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
        rw [this, map_add, fx, fy, add_zero]
      neg_mem' := by
        rintro x ⟨hx, fx⟩
        refine ⟨M.neg_mem hx, ?_⟩
        have : (⟨-x, M.neg_mem hx⟩ : M) = -⟨x, hx⟩ := rfl
        rw [this, map_neg, fx, neg_zero] }
  have hker : ∀ f x, x ∈ ker f ↔ ∃ h : x ∈ M, f ⟨x, h⟩ = 0 := fun f x => Iff.rfl
  have hinj : Function.Injective ker := by
    intro f g hfg
    ext ⟨x, hx⟩
    have h1 : f ⟨x, hx⟩ = 0 ↔ g ⟨x, hx⟩ = 0 := by
      have := congrArg (fun V : AddSubgroup K => x ∈ V) hfg
      simp only [hker, eq_iff_iff] at this
      exact ⟨fun h => (this.mp ⟨hx, h⟩).2, fun h => (this.mpr ⟨hx, h⟩).2⟩
    have key : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
    exact key _ _ h1
  have hmaps : Set.MapsTo ker {f | f ≠ 0} {V : AddSubgroup K | V ≤ D ∧ 2 * Nat.card V = Nat.card D} := by
    intro f hf
    have hle : ker f ≤ D := fun x hx => ((hker f x).mp hx).1
    refine ⟨hle, ?_⟩
    have : Finite (ker f) :=
      Set.finite_coe_iff.mpr ((Set.toFinite (D : Set K)).subset hle)
    obtain ⟨⟨a, ha⟩, hfa⟩ : ∃ a : M, f a ≠ 0 := by
      by_contra hcon
      exact hf (LinearMap.ext fun a => by
        by_contra h
        exact hcon ⟨a, h⟩)
    have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    have hfa1 := key _ hfa
    have haker : a ∉ ker f := fun h => hfa ((hker f a).mp h).2
    have hD : D = adjoin (ker f) a := by
      ext x
      rw [mem_adjoin]
      constructor
      · intro hx
        by_cases hfx : f ⟨x, hx⟩ = 0
        · exact Or.inl ⟨hx, hfx⟩
        · refine Or.inr ⟨M.add_mem hx ha, ?_⟩
          have : (⟨x + a, M.add_mem hx ha⟩ : M) = ⟨x, hx⟩ + ⟨a, ha⟩ := rfl
          rw [this, map_add, key _ hfx, hfa1]
          decide
      · rintro (h | h)
        · exact hle h
        · have := D.sub_mem (hle h) ha
          rwa [add_sub_cancel_right] at this
    have hc := card_adjoin (ker f) haker
    rw [← hD] at hc
    exact hc.symm
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have : Finite (Module.Dual (ZMod 2) M) := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card (Module.Dual (ZMod 2) M) = Nat.card D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) M),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)]
    rfl
  have hne : ({f : Module.Dual (ZMod 2) M | f ≠ 0}).encard = ((Nat.card D - 1 : ℕ) : ℕ∞) := by
    have h1 : ({f : Module.Dual (ZMod 2) M | f ≠ 0}) = ({0} : Set (Module.Dual (ZMod 2) M))ᶜ := by
      ext f
      simp
    rw [h1, ← Set.Finite.cast_ncard_eq (Set.toFinite _), Set.ncard_compl, Set.ncard_singleton,
      hcard]
  rw [← hne]
  exact Set.encard_le_encard_of_injOn hmaps hinj.injOn

/-- Rate 1/4: on a subspace domain `D` of size `n = 2 ^ (s + 1)`, the word `x ↦ x ^ (n / 2 - 1)`
has at least `n - 1` polynomials of degree below `n / 4` that agree with it on at least
`n / 2 - 1` points. The Johnson radius of the code is `n / 2`. -/
theorem flats_quarter (D : AddSubgroup K) [Finite D] {s : ℕ} (hs : 1 ≤ s)
    (hD : Nat.card D = 2 ^ (s + 1)) :
    ((Nat.card D - 1 : ℕ) : ℕ∞) ≤
      (RSList (pts D) (fun x => x ^ (2 ^ s - 1)) (2 ^ (s - 1)) (2 ^ s - 1)).encard := by
  refine (card_hyperplanes_ge D).trans (le_trans (Set.encard_le_encard ?_) (flats_list (pts D) hs))
  rintro V ⟨hle, hc⟩
  refine ⟨fun x hx => mem_pts.mpr (hle hx), ?_⟩
  rw [hD, pow_succ'] at hc
  omega

end CharTwo

end Constructions
