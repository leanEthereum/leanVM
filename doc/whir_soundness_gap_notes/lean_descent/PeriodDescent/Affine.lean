/-
The base bound for affine spaces of codewords: note 04 Theorem 1.2, which is the proof of note 37
Lemma 3.2 as it is written (an induction on the dimension `r` of an affine space `H` of members).

* `affine_bound`: the induction, for any vector space `V` with evaluation functionals `ev x`. If
  every subspace of dimension `s ≥ 1` of `W₀` has at most `z s` common zeros among the points, then
  the members of an affine space `c₀ + W`, `W ≤ W₀` of dimension `r`, that agree with a word on `A`
  points or more satisfy `L ∏_{s = 1}^{r} (A - z s) ≤ ∏_{s = 1}^{r} (n - z s)`.
* `finrank_add_card_common_zeros_le`: a subspace of dimension `r` of the polynomials of degree
  `< k` has at most `k - r` common zeros (the MDS property of Reed-Solomon codes), by Lagrange
  interpolation and the rank theorem.
* `card_common_zeros_le`: through a map `ℓ` whose fibres on `D` have at most `m` points, at most
  `m (k - r)` common zeros in `D`.
* `affine_poly_bound`: note 37 Lemma 3.2 for an affine space of dimension `r` of polynomials of
  degree `< k` in `ℓ`: `L ∏_{s = 1}^{r} (A - m (k - s)) ≤ ∏_{s = 1}^{r} (n - m (k - s))`.
* `affine_ordinary_bound`: **note 04 Theorem 1.2**: for `ℓ = X`, `m = 1`: a list contained in an
  affine space of dimension `r` of polynomials of degree `< k`, each agreeing with a word on at
  least `T` of the `n` points, has `L` members with
  `L ∏_{i = 1}^{r} (T - k + i) ≤ ∏_{i = 1}^{r} (n - k + i)`.
-/
import PeriodDescent.Base

open Finset Polynomial
open scoped Classical

namespace PeriodDescent

/-! ### The induction on the dimension -/

section Abstract

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {α : Type*}

/-- The induction of note 04 Theorem 1.2. -/
theorem affine_bound (X : Finset α) (ev : α → V →ₗ[K] K) (w : α → Option K) (z : ℕ → ℕ) (A : ℕ)
    (W0 : Submodule K V)
    (hMDS : ∀ W : Submodule K V, W ≤ W0 → FiniteDimensional K W → 1 ≤ Module.finrank K W →
      (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card ≤ z (Module.finrank K W)) :
    ∀ (r : ℕ) (W : Submodule K V), W ≤ W0 → FiniteDimensional K W → Module.finrank K W = r →
      ∀ (c0 : V) (S : Finset V), (∀ h ∈ S, h - c0 ∈ W) →
        (∀ h ∈ S, A ≤ (X.filter (fun x => w x = some (ev x h))).card) →
        S.card * ∏ s ∈ Finset.Icc 1 r, (A - z s) ≤ ∏ s ∈ Finset.Icc 1 r, (X.card - z s) := by
  intro r
  induction r with
  | zero =>
    intro W _ hfin hr c0 S hS _
    have := hfin
    have hW : W = ⊥ := Submodule.finrank_eq_zero.mp hr
    have h1 : S.card ≤ 1 := Finset.card_le_one.mpr fun h hh h' hh' => by
      have e1 := hS h hh
      have e2 := hS h' hh'
      rw [hW, Submodule.mem_bot, sub_eq_zero] at e1 e2
      rw [e1, e2]
    simpa using h1
  | succ r ih =>
    intro W hW0 hfin hr c0 S hS hagr
    have := hfin
    rcases S.eq_empty_or_nonempty with hS0 | ⟨h0, hh0⟩
    · subst hS0
      simp
    have hAn : A ≤ X.card := (hagr h0 hh0).trans (Finset.card_filter_le _ _)
    -- the common zeros of the direction space
    have hZX : X.filter (fun x => ∀ u ∈ W, ev x u = 0) ⊆ X := Finset.filter_subset _ _
    have hz : (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card ≤ z (r + 1) := by
      have h1 := hMDS W hW0 hfin (by omega)
      rwa [hr] at h1
    have hcardXZ : (X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card
        = X.card - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card := by
      have := Finset.card_sdiff_add_card_eq_card hZX
      omega
    -- off the common zeros, the members through a point lie in an affine space of dimension `r`
    have hx : ∀ x ∈ X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0),
        (S.filter (fun h => w x = some (ev x h))).card * ∏ s ∈ Finset.Icc 1 r, (A - z s)
          ≤ ∏ s ∈ Finset.Icc 1 r, (X.card - z s) := by
      intro x hx
      rcases (S.filter (fun h => w x = some (ev x h))).eq_empty_or_nonempty with he | ⟨c', hc'⟩
      · rw [he]
        simp
      have hc'S := (Finset.mem_filter.mp hc').1
      have hc'v := (Finset.mem_filter.mp hc').2
      have hxZ : ¬ ∀ u ∈ W, ev x u = 0 := fun h =>
        (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1, h⟩)
      have hf : (ev x).domRestrict W ≠ 0 := by
        intro h0
        apply hxZ
        intro u hu
        have h1 := LinearMap.congr_fun h0 ⟨u, hu⟩
        exact h1
      have hker : Module.finrank K (LinearMap.ker ((ev x).domRestrict W)) = r := by
        have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hf
        omega
      refine ih ((LinearMap.ker ((ev x).domRestrict W)).map W.subtype)
        ((Submodule.map_subtype_le W _).trans hW0) inferInstance ?_ c' _ ?_ ?_
      · rw [Submodule.finrank_map_subtype_eq, hker]
      · intro h hh
        have hhS := (Finset.mem_filter.mp hh).1
        have hhv := (Finset.mem_filter.mp hh).2
        have hW' : h - c' ∈ W := by
          have e : h - c' = (h - c0) - (c' - c0) := by abel
          rw [e]
          exact W.sub_mem (hS h hhS) (hS c' hc'S)
        refine Submodule.mem_map.mpr ⟨⟨h - c', hW'⟩, ?_, rfl⟩
        rw [LinearMap.mem_ker]
        show ev x (h - c') = 0
        rw [map_sub, sub_eq_zero]
        exact Option.some.inj (hhv.symm.trans hc'v)
      · intro h hh
        exact hagr h (Finset.mem_filter.mp hh).1
    -- double counting
    have hdc : ∑ x ∈ X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0),
          (S.filter (fun h => w x = some (ev x h))).card
        = ∑ h ∈ S, ((X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0)).filter
            (fun x => w x = some (ev x h))).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have hmem : ∀ h ∈ S, A - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card
        ≤ ((X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0)).filter
            (fun x => w x = some (ev x h))).card := by
      intro h hh
      have hsub : X.filter (fun x => w x = some (ev x h))
          ⊆ (X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0)).filter (fun x => w x = some (ev x h))
            ∪ X.filter (fun x => ∀ u ∈ W, ev x u = 0) := by
        intro x hx
        by_cases hxz : x ∈ X.filter (fun x => ∀ u ∈ W, ev x u = 0)
        · exact Finset.mem_union_right _ hxz
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hx).1, hxz⟩, (Finset.mem_filter.mp hx).2⟩)
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h2 := hagr h hh
      omega
    have hcount : S.card * (A - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card)
        ≤ ∑ x ∈ X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0),
            (S.filter (fun h => w x = some (ev x h))).card := by
      rw [hdc]
      calc S.card * (A - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card)
          = ∑ _h ∈ S, (A - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hmem
    have hkey : S.card * (A - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card)
          * ∏ s ∈ Finset.Icc 1 r, (A - z s)
        ≤ (X.card - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card)
          * ∏ s ∈ Finset.Icc 1 r, (X.card - z s) := by
      calc S.card * (A - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card)
            * ∏ s ∈ Finset.Icc 1 r, (A - z s)
          ≤ (∑ x ∈ X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0),
              (S.filter (fun h => w x = some (ev x h))).card)
              * ∏ s ∈ Finset.Icc 1 r, (A - z s) := Nat.mul_le_mul_right _ hcount
        _ = ∑ x ∈ X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0),
              (S.filter (fun h => w x = some (ev x h))).card
              * ∏ s ∈ Finset.Icc 1 r, (A - z s) := Finset.sum_mul _ _ _
        _ ≤ ∑ _x ∈ X \ X.filter (fun x => ∀ u ∈ W, ev x u = 0),
              ∏ s ∈ Finset.Icc 1 r, (X.card - z s) := Finset.sum_le_sum hx
        _ = (X.card - (X.filter (fun x => ∀ u ∈ W, ev x u = 0)).card)
              * ∏ s ∈ Finset.Icc 1 r, (X.card - z s) := by
            rw [Finset.sum_const, smul_eq_mul, hcardXZ]
    have hfinal := step_arith S.card A X.card _ (z (r + 1)) _ _ hz hAn hkey
    rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega)]
    calc S.card * ((∏ s ∈ Finset.Icc 1 r, (A - z s)) * (A - z (r + 1)))
        = S.card * (A - z (r + 1)) * ∏ s ∈ Finset.Icc 1 r, (A - z s) := by ring
      _ ≤ (X.card - z (r + 1)) * ∏ s ∈ Finset.Icc 1 r, (X.card - z s) := hfinal
      _ = (∏ s ∈ Finset.Icc 1 r, (X.card - z s)) * (X.card - z (r + 1)) := by ring

end Abstract

/-! ### Polynomials: the MDS property -/

variable {F : Type*} [Field F]

/-- A subspace `W` of the polynomials of degree `< k` that vanishes on a set `Y` of at most `k`
points has dimension at most `k - |Y|`: evaluation at the points of `Y` is onto (Lagrange
interpolation) and `W` lies in its kernel. -/
theorem finrank_add_card_common_zeros_le (k : ℕ) (W : Submodule F F[X]) (hW : W ≤ degreeLT F k)
    (Y : Finset F) (hY : ∀ y ∈ Y, ∀ u ∈ W, u.eval y = 0) (hYk : Y.card ≤ k) :
    Module.finrank F W + Y.card ≤ k := by
  have : Module.Finite F (degreeLT F k) := Module.Finite.equiv (degreeLTEquiv F k).symm
  let E : (degreeLT F k) →ₗ[F] (Y → F) :=
    LinearMap.pi (fun y => (Polynomial.leval (y : F)).comp (degreeLT F k).subtype)
  have hinj : Set.InjOn (fun y : Y => (y : F)) ((Finset.univ : Finset Y) : Set Y) :=
    fun a _ b _ h => Subtype.ext h
  have hsurj : Function.Surjective E := by
    intro g
    refine ⟨⟨Lagrange.interpolate Finset.univ (fun y : Y => (y : F)) g, ?_⟩, ?_⟩
    · rw [mem_degreeLT]
      refine lt_of_lt_of_le (Lagrange.degree_interpolate_lt g hinj) ?_
      rw [Finset.card_univ, Fintype.card_coe]
      exact_mod_cast hYk
    · funext y
      show (Lagrange.interpolate Finset.univ (fun y : Y => (y : F)) g).eval (y : F) = g y
      exact Lagrange.eval_interpolate_at_node g hinj (Finset.mem_univ y)
  have h1 := LinearMap.finrank_range_add_finrank_ker E
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe, (degreeLTEquiv F k).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at h1
  have hle : Submodule.comap (degreeLT F k).subtype W ≤ LinearMap.ker E := by
    intro P hP
    rw [LinearMap.mem_ker]
    funext y
    exact hY y.1 y.2 P.1 hP
  have h2 := Submodule.finrank_mono hle
  have h3 := (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  omega

/-- The common zeros in `D`, through a map `ℓ` whose fibres on `D` have at most `m` points, of a
subspace of dimension `r ≥ 1` of the polynomials of degree `< k`: at most `m (k - r)`. -/
theorem card_common_zeros_le (D : Finset F) (ℓ : F[X]) (m k : ℕ)
    (hfib : ∀ y, (D.filter (fun x => ℓ.eval x = y)).card ≤ m) (W : Submodule F F[X])
    (hW : W ≤ degreeLT F k) (hr : 1 ≤ Module.finrank F W) :
    (D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).card ≤ m * (k - Module.finrank F W) := by
  have hY : ∀ y ∈ (D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).image (fun x => ℓ.eval x),
      ∀ u ∈ W, u.eval y = 0 := by
    intro y hy u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2 u hu
  have hYcard : ((D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).image
      (fun x => ℓ.eval x)).card + Module.finrank F W ≤ k := by
    rcases Nat.lt_or_ge k ((D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).image
        (fun x => ℓ.eval x)).card with hlt | hge
    · exfalso
      obtain ⟨Y', hY'Y, hY'c⟩ := Finset.exists_subset_card_eq hlt.le
      have h1 := finrank_add_card_common_zeros_le k W hW Y' (fun y hy => hY y (hY'Y hy)) hY'c.le
      omega
    · have h1 := finrank_add_card_common_zeros_le k W hW _ hY hge
      omega
  have h1 : (D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).card
      = ∑ y ∈ (D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).image (fun x => ℓ.eval x),
          ((D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).filter
            (fun x => ℓ.eval x = y)).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx =>
      Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hx))
  have h2 : ∀ y ∈ (D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).image (fun x => ℓ.eval x),
      ((D.filter (fun x => ∀ u ∈ W, u.eval (ℓ.eval x) = 0)).filter
        (fun x => ℓ.eval x = y)).card ≤ m := fun y _ =>
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (hfib y)
  rw [h1]
  refine (Finset.sum_le_card_nsmul _ _ _ h2).trans ?_
  rw [smul_eq_mul, mul_comm]
  exact Nat.mul_le_mul_left m (by omega)

/-- **Note 37 Lemma 3.2 for an affine space of members.** Let `W` be a subspace of dimension `r` of
the polynomials of degree `< k`, and `ℓ` a map whose fibres on `D` have at most `m` points. The
polynomials `P ∈ c₀ + W` with `#{x ∈ D : v(x) = P(ℓ(x))} ≥ A` number `L` with
`L ∏_{s = 1}^{r} (A - m (k - s)) ≤ ∏_{s = 1}^{r} (n - m (k - s))`. -/
theorem affine_poly_bound (D : Finset F) (ℓ : F[X]) (v : F → Option F) (m k A : ℕ)
    (hfib : ∀ y, (D.filter (fun x => ℓ.eval x = y)).card ≤ m) (W : Submodule F F[X])
    (hW : W ≤ degreeLT F k) (c0 : F[X]) (S : Finset F[X]) (hS : ∀ P ∈ S, P - c0 ∈ W)
    (hagr : ∀ P ∈ S, A ≤ polyAgr D ℓ v P) :
    S.card * ∏ s ∈ Finset.Icc 1 (Module.finrank F W), (A - m * (k - s))
      ≤ ∏ s ∈ Finset.Icc 1 (Module.finrank F W), (D.card - m * (k - s)) := by
  have : Module.Finite F (degreeLT F k) := Module.Finite.equiv (degreeLTEquiv F k).symm
  have hfin : FiniteDimensional F W := Submodule.finiteDimensional_of_le hW
  exact affine_bound D (fun x => Polynomial.leval (ℓ.eval x)) v (fun s => m * (k - s)) A W
    (fun W' hW' _ hr => card_common_zeros_le D ℓ m k hfib W' (hW'.trans hW) hr)
    (Module.finrank F W) W le_rfl hfin rfl c0 S hS hagr

/-- **Note 04 Theorem 1.2.** Let `W` be a subspace of dimension `r` of the polynomials of degree
`< k` and `D` a set of `n` points. The polynomials of the affine space `c₀ + W` that agree with a
word `w` on at least `T` points of `D` number `L` with
`L ∏_{i = 1}^{r} (T - (k - i)) ≤ ∏_{i = 1}^{r} (n - (k - i))`, that is
`L ≤ ∏_{i = 1}^{r} (n - k + i) / (T - k + i)` when `T ≥ k`. -/
theorem affine_ordinary_bound (D : Finset F) (w : F → F) (k T : ℕ) (W : Submodule F F[X])
    (hW : W ≤ degreeLT F k) (c0 : F[X]) (S : Finset F[X]) (hS : ∀ P ∈ S, P - c0 ∈ W)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    S.card * ∏ i ∈ Finset.Icc 1 (Module.finrank F W), (T - (k - i))
      ≤ ∏ i ∈ Finset.Icc 1 (Module.finrank F W), (D.card - (k - i)) := by
  have hfib : ∀ y, (D.filter (fun x => (X : F[X]).eval x = y)).card ≤ 1 := by
    intro y
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    rw [eval_X] at h1 h2
    rw [h1, h2]
  have hagr' : ∀ P ∈ S, T ≤ polyAgr D X (fun x => some (w x)) P := by
    intro P hP
    refine (hagr P hP).trans (Finset.card_le_card fun x hx => ?_)
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [eval_X, hx.2]
  have h := affine_poly_bound D X (fun x => some (w x)) 1 k T hfib W hW c0 S hS hagr'
  simpa using h

end PeriodDescent
