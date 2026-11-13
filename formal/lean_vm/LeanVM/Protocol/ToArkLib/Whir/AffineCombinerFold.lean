/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFold

  One affine fold round whose weight is folded at the combiner's own `α`: Annex B's
  `lem:fold-list`, from any bound on the exceptional pairs of the affine combiner.
  Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDefs

/-!
# An affine fold round

Annex B of the leanVM specification
(`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), `lem:fold-list`, after [CWYZ26],
Thm. 1.1 (Lemma 4.1). Fix an interleaved word with halves `f g : ρ → ι → F` (the lanes whose
folded bit is `0` and `1`), a degree `1 ≤ d`, a threshold `A` with `(A - 1)² > n d`, and
`L := jl n (A - 1) d`. The round's claim is `Λ₀ F + Λ₁ G = c` on pairs `(F, G)` of tuples, for
`F`-linear functionals `Λ₀ Λ₁` (the Annex's `⟨W₀, ·⟩` and `⟨W₁, ·⟩`; that coefficients of index
`2^κ` and above carry no weight is irrelevant here, only linearity is used).

* `foldW dom f g α β = g + (α + β x) f`, the affine fold (`def:affine-fold`).
* `card_foldBad_le`: if every pair of `lst(f, g; A - 1, d)` violates the claim, then for every
  table `u₀ v c₀ c₁` (the claimed `⟨W₀, G⟩`, `⟨W₁ − W₀, F⟩`, `⟨W₀, XF⟩`, `⟨W₁, XF⟩`), at most
  `N + 2 L |F|` challenges `(α, β)` let some tuple of `lst(fold; A, d)` satisfy the new claim
  `(1 - α) Λ₀ P + α Λ₁ P = u₀ + α (c - u₀) + α² v + β c₀ + α β (c₁ - c₀)`, where `N` is the
  number of exceptional pairs of the combiner for the words `g` and `f`. Divided by `|F|²`, this
  is the Annex's `ε_aff + 2L/|E|` when `N ≤ |F|² ε_aff`.

Outside the exceptional pairs, a tuple `P` of the fold's list is `U + (α + β X) V` with
`deg U ≤ d`, `deg V ≤ d - 1`, `U = g` and `V = f` off at most one agreement point, so `(V, U)` is
in `lst(f, g; A - 1, d)` at the same degree `d`. Its true value and the claimed one have the
same shape `a + α (c − a) + α² b + β d + α β e` (true: `a = Λ₀ U`, `c = Λ₀ V + Λ₁ U`,
`b = Λ₁ V − Λ₀ V`, `d = Λ₀ (X V)`, `e = Λ₁ (X V) − Λ₀ (X V)`), so their difference is a
polynomial of degree at most two in `(α, β)`; it is nonzero, for its constant coefficient would
force `a = u₀` and then its `α` coefficient `Λ₀ V + Λ₁ U = c`, which the pair violates. It
vanishes at most at `2 |F|` pairs (`card_quad_zero_le`). The two events are counted over the same
pairs; no independence of the weight's point from the combiner is needed.

In characteristic `2` the claim is the Annex's `u₀ + α (u₀ + c) + α² w + β c₀ + α β (c₀ + c₁)`,
`w = ⟨W₀ + W₁, F⟩`; the form here is the one valid in every characteristic. The weight
`mle W (α, ·)` of the Annex is `(1 - α) W₀ + α W₁`.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {F : Type*} [Field F] [Fintype F] {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

/-! ## Counting zeros of a quadratic in two variables -/

section Quadratic

variable [DecidableEq F]

/-- A nonzero quadratic `a₀ + α a₁ + α² a₂` has at most two roots. -/
theorem card_quad_roots_le (a₀ a₁ a₂ : F) (h : ¬ (a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0)) :
    (univ.filter fun α : F ↦ a₀ + α * a₁ + α ^ 2 * a₂ = 0).card ≤ 2 := by
  classical
  set p : F[X] := C a₀ + C a₁ * X + C a₂ * X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h0
    apply h
    have e := fun n ↦ congrArg (fun q : F[X] ↦ q.coeff n) h0
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    simp [hp, coeff_X, coeff_C, coeff_X_pow] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  have hdeg : p.natDegree ≤ 2 := by
    rw [hp]
    compute_degree!
  calc (univ.filter fun α : F ↦ a₀ + α * a₁ + α ^ 2 * a₂ = 0).card
      ≤ p.roots.toFinset.card := card_le_card fun α hα ↦ by
        rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot, hp]
        have := (mem_filter.mp hα).2
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
        linear_combination this
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ ≤ 2 := hdeg

/-- **A quadratic in two variables.** If `a₀ + α a₁ + α² a₂ + β (b₀ + α b₁)` is not the zero
polynomial, it vanishes at no more than `2 |F|` pairs `(α, β)`: for each `α` it is affine in `β`,
and either `b₀ + α b₁` vanishes for at most one `α`, or the coefficient of `β` is zero and the
quadratic in `α` has at most two roots. -/
theorem card_quad_zero_le (a₀ a₁ a₂ b₀ b₁ : F)
    (h : ¬ (a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ b₀ = 0 ∧ b₁ = 0)) :
    (univ.filter fun t : F × F ↦
      a₀ + t.1 * a₁ + t.1 ^ 2 * a₂ + t.2 * (b₀ + t.1 * b₁) = 0).card ≤
      2 * Fintype.card F := by
  classical
  set q := Fintype.card F
  let cα : F → F := fun α ↦ a₀ + α * a₁ + α ^ 2 * a₂
  let eα : F → F := fun α ↦ b₀ + α * b₁
  let fib : F → Finset F := fun α ↦ univ.filter fun β ↦ cα α + β * eα α = 0
  have hsub : (univ.filter fun t : F × F ↦
      a₀ + t.1 * a₁ + t.1 ^ 2 * a₂ + t.2 * (b₀ + t.1 * b₁) = 0) ⊆
      univ.biUnion fun α ↦ (fib α).map ⟨fun β ↦ (α, β), fun β β' h ↦ (Prod.mk.inj h).2⟩ := by
    intro t ht
    have ht := (mem_filter.mp ht).2
    exact mem_biUnion.mpr ⟨t.1, mem_univ _, mem_map.mpr ⟨t.2, mem_filter.mpr ⟨mem_univ _, ht⟩,
      rfl⟩⟩
  -- A fiber with a nonzero `β` coefficient has at most one point.
  have hone : ∀ α, eα α ≠ 0 → (fib α).card ≤ 1 := fun α he ↦ card_le_one.mpr fun β hβ β' hβ' ↦ by
    have h1 := (mem_filter.mp hβ).2
    have h2 := (mem_filter.mp hβ').2
    exact mul_right_cancel₀ he (by linear_combination h1 - h2)
  -- A fiber with a zero `β` coefficient is empty or everything.
  have hzero : ∀ α, eα α = 0 → (fib α).card ≤ if cα α = 0 then q else 0 := fun α he ↦ by
    split_ifs with hc
    · exact (card_le_univ _)
    · refine le_of_eq (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun β _ hβ ↦ hc ?_))
      simpa [he] using hβ
  have hsum : (univ.filter fun t : F × F ↦
      a₀ + t.1 * a₁ + t.1 ^ 2 * a₂ + t.2 * (b₀ + t.1 * b₁) = 0).card ≤ ∑ α, (fib α).card :=
    (card_le_card hsub).trans (card_biUnion_le.trans (by simp))
  by_cases hb : b₀ = 0 ∧ b₁ = 0
  · -- The `β` coefficient vanishes everywhere: the quadratic's roots, each a full fiber.
    have ha : ¬ (a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) := fun ha ↦ h ⟨ha.1, ha.2.1, ha.2.2, hb.1, hb.2⟩
    have he : ∀ α, eα α = 0 := fun α ↦ by simp [eα, hb.1, hb.2]
    calc _ ≤ ∑ α, (fib α).card := hsum
      _ ≤ ∑ α, (if cα α = 0 then q else 0) := sum_le_sum fun α _ ↦ hzero α (he α)
      _ = (univ.filter fun α ↦ cα α = 0).card * q := by rw [← sum_filter, sum_const, smul_eq_mul]
      _ ≤ 2 * q := Nat.mul_le_mul_right _ (card_quad_roots_le a₀ a₁ a₂ ha)
  · -- The `β` coefficient vanishes for at most one `α`; elsewhere a fiber has one point.
    have hZ : (univ.filter fun α ↦ eα α = 0).card ≤ 1 := card_le_one.mpr fun α hα α' hα' ↦ by
      by_contra hne
      have h1 := (mem_filter.mp hα).2
      have h2 := (mem_filter.mp hα').2
      have hd : (α - α') * b₁ = 0 := by simp only [eα] at h1 h2; linear_combination h1 - h2
      have hb₁ : b₁ = 0 := (mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hne)
      have hb₀ : b₀ = 0 := by simp only [eα, hb₁, mul_zero, add_zero] at h1; exact h1
      exact hb ⟨hb₀, hb₁⟩
    have hfib : ∀ α, (fib α).card ≤ 1 + if eα α = 0 then q else 0 := fun α ↦ by
      by_cases he : eα α = 0
      · simp only [he, ↓reduceIte]
        exact (card_le_univ _).trans (Nat.le_add_left _ _)
      · simp only [he, ↓reduceIte, add_zero]
        exact hone α he
    calc _ ≤ ∑ α, (fib α).card := hsum
      _ ≤ ∑ α, (1 + if eα α = 0 then q else 0) := sum_le_sum fun α _ ↦ hfib α
      _ = q + (univ.filter fun α ↦ eα α = 0).card * q := by
        rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, smul_eq_mul, smul_eq_mul,
          card_univ, mul_one]
      _ ≤ q + 1 * q := by gcongr
      _ = 2 * q := by ring

end Quadratic

/-! ## The fold -/

/-- **The affine fold** (Annex B, `def:affine-fold`): `g + (α + β x) f`, lane by lane. -/
def foldW (dom : ι ↪ F) (f g : ρ → ι → F) (α β : F) : ρ → ι → F :=
  comb dom g f α β

omit [Fintype F] [DecidableEq ι] [Fintype ρ] in
/-- The fold of a tuple is linear in the affine combiner: `Λ (G + (α + β X) H) =
Λ G + α Λ H + β Λ (X H)`. -/
theorem map_fold (Λ : (ρ → F[X]) →ₗ[F] F) (G H : ρ → F[X]) (α β : F) :
    Λ (fun r ↦ G r + lin α β * H r) = Λ G + α * Λ H + β * Λ (fun r ↦ X * H r) := by
  have : (fun r ↦ G r + lin α β * H r) = G + α • H + β • (fun r ↦ X * H r) := by
    funext r
    simp only [lin, Pi.add_apply, Pi.smul_apply, smul_eq_C_mul]
    ring
  rw [this, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The claim after a fold round, the weight folded at `α`:
`(1 - α) Λ₀ P + α Λ₁ P = Σ_ι eq(α, ι) (u_ι + α v_ι + β c_ι)`. -/
def ClaimHolds (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (α β c u₀ v c₀ c₁ : F) (P : ρ → F[X]) : Prop :=
  (1 - α) * Λ₀ P + α * Λ₁ P = u₀ + α * (c - u₀) + α ^ 2 * v + β * c₀ + α * β * (c₁ - c₀)

open Classical in
/-- **The fold round's escapes**: the challenges `(α, β)` after which some tuple of
`lst(fold; A, d)` satisfies the new claim, for the table `u₀ v c₀ c₁` and the running claim
`c`. -/
noncomputable def foldBad (dom : ι ↪ F) (f g : ρ → ι → F) (A d : ℕ)
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c u₀ v c₀ c₁ : F) : Finset (F × F) :=
  univ.filter fun t ↦ ∃ P ∈ tupleList dom (foldW dom f g t.1 t.2) A d,
    ClaimHolds Λ₀ Λ₁ t.1 t.2 c u₀ v c₀ c₁ P

variable [DecidableEq F] (dom : ι ↪ F) (f g : ρ → ι → F) {A d : ℕ}

/-- **`lem:fold-list`**, counting form. Let every pair of `lst(f, g; A - 1, d)` violate the claim
`Λ₀ F + Λ₁ G = c`. For every table `u₀ v c₀ c₁`, at most
`|excSet(g, f)| + 2 jl n (A - 1) d |F|` challenges `(α, β)` let a tuple of `lst(fold; A, d)`
satisfy the new claim. -/
theorem card_foldBad_le (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F)
    (hviol : ∀ p ∈ pairList dom f g (A - 1) d, Λ₀ p.1 + Λ₁ p.2 ≠ c) (u₀ v c₀ c₁ : F) :
    (foldBad dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁).card ≤
      (excSet dom g f d A).card + 2 * jl (Fintype.card ι) (A - 1) d * Fintype.card F := by
  classical
  set pairs := pairList dom f g (A - 1) d
  -- The fold of a pair, and its escapes.
  let B2 : (ρ → F[X]) × (ρ → F[X]) → Finset (F × F) := fun p ↦ univ.filter fun t ↦
    ClaimHolds Λ₀ Λ₁ t.1 t.2 c u₀ v c₀ c₁ fun r ↦ p.2 r + lin t.1 t.2 * p.1 r
  have hB2 : ∀ p ∈ pairs, (B2 p).card ≤ 2 * Fintype.card F := by
    intro p hp
    refine le_trans (card_le_card ?_) (card_quad_zero_le (Λ₀ p.2 - u₀)
      ((Λ₀ p.1 + Λ₁ p.2 - Λ₀ p.2) - (c - u₀)) ((Λ₁ p.1 - Λ₀ p.1) - v)
      (Λ₀ (fun r ↦ X * p.1 r) - c₀)
      ((Λ₁ (fun r ↦ X * p.1 r) - Λ₀ (fun r ↦ X * p.1 r)) - (c₁ - c₀)) ?_)
    · intro t ht
      have ht := (mem_filter.mp ht).2
      simp only [ClaimHolds, map_fold] at ht
      exact mem_filter.mpr ⟨mem_univ _, by linear_combination ht⟩
    · rintro ⟨ha₀, ha₁, -, -, -⟩
      apply hviol p hp
      linear_combination ha₁ + ha₀
  have hsub : foldBad dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ ⊆
      excSet dom g f d A ∪ pairs.biUnion B2 := by
    intro t ht
    obtain ⟨P, hP, hclaim⟩ := (mem_filter.mp ht).2
    rw [mem_tupleList] at hP
    by_cases hE : IsExceptional dom g f d A t.1 t.2
    · exact mem_union_left _ ((mem_excSet _ _ _ _ _ _).mpr hE)
    obtain ⟨U, V, hU, hV, hPUV, hloss⟩ : ∃ U V, IsWitness dom g f d t.1 t.2 P U V := by
      by_contra hw
      exact hE ⟨P, hP.1, hP.2, hw⟩
    let p : (ρ → F[X]) × (ρ → F[X]) := (V, U)
    -- `(F, G) = (V, U)` agrees with `(f, g)` wherever the witness does.
    set S := agree dom P (comb dom g f t.1 t.2) with hS
    have hagr : S.filter (fun x ↦ ¬ ∃ r, (U r).eval (dom x) ≠ g r x ∨
        (V r).eval (dom x) ≠ f r x) ⊆ agree dom p.1 f ∩ agree dom p.2 g := by
      intro x hx
      obtain ⟨-, hx⟩ := mem_filter.mp hx
      simp only [not_exists, not_or, not_not] at hx
      exact mem_inter.mpr ⟨(mem_agree _ _ _ _).mpr fun r ↦ (hx r).2,
        (mem_agree _ _ _ _).mpr fun r ↦ (hx r).1⟩
    have hcardS : A ≤ S.card := hP.2
    have hsplit := card_filter_add_card_filter_not (s := S) (fun x ↦ ∃ r,
      (U r).eval (dom x) ≠ g r x ∨ (V r).eval (dom x) ≠ f r x)
    have hloss' : (S.filter fun x ↦ ∃ r, (U r).eval (dom x) ≠ g r x ∨
        (V r).eval (dom x) ≠ f r x).card ≤ 1 := by
      convert hloss
    have hA1 : A - 1 ≤ (agree dom p.1 f ∩ agree dom p.2 g).card :=
      le_trans (by omega) (card_le_card hagr)
    have hp : p ∈ pairs :=
      (mem_pairList _ _ _ _ _ _).mpr ⟨fun r ↦ (hV r).trans (Nat.sub_le _ _), hU, hA1⟩
    refine mem_union_right _ (mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩)
    have hPeq : (fun r ↦ p.2 r + lin t.1 t.2 * p.1 r) = P := by
      funext r; exact (hPUV r).symm
    rw [hPeq]
    exact hclaim
  calc (foldBad dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁).card
      ≤ (excSet dom g f d A).card + (pairs.biUnion B2).card :=
        (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ (excSet dom g f d A).card + pairs.card * (2 * Fintype.card F) := by
        gcongr
        exact card_biUnion_le_card_mul _ _ _ hB2
    _ ≤ (excSet dom g f d A).card + jl (Fintype.card ι) (A - 1) d * (2 * Fintype.card F) := by
        gcongr
        exact card_pairList_le_jl dom f g (A - 1) d hgap
    _ = _ := by ring

end
end LeanVM.Protocol.Whir.AffineCombiner
