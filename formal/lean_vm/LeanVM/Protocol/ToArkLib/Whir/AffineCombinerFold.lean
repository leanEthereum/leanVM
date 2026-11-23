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
* `ClaimHolds`, `map_fold`: the claim after a fold round, and the fold's linearity in the
  combiner; `card_quad_zero_le`: a nonzero quadratic in `(α, β)` vanishes at most at `2 |F|`
  pairs. `AffineCombinerFoldRel.lean` counts a round's escapes (`lem:fold-list`) from them.

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

end
end LeanVM.Protocol.Whir.AffineCombiner
