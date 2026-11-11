/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFold

  One affine fold round with the weight challenge `γ`: Annex B's `lem:fold-list`, from any bound
  on the exceptional pairs of the affine combiner.
  Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDefs

/-!
# An affine fold round

Annex B of the leanVM specification (branch `f128`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), `lem:fold-list`, after [CYWZ26, preprint],
Thm. 1.1 (Lemma 4.1). Fix an interleaved word with halves `f g : ρ → ι → F` (the lanes whose
folded bit is `0` and `1`), a degree `1 ≤ d`, a threshold `A` with `(A - 1)² > n d`, and
`L := jl n (A - 1) d`. The round's claim is `Λ₀ F + Λ₁ G = c` on pairs `(F, G)` of tuples, for
`F`-linear functionals `Λ₀ Λ₁` (the Annex's `⟨W₀, ·⟩` and `⟨W₁, ·⟩`; that coefficients of index
`2^κ` and above carry no weight is irrelevant here, only linearity is used).

* `foldW dom f g α β = g + (α + β x) f`, the affine fold (`def:affine-fold`).
* `card_foldBad_le`: if every pair of `lst(f, g; A - 1, d)` violates the claim, then for every
  table `u₀ v₀ c₀ v₁ c₁` and `u₁ := c - v₀`, at most `|F| · N + 2 L |F|²` challenges `(γ, α, β)`
  let some tuple of `lst(fold; A, d)` satisfy the new claim
  `(1 - γ) Λ₀ P + γ Λ₁ P = (1 - γ)(u₀ + α v₀ + β c₀) + γ (u₁ + α v₁ + β c₁)`, where `N` is the
  number of exceptional pairs of the combiner for the words `g` and `f`. Divided by `|F|³`, this
  is the Annex's `ε_aff + 2L/|E|` when `N ≤ |F|² ε_aff`.

Outside the exceptional pairs, a tuple `P` of the fold's list is `U + (α + β X) V` with
`deg U ≤ d`, `deg V ≤ d - 1`, `U = g` and `V = f` off at most one agreement point, so `(V, U)` is
in `lst(f, g; A - 1, d)` at the same degree `d`: no premix is needed to keep `U` below the degree.
Its discrepancy from the table is an affine form in `(α, β)` for each `γ`, zero for at most one
`γ` (else all six entries would be right and `v₀ + u₁ = Λ₀ V + Λ₁ U ≠ c`), and otherwise zero at
most `|F|` times.

The Annex writes `u₁ := c + v₀`, which is `c - v₀` in characteristic `2`; the form here is the one
valid in every characteristic. The weight `mle W (γ, ·)` of the Annex is `(1 - γ) W₀ + γ W₁`, so
its claim is the one above.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {F : Type*} [Field F] [Fintype F] {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

/-! ## Counting zeros of affine forms -/

section Affine

variable [DecidableEq F]

/-- A nonzero affine form `a + α b + β c` vanishes at no more than `|F|` pairs `(α, β)`. -/
theorem card_affine_zero_le (a b c : F) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    (univ.filter fun p : F × F ↦ a + p.1 * b + p.2 * c = 0).card ≤ Fintype.card F := by
  classical
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · have ha : a ≠ 0 := fun ha ↦ h ⟨ha, hb, hc⟩
      have : (univ.filter fun p : F × F ↦ a + p.1 * b + p.2 * c = 0) = ∅ :=
        filter_eq_empty_iff.mpr fun p _ h' ↦ ha (by simpa [hb, hc] using h')
      rw [this, card_empty]
      exact Nat.zero_le _
    · refine (card_le_card_of_injOn (fun p : F × F ↦ p.1) (fun _ _ ↦ mem_coe.mpr (mem_univ _))
        fun p hp p' hp' heq ↦ ?_).trans card_univ.le
      have h1 := (mem_filter.mp hp).2
      have h2 := (mem_filter.mp hp').2
      simp only at heq
      refine Prod.ext heq (mul_right_cancel₀ hc ?_)
      rw [heq] at h1
      linear_combination h1 - h2
  · refine (card_le_card_of_injOn (fun p : F × F ↦ p.2) (fun _ _ ↦ mem_coe.mpr (mem_univ _))
      fun p hp p' hp' heq ↦ ?_).trans card_univ.le
    have h1 := (mem_filter.mp hp).2
    have h2 := (mem_filter.mp hp').2
    simp only at heq
    refine Prod.ext (mul_right_cancel₀ hb ?_) heq
    rw [heq] at h1
    linear_combination h1 - h2

/-- **A pencil of affine forms.** If the affine forms `Δ₀ = a₀ + α b₀ + β c₀` and
`Δ₁ = a₁ + α b₁ + β c₁` are not both zero, then `(1 - γ) Δ₀ + γ Δ₁` vanishes at no more than
`2 |F|²` triples `(γ, α, β)`: it is the zero form for at most one `γ`, and otherwise vanishes at
no more than `|F|` pairs. -/
theorem card_pencil_le (a₀ b₀ c₀ a₁ b₁ c₁ : F)
    (h : ¬ (a₀ = 0 ∧ b₀ = 0 ∧ c₀ = 0 ∧ a₁ = 0 ∧ b₁ = 0 ∧ c₁ = 0)) :
    (univ.filter fun t : F × F × F ↦ (1 - t.1) * (a₀ + t.2.1 * b₀ + t.2.2 * c₀) +
      t.1 * (a₁ + t.2.1 * b₁ + t.2.2 * c₁) = 0).card ≤ 2 * Fintype.card F ^ 2 := by
  classical
  set q := Fintype.card F
  -- The form at `γ` is `va γ + α vb γ + β vc γ`.
  let va : F → F := fun γ ↦ a₀ + γ * (a₁ - a₀)
  let vb : F → F := fun γ ↦ b₀ + γ * (b₁ - b₀)
  let vc : F → F := fun γ ↦ c₀ + γ * (c₁ - c₀)
  let fib : F → Finset (F × F) := fun γ ↦ univ.filter fun p ↦ va γ + p.1 * vb γ + p.2 * vc γ = 0
  have hsub : (univ.filter fun t : F × F × F ↦ (1 - t.1) * (a₀ + t.2.1 * b₀ + t.2.2 * c₀) +
      t.1 * (a₁ + t.2.1 * b₁ + t.2.2 * c₁) = 0) ⊆
      univ.biUnion fun γ ↦ (fib γ).map ⟨fun p ↦ (γ, p), fun p p' h ↦ (Prod.mk.inj h).2⟩ := by
    intro t ht
    have ht := (mem_filter.mp ht).2
    refine mem_biUnion.mpr ⟨t.1, mem_univ _, mem_map.mpr ⟨t.2, mem_filter.mpr ⟨mem_univ _, ?_⟩,
      rfl⟩⟩
    simp only [va, vb, vc]
    linear_combination ht
  -- The forms that vanish identically: at most one `γ`.
  let Z : Finset F := univ.filter fun γ ↦ va γ = 0 ∧ vb γ = 0 ∧ vc γ = 0
  have hZ : Z.card ≤ 1 := by
    refine card_le_one.mpr fun γ hγ γ' hγ' ↦ ?_
    by_contra hne
    have hγ := (mem_filter.mp hγ).2
    have hγ' := (mem_filter.mp hγ').2
    have hsub' : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
    have e (x₀ x₁ : F) (h₀ : x₀ + γ * (x₁ - x₀) = 0) (h₁ : x₀ + γ' * (x₁ - x₀) = 0) :
        x₀ = 0 ∧ x₁ = 0 := by
      have hd : (γ - γ') * (x₁ - x₀) = 0 := by linear_combination h₀ - h₁
      have hx : x₁ - x₀ = 0 := (mul_eq_zero.mp hd).resolve_left hsub'
      have hx₀ : x₀ = 0 := by rw [hx, mul_zero, add_zero] at h₀; exact h₀
      exact ⟨hx₀, by linear_combination hx + hx₀⟩
    obtain ⟨ha₀, ha₁⟩ := e a₀ a₁ hγ.1 hγ'.1
    obtain ⟨hb₀, hb₁⟩ := e b₀ b₁ hγ.2.1 hγ'.2.1
    obtain ⟨hc₀, hc₁⟩ := e c₀ c₁ hγ.2.2 hγ'.2.2
    exact h ⟨ha₀, hb₀, hc₀, ha₁, hb₁, hc₁⟩
  have hfib (γ : F) : (fib γ).card ≤ q + if γ ∈ Z then q ^ 2 else 0 := by
    by_cases hγ : γ ∈ Z
    · simp only [hγ, ↓reduceIte]
      refine (card_le_univ _).trans ?_
      simp [Fintype.card_prod, q, sq]
    · simp only [hγ, ↓reduceIte, add_zero]
      exact card_affine_zero_le _ _ _ fun h' ↦ hγ (mem_filter.mpr ⟨mem_univ _, h'⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ γ, ((fib γ).map ⟨fun p ↦ (γ, p), fun p p' h ↦ (Prod.mk.inj h).2⟩).card :=
        card_biUnion_le
    _ = ∑ γ, (fib γ).card := by simp
    _ ≤ ∑ γ, (q + if γ ∈ Z then q ^ 2 else 0) := sum_le_sum fun γ _ ↦ hfib γ
    _ = q * q + Z.card * q ^ 2 := by
        rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, ← sum_filter, sum_const,
          smul_eq_mul, filter_mem_eq_inter, univ_inter]
    _ ≤ q * q + 1 * q ^ 2 := by gcongr
    _ = 2 * q ^ 2 := by ring

end Affine

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

/-- The claim after a fold round: `(1 - γ) Λ₀ P + γ Λ₁ P = Σ_ι eq(γ, ι) (u_ι + α v_ι + β c_ι)`. -/
def ClaimHolds (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (γ α β u₀ v₀ c₀ u₁ v₁ c₁ : F) (P : ρ → F[X]) :
    Prop :=
  (1 - γ) * Λ₀ P + γ * Λ₁ P = (1 - γ) * (u₀ + α * v₀ + β * c₀) + γ * (u₁ + α * v₁ + β * c₁)

open Classical in
/-- **The fold round's escapes**: the challenges `(γ, α, β)` after which some tuple of
`lst(fold; A, d)` satisfies the new claim, for the table `u₀ v₀ c₀ v₁ c₁` and the verifier's
`u₁ = c - v₀`. -/
noncomputable def foldBad (dom : ι ↪ F) (f g : ρ → ι → F) (A d : ℕ)
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c u₀ v₀ c₀ v₁ c₁ : F) : Finset (F × F × F) :=
  univ.filter fun t ↦ ∃ P ∈ tupleList dom (foldW dom f g t.2.1 t.2.2) A d,
    ClaimHolds Λ₀ Λ₁ t.1 t.2.1 t.2.2 u₀ v₀ c₀ (c - v₀) v₁ c₁ P

variable [DecidableEq F] (dom : ι ↪ F) (f g : ρ → ι → F) {A d : ℕ}

/-- **`lem:fold-list`**, counting form. Let every pair of `lst(f, g; A - 1, d)` violate the claim
`Λ₀ F + Λ₁ G = c`. For every table `u₀ v₀ c₀ v₁ c₁`, at most
`|F| · |excSet(g, f)| + 2 jl n (A - 1) d |F|²` challenges `(γ, α, β)` let a tuple of
`lst(fold; A, d)` satisfy the new claim. -/
theorem card_foldBad_le (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F)
    (hviol : ∀ p ∈ pairList dom f g (A - 1) d, Λ₀ p.1 + Λ₁ p.2 ≠ c) (u₀ v₀ c₀ v₁ c₁ : F) :
    (foldBad dom f g A d Λ₀ Λ₁ c u₀ v₀ c₀ v₁ c₁).card ≤
      Fintype.card F * (excSet dom g f d A).card +
        2 * jl (Fintype.card ι) (A - 1) d * Fintype.card F ^ 2 := by
  classical
  set u₁ := c - v₀ with hu₁
  set pairs := pairList dom f g (A - 1) d
  -- The fold of a pair, and its escapes.
  let B2 : (ρ → F[X]) × (ρ → F[X]) → Finset (F × F × F) := fun p ↦ univ.filter fun t ↦
    ClaimHolds Λ₀ Λ₁ t.1 t.2.1 t.2.2 u₀ v₀ c₀ u₁ v₁ c₁ fun r ↦ p.2 r + lin t.2.1 t.2.2 * p.1 r
  have hB2 : ∀ p ∈ pairs, (B2 p).card ≤ 2 * Fintype.card F ^ 2 := by
    intro p hp
    refine le_trans (card_le_card ?_) (card_pencil_le (Λ₀ p.2 - u₀) (Λ₀ p.1 - v₀)
      (Λ₀ (fun r ↦ X * p.1 r) - c₀) (Λ₁ p.2 - u₁) (Λ₁ p.1 - v₁)
      (Λ₁ (fun r ↦ X * p.1 r) - c₁) ?_)
    · intro t ht
      have ht := (mem_filter.mp ht).2
      simp only [ClaimHolds, map_fold] at ht
      exact mem_filter.mpr ⟨mem_univ _, by linear_combination ht⟩
    · rintro ⟨-, hb₀, -, ha₁, -, -⟩
      apply hviol p hp
      linear_combination hb₀ + ha₁ + hu₁
  have hsub : foldBad dom f g A d Λ₀ Λ₁ c u₀ v₀ c₀ v₁ c₁ ⊆
      (univ ×ˢ excSet dom g f d A) ∪ pairs.biUnion B2 := by
    intro t ht
    obtain ⟨P, hP, hclaim⟩ := (mem_filter.mp ht).2
    rw [mem_tupleList] at hP
    by_cases hE : IsExceptional dom g f d A t.2.1 t.2.2
    · exact mem_union_left _ (mem_product.mpr ⟨mem_univ _, (mem_excSet _ _ _ _ _ _).mpr hE⟩)
    obtain ⟨U, V, hU, hV, hPUV, hloss⟩ : ∃ U V, IsWitness dom g f d t.2.1 t.2.2 P U V := by
      by_contra hw
      exact hE ⟨P, hP.1, hP.2, hw⟩
    let p : (ρ → F[X]) × (ρ → F[X]) := (V, U)
    -- `(F, G) = (V, U)` agrees with `(f, g)` wherever the witness does.
    set S := agree dom P (comb dom g f t.2.1 t.2.2) with hS
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
    have hPeq : (fun r ↦ p.2 r + lin t.2.1 t.2.2 * p.1 r) = P := by
      funext r; exact (hPUV r).symm
    rw [hPeq]
    exact hclaim
  calc (foldBad dom f g A d Λ₀ Λ₁ c u₀ v₀ c₀ v₁ c₁).card
      ≤ (univ ×ˢ excSet dom g f d A).card + (pairs.biUnion B2).card :=
        (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ Fintype.card F * (excSet dom g f d A).card + pairs.card * (2 * Fintype.card F ^ 2) := by
        rw [card_product, card_univ]
        gcongr
        exact card_biUnion_le_card_mul _ _ _ hB2
    _ ≤ Fintype.card F * (excSet dom g f d A).card +
          jl (Fintype.card ι) (A - 1) d * (2 * Fintype.card F ^ 2) := by
        gcongr
        exact card_pairList_le_jl dom f g (A - 1) d hgap
    _ = _ := by ring

end
end LeanVM.Protocol.Whir.AffineCombiner
