/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFoldRel

  The fold round's escape count relativised to a predicate on pairs of tuples, pulled back to the
  fold's tuples through the pairs near them.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFold
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerLemma43

/-!
# An affine fold round, relativised

`card_foldBad_le` (`lem:fold-list`) counts the challenges `(α, β)` after which some tuple of
`lst(fold; A, d)` satisfies the new claim, when every pair of `lst(f, g; A − 1, d)` violates the
old one. The agreement-set extractor's invariant only asks this of the pairs satisfying a
predicate `Bp` (those whose descent is bad), and of the fold's tuples all of whose near pairs
satisfy it:

* `NearPair dom f g d S p`: both halves of `p` have degree at most `d` and agree with `(f, g)` on
  all of `S` but at most one point, the agreement loss of `thm:mca-affine`.
* `foldBadR`: the challenges after which a tuple `P` of the fold's list, every near pair of whose
  agreement set satisfies `Bp`, satisfies the new claim.
* `card_foldBadR_le`: if every pair of `lst(f, g; A − 1, d)` satisfying `Bp` violates the old
  claim, at most `|excSet(g, f)| + 2 jl n (A − 1) d |F|` such challenges. Outside the exceptional
  pairs, `P`'s MCA witness is a near pair, so it satisfies `Bp`, and the count is
  `card_foldBad_le`'s over the pairs satisfying `Bp`.
* `card_foldBadR_le_nAff'`: with the unconditional MCA count, `nAff + 2 jl n (A − 1) d |F|`.

With `Bp` true this is `card_foldBad_le`.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {F : Type*} [Field F] [Fintype F] {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

open Classical in
/-- **A near pair**: `p = (F, G)` has both halves of degree at most `d`, and agrees with `(f, g)`
on all of `S` but at most one point. -/
def NearPair (dom : ι ↪ F) (f g : ρ → ι → F) (d : ℕ) (S : Finset ι)
    (p : (ρ → F[X]) × (ρ → F[X])) : Prop :=
  DegLE d p.1 ∧ DegLE d p.2 ∧
    (S.filter fun x ↦ ∃ r, (p.1 r).eval (dom x) ≠ f r x ∨ (p.2 r).eval (dom x) ≠ g r x).card ≤ 1

open Classical in
/-- **The fold round's relativised escapes**: the challenges `(α, β)` after which some tuple of
`lst(fold; A, d)`, every near pair of whose agreement set satisfies `Bp`, satisfies the new
claim. -/
noncomputable def foldBadR (dom : ι ↪ F) (f g : ρ → ι → F) (A d : ℕ)
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c u₀ v c₀ c₁ : F)
    (Bp : (ρ → F[X]) × (ρ → F[X]) → Prop) : Finset (F × F) :=
  univ.filter fun t ↦ ∃ P ∈ tupleList dom (foldW dom f g t.1 t.2) A d,
    (∀ p, NearPair dom f g d (agree dom P (foldW dom f g t.1 t.2)) p → Bp p) ∧
      ClaimHolds Λ₀ Λ₁ t.1 t.2 c u₀ v c₀ c₁ P

variable [DecidableEq F] (dom : ι ↪ F) (f g : ρ → ι → F) {A d : ℕ}

/-- **`lem:fold-list`, relativised.** Let every pair of `lst(f, g; A - 1, d)` satisfying `Bp`
violate the claim `Λ₀ F + Λ₁ G = c`. For every table `u₀ v c₀ c₁`, at most
`|excSet(g, f)| + 2 jl n (A - 1) d |F|` challenges `(α, β)` let a tuple of `lst(fold; A, d)`, all
of whose near pairs satisfy `Bp`, satisfy the new claim. -/
theorem card_foldBadR_le (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F) (Bp : (ρ → F[X]) × (ρ → F[X]) → Prop)
    (hviol : ∀ p ∈ pairList dom f g (A - 1) d, Bp p → Λ₀ p.1 + Λ₁ p.2 ≠ c) (u₀ v c₀ c₁ : F) :
    (foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp).card ≤
      (excSet dom g f d A).card + 2 * jl (Fintype.card ι) (A - 1) d * Fintype.card F := by
  classical
  set pairs := (pairList dom f g (A - 1) d).filter Bp
  let B2 : (ρ → F[X]) × (ρ → F[X]) → Finset (F × F) := fun p ↦ univ.filter fun t ↦
    ClaimHolds Λ₀ Λ₁ t.1 t.2 c u₀ v c₀ c₁ fun r ↦ p.2 r + lin t.1 t.2 * p.1 r
  have hB2 : ∀ p ∈ pairs, (B2 p).card ≤ 2 * Fintype.card F := by
    intro p hp
    obtain ⟨hp, hBp⟩ := mem_filter.mp hp
    refine le_trans (card_le_card ?_) (card_quad_zero_le (Λ₀ p.2 - u₀)
      ((Λ₀ p.1 + Λ₁ p.2 - Λ₀ p.2) - (c - u₀)) ((Λ₁ p.1 - Λ₀ p.1) - v)
      (Λ₀ (fun r ↦ X * p.1 r) - c₀)
      ((Λ₁ (fun r ↦ X * p.1 r) - Λ₀ (fun r ↦ X * p.1 r)) - (c₁ - c₀)) ?_)
    · intro t ht
      have ht := (mem_filter.mp ht).2
      simp only [ClaimHolds, map_fold] at ht
      exact mem_filter.mpr ⟨mem_univ _, by linear_combination ht⟩
    · rintro ⟨ha₀, ha₁, -, -, -⟩
      apply hviol p hp hBp
      linear_combination ha₁ + ha₀
  have hsub : foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp ⊆
      excSet dom g f d A ∪ pairs.biUnion B2 := by
    intro t ht
    obtain ⟨P, hP, hpull, hclaim⟩ := (mem_filter.mp ht).2
    rw [mem_tupleList] at hP
    by_cases hE : IsExceptional dom g f d A t.1 t.2
    · exact mem_union_left _ ((mem_excSet _ _ _ _ _ _).mpr hE)
    obtain ⟨U, V, hU, hV, hPUV, hloss⟩ : ∃ U V, IsWitness dom g f d t.1 t.2 P U V := by
      by_contra hw
      exact hE ⟨P, hP.1, hP.2, hw⟩
    let p : (ρ → F[X]) × (ρ → F[X]) := (V, U)
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
    have hdV : DegLE d V := fun r ↦ (hV r).trans (Nat.sub_le _ _)
    have hnear : NearPair dom f g d (agree dom P (foldW dom f g t.1 t.2)) p := by
      refine ⟨hdV, hU, le_trans (le_of_eq (congrArg Finset.card ?_)) hloss'⟩
      ext x
      simp only [mem_filter, hS, foldW]
      exact and_congr_right fun _ ↦ exists_congr fun r ↦ or_comm
    have hp : p ∈ pairs :=
      mem_filter.mpr ⟨(mem_pairList _ _ _ _ _ _).mpr ⟨hdV, hU, hA1⟩, hpull p hnear⟩
    refine mem_union_right _ (mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩)
    have hPeq : (fun r ↦ p.2 r + lin t.1 t.2 * p.1 r) = P := by
      funext r; exact (hPUV r).symm
    rw [hPeq]
    exact hclaim
  calc (foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp).card
      ≤ (excSet dom g f d A).card + (pairs.biUnion B2).card :=
        (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ (excSet dom g f d A).card + pairs.card * (2 * Fintype.card F) := by
        gcongr
        exact card_biUnion_le_card_mul _ _ _ hB2
    _ ≤ (excSet dom g f d A).card + jl (Fintype.card ι) (A - 1) d * (2 * Fintype.card F) := by
        gcongr
        exact (card_filter_le _ _).trans (card_pairList_le_jl dom f g (A - 1) d hgap)
    _ = _ := by ring

/-- **One affine fold round, relativised and unconditional**: at most
`nAff + 2 jl n (A - 1) d |F|` escapes. -/
theorem card_foldBadR_le_nAff' (p : ℕ) [Fact p.Prime] [CharP F p] {m D B : ℕ}
    (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (hadm : Admissible (Fintype.card ι) d A m D B)
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F) (Bp : (ρ → F[X]) × (ρ → F[X]) → Prop)
    (hviol : ∀ q ∈ pairList dom f g (A - 1) d, Bp q → Λ₀ q.1 + Λ₁ q.2 ≠ c) (u₀ v c₀ c₁ : F) :
    ((foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp).card : ℚ) ≤
      nAff (Fintype.card F) (Fintype.card ι) d A m D B +
        2 * jl (Fintype.card ι) (A - 1) d * (Fintype.card F : ℚ) := by
  have h := card_foldBadR_le dom f g hgap Λ₀ Λ₁ c Bp hviol u₀ v c₀ c₁
  have hmca := card_excSet_le_nAff' p dom hadm g f
  calc ((foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ Bp).card : ℚ)
      ≤ ((excSet dom g f d A).card : ℚ) +
          2 * jl (Fintype.card ι) (A - 1) d * (Fintype.card F : ℚ) := by exact_mod_cast h
    _ ≤ _ := by gcongr

end
end LeanVM.Protocol.Whir.AffineCombiner
