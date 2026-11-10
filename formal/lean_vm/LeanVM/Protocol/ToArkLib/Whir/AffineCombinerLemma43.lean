/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerLemma43

  [CYWZ26, preprint], Lemma 4.3 with (4.6) and (4.7): every interpolant over the algebraic closure
  of a finite field has an excluded factorization, so the affine MCA and fold-round bounds hold
  unconditionally. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerExcluded
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerReduction
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Lemma 4.3

`lemma43`: for a finite field `F` of characteristic `p`, every nonzero `Q ∈ F̄[X, Y, Z]` with
`deg_{Y,Z} Q ≤ D` and `deg_Z Q ≤ M` has an `ExcludedFactorization`. Factor `Q` into irreducibles;
the factors without `Z` multiply to `C`, and each factor with `Z` is replaced by its Frobenius
reduction (`exists_reducedFactor`). The `(Y, Z)`-degrees add up to at most `yzDeg Q ≤ D`
(`yzDeg_prod`, `yzDeg_le_of_dvd`), the Frobenius exponents are at most `deg_Z Q ≤ M`, `C` vanishes
on at most `deg_Y C` lines, and each reduced factor has at most `h (h - 1)` excluded lines
(`card_excludedLines_le`).

`card_excSet_le_nAff'` and `card_foldBad_le_nAff'`: the affine MCA count and the fold round's
escape count, with no hypothesis beyond admissibility.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

section L43

open Classical in
/-- The lines on which a nonzero `c(X, Y) ∈ L[X][Y]` vanishes: at most `deg_Y c`. -/
theorem card_lines_le {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L]
    {c : L[X][X]} (hc : c ≠ 0) :
    (univ.filter fun ab : F × F ↦
      c.eval (C (algebraMap F L ab.1) + C (algebraMap F L ab.2) * X) = 0).card ≤ c.natDegree := by
  classical
  let line : F × F → L[X] := fun ab ↦ C (algebraMap F L ab.1) + C (algebraMap F L ab.2) * X
  calc _ ≤ c.roots.toFinset.card := by
        refine card_le_card_of_injOn line (fun ab hab ↦ ?_) fun ab _ ab' _ heq ↦ ?_
        · rw [mem_coe, Multiset.mem_toFinset, mem_roots hc]
          exact (mem_filter.mp hab).2
        · have c0 := congrArg (coeff · 0) heq
          have c1 := congrArg (coeff · 1) heq
          simp only [line, coeff_add, coeff_C_mul, coeff_X_zero, coeff_X_one, mul_zero, add_zero,
            mul_one, coeff_C, one_ne_zero, ↓reduceIte, zero_add] at c0 c1
          exact Prod.ext ((algebraMap F L).injective c0) ((algebraMap F L).injective c1)
    _ ≤ c.roots.card := Multiset.toFinset_card_le _
    _ ≤ c.natDegree := card_roots' c

variable {F : Type*} [Field F] [Fintype F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]

/-- **[CYWZ26, Lemma 4.3]** over the algebraic closure of a finite field. -/
theorem lemma43 (D M : ℕ) : Lemma43 F p D M := by
  classical
  intro Q hQ hsupp
  set L := AlgebraicClosure F
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  -- Factors.
  set nf := UniqueFactorizationMonoid.factors Q
  set s := nf.toFinset
  have hirr : ∀ q ∈ s, Irreducible q := fun q hq ↦
    UniqueFactorizationMonoid.irreducible_of_factor q (Multiset.mem_toFinset.mp hq)
  have hne : ∀ q ∈ s, q ≠ 0 := fun q hq ↦ (hirr q hq).ne_zero
  have hassoc := UniqueFactorizationMonoid.factors_prod hQ
  have hsdvd : ∏ q ∈ s, q ∣ Q := by
    have h1 : ∏ q ∈ s, q ∣ nf.prod := by
      rw [prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.map_id']
      exact Multiset.prod_dvd_prod_of_le (Multiset.dedup_le nf)
    exact h1.trans hassoc.dvd
  set sZ := s.filter fun q ↦ MvPolynomial.degreeOf 2 q = 0
  set sP := s.filter fun q ↦ ¬ MvPolynomial.degreeOf 2 q = 0
  have hred : ∀ q ∈ sP, ∃ (R : MvPolynomial (Fin 3) L) (κ : ℕ), Irreducible R ∧
      MvPolynomial.pderiv 2 R ≠ 0 ∧ 1 ≤ yzDeg R ∧ yzDeg R ≤ yzDeg q ∧
      p ^ κ ≤ MvPolynomial.degreeOf 2 q ∧
      ∀ (α β : L) (P : L[X]), MvPolynomial.aeval ![X, C α + C β * X, P] q = 0 →
        ∀ α' β' : L, α' ^ p ^ κ = α → β' ^ p ^ κ = β →
          MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ p ^ κ)] R = 0 := by
    intro q hq
    obtain ⟨hqs, hq0⟩ := mem_filter.mp hq
    exact exists_reducedFactor q (hirr q hqs) (Nat.pos_of_ne_zero hq0)
  choose! Rf κf hRirr hRd hR1 hRle hκ hcov using hred
  set r := sP.card
  set eq := sP.equivFin
  -- The `Z`-free part.
  set Cf := ∏ q ∈ sZ, q
  have hCf0 : Cf ≠ 0 := prod_ne_zero_iff.mpr fun q hq ↦ hne q (mem_filter.mp hq).1
  have hCfZ : MvPolynomial.degreeOf 2 Cf = 0 := by
    refine Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_prod_le 2 _ _).trans ?_)
    exact (sum_eq_zero fun q hq ↦ (mem_filter.mp hq).2).le
  set c0 := (trivEquiv L Cf).coeff 0
  have hCt : trivEquiv L Cf = C c0 := by
    refine eq_C_of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr ?_)
    refine degree_le_of_natDegree_le (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_)
    ext j k
    have h := coeff_trivEquiv Cf (tri k j i)
    simp only [tri_zero, tri_one, tri_two] at h
    rw [h]
    simp only [coeff_zero]
    by_contra hc
    have := MvPolynomial.monomial_le_degreeOf 2 (MvPolynomial.mem_support_iff.mpr hc)
    simp only [tri_two] at this
    have : 0 < i := hi
    omega
  have hc0 : c0 ≠ 0 := fun h ↦ hCf0 ((trivEquiv L).injective (by rw [hCt, h, C_0, map_zero]))
  have hCeval (y z : L[X]) : MvPolynomial.aeval ![X, y, z] Cf = c0.eval y := by
    rw [← trivEval_trivEquiv, hCt, trivEval_X_eq]; simp
  set cpoly : MvPolynomial (Fin 2) L :=
    MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, 0] Cf
  have hcpoly (y : L[X]) : MvPolynomial.aeval ![X, y] cpoly = c0.eval y := by
    have : MvPolynomial.aeval ![X, y] cpoly = MvPolynomial.aeval ![X, y, 0] Cf := by
      have hf : (fun i ↦ MvPolynomial.aeval ![X, y]
          (![MvPolynomial.X 0, MvPolynomial.X 1, 0] i : MvPolynomial (Fin 2) L)) = ![X, y, 0] := by
        funext i; fin_cases i <;> simp
      rw [show cpoly = MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, 0] Cf from rfl,
        ← AlgHom.comp_apply, MvPolynomial.comp_aeval, hf]
    rw [this, hCeval]
  have hcY : c0.natDegree ≤ yzDeg Cf := by
    have := add_natDegree_coeff_le Cf 0 (by rw [hCt, coeff_C_zero]; exact hc0)
    simpa [c0] using this
  -- Degree bookkeeping.
  have hQD : yzDeg Q ≤ D := yzDeg_le_iff.mpr fun m hm ↦ (hsupp m hm).1
  have hQM : MvPolynomial.degreeOf 2 Q ≤ M := by
    rw [MvPolynomial.degreeOf_le_iff]; exact fun m hm ↦ (hsupp m hm).2
  have hdegZ : ∀ q ∈ s, MvPolynomial.degreeOf 2 q ≤ MvPolynomial.degreeOf 2 Q := by
    intro q hq
    obtain ⟨c, hc⟩ := (dvd_prod_of_mem (fun q ↦ q) hq).trans hsdvd
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hQ hc
    rw [hc, MvPolynomial.degreeOf_mul_eq (hne q hq) hc0]
    omega
  have hsum : yzDeg Cf + ∑ q ∈ sP, yzDeg q ≤ D := by
    rw [yzDeg_prod _ _ fun q hq ↦ hne q (mem_filter.mp hq).1, sum_filter_add_sum_filter_not,
      ← yzDeg_prod _ _ hne]
    exact (yzDeg_le_of_dvd hsdvd hQ).trans hQD
  refine ⟨{
    r := r
    R := fun i ↦ Rf (eq.symm i)
    κ := fun i ↦ κf (eq.symm i)
    h := fun i ↦ yzDeg (Rf (eq.symm i))
    cpoly := cpoly
    cY := c0.natDegree
    deg_R := fun i m hm ↦ le_yzDeg hm
    one_le_h := fun i ↦ hR1 _ (eq.symm i).2
    e_le := fun i ↦ ((hκ _ (eq.symm i).2).trans (hdegZ _ (mem_filter.mp (eq.symm i).2).1)).trans
      hQM
    deg_sum := ?_
    cover := ?_
    card_line := ?_
    card_excluded := fun i ↦ card_excludedLines_le _ (hRirr _ (eq.symm i).2)
      (hRd _ (eq.symm i).2) _ }⟩
  · calc c0.natDegree + ∑ i, yzDeg (Rf (eq.symm i))
        ≤ yzDeg Cf + ∑ q ∈ sP, yzDeg q := by
          refine add_le_add hcY ?_
          rw [Equiv.sum_comp eq.symm (fun x ↦ yzDeg (Rf x)), ← sum_coe_sort sP]
          exact sum_le_sum fun x _ ↦ hRle _ x.2
      _ ≤ D := hsum
  · intro α β P hQP
    -- Some factor vanishes along the line.
    obtain ⟨u, hu⟩ := hassoc
    have hprod : MvPolynomial.aeval ![X, C α + C β * X, P] nf.prod = 0 := by
      have := congrArg (MvPolynomial.aeval ![X, C α + C β * X, P]) hu
      rw [map_mul, hQP] at this
      exact (mul_eq_zero.mp this).resolve_right (u.isUnit.map _).ne_zero
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
    obtain ⟨q, hqnf, hq0⟩ := hprod
    have hqs : q ∈ s := Multiset.mem_toFinset.mpr hqnf
    by_cases hZq : MvPolynomial.degreeOf 2 q = 0
    · left
      rw [hcpoly, ← hCeval _ P, map_prod]
      exact prod_eq_zero (mem_filter.mpr ⟨hqs, hZq⟩) hq0
    · right
      have hqP : q ∈ sP := mem_filter.mpr ⟨hqs, hZq⟩
      refine ⟨eq ⟨q, hqP⟩, (iterateFrobeniusEquiv L p (κf q)).symm α,
        (iterateFrobeniusEquiv L p (κf q)).symm β, ?_, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]
        exact (iterateFrobeniusEquiv L p (κf q)).apply_symm_apply α
      · simp only [Equiv.symm_apply_apply]
        exact (iterateFrobeniusEquiv L p (κf q)).apply_symm_apply β
      · simp only [Equiv.symm_apply_apply]
        exact hcov q hqP α β P hq0 _ _ ((iterateFrobeniusEquiv L p (κf q)).apply_symm_apply α)
          ((iterateFrobeniusEquiv L p (κf q)).apply_symm_apply β)
  · simp only [hcpoly]
    exact card_lines_le hc0

end L43

section Final

variable {F : Type*} [Field F] [Fintype F] {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

/-- **Affine MCA, counting form, unconditional** (Annex B, `thm:mca-affine`). -/
theorem card_excSet_le_nAff' (p : ℕ) [Fact p.Prime] [CharP F p] (dom : ι ↪ F) {d A m D B : ℕ}
    (hadm : Admissible (Fintype.card ι) d A m D B) (f g : ρ → ι → F) :
    ((excSet dom f g d A).card : ℚ) ≤ nAff (Fintype.card F) (Fintype.card ι) d A m D B :=
  card_excSet_le_nAff_of_lemma43 dom hadm (lemma43 (p := p) D _) f g

/-- **One affine fold round, unconditional** (Annex B, `lem:fold-list` (ii), counting form). -/
theorem card_foldBad_le_nAff' [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p] (dom : ι ↪ F) (f g : ρ → ι → F) {d A m D B : ℕ}
    (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (hadm : Admissible (Fintype.card ι) d A m D B)
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F)
    (hviol : ∀ q ∈ pairList dom f g (A - 1) (d - 1), Λ₀ q.1 + Λ₁ q.2 ≠ c)
    (θ : F) (hθ : IsGood dom f g A d θ) (u₀ v₀ c₀ v₁ c₁ : F) :
    ((foldBad dom f g A d Λ₀ Λ₁ c θ u₀ v₀ c₀ v₁ c₁).card : ℚ) ≤
      Fintype.card F * nAff (Fintype.card F) (Fintype.card ι) d A m D B +
        2 * jl (Fintype.card ι) (A - 1) d * (Fintype.card F : ℚ) ^ 2 :=
  card_foldBad_le_nAff_of_lemma43 dom f g hgap hadm (lemma43 (p := p) D _) Λ₀ Λ₁ c hviol θ hθ
    u₀ v₀ c₀ v₁ c₁

end Final

end

end LeanVM.Protocol.Whir.AffineCombiner
