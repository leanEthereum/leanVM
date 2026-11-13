/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerExcluded

  [CWYZ26], Lemma 4.3, the excluded pairs of one factor: at most `h (h - 1)` lines carry a
  common root of `R` and `∂_Z R`. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerReducedFactor

/-!
# The excluded pairs of one factor

`card_excludedLines_le`: for an irreducible `R ∈ L[X, Y, Z]` with `∂_Z R ≠ 0` and `h = yzDeg R`,
at most `h (h - 1)` pairs `(α, β) ∈ F²` have `e`-th roots `α'`, `β'` and a root `P(X^e)` of
`R(X, α' + β' X, Z)` at which `∂_Z R(X, α' + β' X, Z)` also vanishes. The resultant
`Res_Z(R, ∂_Z R) ∈ L[X][Y]` is nonzero, vanishes at `Y = α' + β' X` for each such pair, and has
`Y`-degree at most `(2b - 1) h - b² ≤ h (h - 1)`, `b = deg_Z R ≤ h`.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {L : Type*} [Field L]

/-- The `Z`-coefficients of the nested form sit below the `(Y, Z)`-degree. -/
theorem add_natDegree_coeff_le (R : MvPolynomial (Fin 3) L) (i : ℕ)
    (hi : (trivEquiv L R).coeff i ≠ 0) :
    i + ((trivEquiv L R).coeff i).natDegree ≤ yzDeg R := by
  set j := ((trivEquiv L R).coeff i).natDegree
  obtain ⟨k, hk⟩ : ∃ k, (((trivEquiv L R).coeff i).coeff j).coeff k ≠ 0 := by
    by_contra h; push Not at h
    exact (leadingCoeff_ne_zero.mpr hi) (Polynomial.ext h)
  have hmem : tri k j i ∈ R.support := by
    rw [MvPolynomial.mem_support_iff, ← coeff_trivEquiv]; simpa using hk
  have := le_yzDeg hmem
  simp only [tri_one, tri_two] at this
  omega

open Classical in
/-- **The excluded pairs of one factor** ([CWYZ26, Lemma 4.3]). -/
theorem card_excludedLines_le {F : Type*} [Field F] [Fintype F] [Algebra F L]
    (R : MvPolynomial (Fin 3) L) (hR : Irreducible R) (hd : MvPolynomial.pderiv 2 R ≠ 0)
    (e : ℕ) :
    (univ.filter fun ab : F × F ↦ ∃ (P : L[X]) (α' β' : L),
      α' ^ e = algebraMap F L ab.1 ∧ β' ^ e = algebraMap F L ab.2 ∧
      MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0 ∧
      MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)]
        (MvPolynomial.pderiv 2 R) = 0).card ≤ yzDeg R * (yzDeg R - 1) := by
  classical
  set Rt := trivEquiv L R with hRt
  set b := Rt.natDegree
  set h := yzDeg R
  have hirr : Irreducible Rt := (MulEquiv.irreducible_iff (trivEquiv L).toMulEquiv).mpr hR
  have hder : derivative Rt ≠ 0 := by
    rw [hRt, ← trivEquiv_pderiv]
    exact (map_ne_zero_iff _ (trivEquiv L).injective).mpr hd
  have hb : b ≠ 0 := fun h0 ↦ hder (derivative_of_natDegree_zero h0)
  have hRt0 : Rt ≠ 0 := fun h0 ↦ hder (by rw [h0, derivative_zero])
  have hbh : b ≤ h := by
    have := add_natDegree_coeff_le R b (leadingCoeff_ne_zero.mpr hRt0)
    omega
  have htri : ∀ i ≤ b, i + (Rt.coeff i).natDegree ≤ h := by
    intro i hi
    by_cases hc : Rt.coeff i = 0
    · rw [hc, natDegree_zero]; omega
    · exact add_natDegree_coeff_le R i hc
  set Res := resultant Rt (derivative Rt) b (b - 1)
  have hRes : Res ≠ 0 := resultant_derivative_ne_zero_of_irreducible Rt hirr hder
  have hResdeg : Res.natDegree ≤ h * (h - 1) := by
    refine (natDegree_resultant_derivative_padded_le_of_coeff_add_le Rt b h htri).trans ?_
    have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
    rw [Nat.sub_le_iff_le_add]
    zify [(by omega : 1 ≤ 2 * b), (by omega : 1 ≤ h)]
    nlinarith [sq_nonneg ((h : ℤ) - b)]
  -- Each excluded pair puts its line among the roots of `Res`.
  set S := univ.filter fun ab : F × F ↦ ∃ (P : L[X]) (α' β' : L),
    α' ^ e = algebraMap F L ab.1 ∧ β' ^ e = algebraMap F L ab.2 ∧
    MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0 ∧
    MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] (MvPolynomial.pderiv 2 R) = 0
  have hex : ∀ ab ∈ S, ∃ (P : L[X]) (α' β' : L),
      α' ^ e = algebraMap F L ab.1 ∧ β' ^ e = algebraMap F L ab.2 ∧
      MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0 ∧
      MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)]
        (MvPolynomial.pderiv 2 R) = 0 := fun ab hab ↦ (mem_filter.mp hab).2
  choose! P α' β' hα hβ h1 h2 using hex
  let line : F × F → L[X] := fun ab ↦ C (α' ab) + C (β' ab) * X
  have hroot : ∀ ab ∈ S, line ab ∈ Res.roots.toFinset := by
    intro ab hab
    rw [Multiset.mem_toFinset, mem_roots hRes, IsRoot.def, ← coe_evalRingHom]
    refine map_resultant_eq_zero_of_common_root (evalRingHom (line ab)) Rt (derivative Rt)
      le_rfl (natDegree_derivative_le Rt) (Or.inl hb) ((P ab).comp (X ^ e)) ?_ ?_
    · rw [← trivEval_X_eq, hRt, trivEval_trivEquiv]; exact h1 ab hab
    · rw [← trivEval_X_eq, hRt, ← trivEquiv_pderiv, trivEval_trivEquiv]; exact h2 ab hab
  have hinj : Set.InjOn line S := by
    intro ab hab ab' hab' heq
    have c0 := congrArg (coeff · 0) heq
    have c1 := congrArg (coeff · 1) heq
    simp only [line, coeff_add, coeff_C_mul, coeff_X_zero, coeff_X_one,
      mul_zero, add_zero, mul_one, coeff_C, one_ne_zero, ↓reduceIte, zero_add] at c0 c1
    refine Prod.ext ((algebraMap F L).injective ?_) ((algebraMap F L).injective ?_)
    · rw [← hα ab hab, ← hα ab' hab', c0]
    · rw [← hβ ab hab, ← hβ ab' hab', c1]
  calc S.card ≤ Res.roots.toFinset.card := card_le_card_of_injOn line hroot hinj
    _ ≤ Res.roots.card := Multiset.toFinset_card_le _
    _ ≤ Res.natDegree := card_roots' Res
    _ ≤ h * (h - 1) := hResdeg

end

end LeanVM.Protocol.Whir.AffineCombiner
