module

public import LeanVM.Protocol.Extraction.Fast.Extract
public import LeanVM.Protocol.Extraction.Fast.TaylorShift
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Roth–Ruckenstein without the fallback

`prefixesTruncD` (`Fast/Truncate.lean`) keeps the polynomial modulo `X^M` and falls back to the
exact recursion where the truncation does not determine a step: exactly where the truncated
polynomial is zero (its `s ≥ M` branch is dead), i.e. where `X^k` divides
`Q(X, p_d + X^d·Y)` along the path `p_d`. Repeated roots reach it: Lee–O'Sullivan's `(Y − f)^m`,
on an uncorrupted lane, strips `m` powers of `X` per level and falls back at depth `≈ k/m`.

At precision `W + 1` instead of `k` (`W` the weighted degree bound), it never does
(**`prefixesTruncD_eq_NF`**): the invariant `i + j·(f − 1) < M` (`NFInv`, a coefficient `X^i·Y^j`,
remaining fuel `f`, precision `M`) holds at the root (`i + j·(k − 1) ≤ W`) and is kept by a step
(the substitution `Y := a + X·Y` moves `X^i·Y^y` to `X^(i+t)·Y^t`, `t ≤ y`; the fuel drops by one),
and a nonzero polynomial under it has a coefficient below the precision; a child is nonzero, as its
coefficient `X^μ·Y^μ` is the `μ`-th Taylor coefficient of `Qn(0, Y)` at the root, `μ` the root's
multiplicity (`coeff_substituteFast_diag_ne_zero`). So `prefixesNF`, the truncated recursion with
no fallback code, computes the same prefixes, and the lane runner the extractor runs is
**`gsRunDistinctNF`**, `gsRunDistinct` at precision `W + 1` with `prefixesNF`
(**`gsRunDistinctNF_eq`**, on distinct points). Its costs are bounded in `Cost/Bounds/RothRuckenstein.lean`.

Credits: the algorithm, its `X`-adic order lemmas and the Guruswami–Sudan interpolation contract are
CompPoly's (github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly
Contributors"; `Bivariate/GuruswamiSudan/`, Valerii Huhnin), used, not copied.
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.GuruswamiSudan

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- **Distinct roots, counted with multiplicity, are at most the degree.** -/
theorem sum_rootMultiplicity_le (P : Polynomial F) (L : Finset F) :
    ∑ a ∈ L, P.rootMultiplicity a ≤ P.natDegree := by
  classical
  calc ∑ a ∈ L, P.rootMultiplicity a = ∑ a ∈ L, P.roots.count a := by
        simp [Polynomial.count_roots]
    _ ≤ ∑ a ∈ L ∪ P.roots.toFinset, P.roots.count a :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ a ∈ P.roots.toFinset, P.roots.count a := by
        refine (Finset.sum_subset Finset.subset_union_right fun a _ ha ↦ ?_).symm
        exact Multiset.count_eq_zero.2 fun h ↦ ha (Multiset.mem_toFinset.2 h)
    _ = Multiset.card P.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ P.natDegree := Polynomial.card_roots' P


omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem cbivariate_coeff_eq (Q : CBivariate F) (i j : ℕ) :
    CBivariate.coeff Q i j = (Q.val.coeff j).coeff i := rfl

theorem toPoly_initialCoefficientPolynomial_coeff (Q : CBivariate F) (j : ℕ) :
    (initialCoefficientPolynomial Q).toPoly.coeff j = CBivariate.coeff Q 0 j := by
  rw [← CPolynomial.coeff_toPoly, coeff_initialCoefficientPolynomial]


/-- The coefficient of `X^μ·Y^μ` in `Q(X, a + X·Y)` is the `μ`-th Taylor coefficient at `a` of
`P = Q(0, Y)`. -/
theorem substCoeff_diag_eq_taylor (Q : CBivariate F) (a : F) (μ : ℕ)
    (hμ : μ < Q.val.size) :
    substCoeff Q a μ μ = ((initialCoefficientPolynomial Q).toPoly.taylor a).coeff μ := by
  set P := (initialCoefficientPolynomial Q).toPoly
  rw [Polynomial.taylor_coeff]
  have hN : (Polynomial.hasseDeriv μ P).natDegree < Q.val.size - μ := by
    have : (Polynomial.hasseDeriv μ P).natDegree ≤ Q.val.size - μ - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [Polynomial.hasseDeriv_coeff, toPoly_initialCoefficientPolynomial_coeff,
        cbivar_coeff_eq_zero_of_y_size_le Q (by omega), mul_zero]
    omega
  rw [Polynomial.eval_eq_sum_range' hN, substCoeff]
  rw [← Finset.sum_range_add_sum_Ico _ hμ.le]
  rw [Finset.sum_eq_zero (s := Finset.range μ) fun y hy ↦ by
    have := Finset.mem_range.1 hy
    simp [show ¬ μ ≤ y by omega], zero_add, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.hasseDeriv_coeff, toPoly_initialCoefficientPolynomial_coeff,
    cbivariate_coeff_eq]
  simp only [Nat.le_add_right, le_refl, and_self, ↓reduceIte, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [Nat.add_comm i μ]
  ring

omit [DecidableEq F] in
/-- A nonzero coefficient `X^i` bounds the `X`-adic order. -/
theorem xAdicOrder?_le_of_coeff_ne_zero {S : CBivariate F} {i j : ℕ}
    (h : CBivariate.coeff S i j ≠ 0) : ∃ s, CBivariate.xAdicOrder? S = some s ∧ s ≤ i := by
  cases hS : CBivariate.xAdicOrder? S with
  | none =>
    exact absurd (by rw [cbivar_xAdicOrder?_none_eq_zero hS, CBivariate.coeff_zero]) h
  | some s =>
    refine ⟨s, rfl, ?_⟩
    by_contra hlt
    exact h (cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt hS (by omega))

/-- **The coefficient of `X^μ·Y^μ` in `Qn(X, a + X·Y)` is nonzero**, `μ` the multiplicity of `a`
in `P = Qn(0, Y) ≠ 0` (the `μ`-th Taylor coefficient of `P` at `a`). -/
theorem coeff_substituteFast_diag_ne_zero [CharP F 2] (Qn : CBivariate F) (a : F)
    (hP : initialCoefficientPolynomial Qn ≠ 0) :
    CBivariate.coeff (substituteFast Qn a)
      ((initialCoefficientPolynomial Qn).toPoly.rootMultiplicity a)
      ((initialCoefficientPolynomial Qn).toPoly.rootMultiplicity a) ≠ 0 := by
  set P := (initialCoefficientPolynomial Qn).toPoly
  set μ := P.rootMultiplicity a
  have hP' : P ≠ 0 := by
    intro h; apply hP; rw [← CPolynomial.toPoly_inj, CPolynomial.toPoly_zero]; exact h
  -- `deg P < |Qn|` and `μ ≤ deg P`
  have hdeg : P.natDegree < Qn.val.size := by
    by_contra hge
    have hlead : P.leadingCoeff = 0 := by
      rw [Polynomial.leadingCoeff, toPoly_initialCoefficientPolynomial_coeff,
        cbivar_coeff_eq_zero_of_y_size_le Qn (by omega)]
    exact hP' (Polynomial.leadingCoeff_eq_zero.1 hlead)
  have hμ : μ ≤ P.natDegree := by
    have := sum_rootMultiplicity_le P {a}
    simpa [μ] using this
  rw [coeff_substituteFast, substCoeff_diag_eq_taylor Qn a μ (by omega)]
  have ht : P.taylor a ≠ 0 := by rwa [Ne, Polynomial.taylor_eq_zero]
  have hμt : μ = (P.taylor a).natTrailingDegree := by
    rw [Polynomial.taylor_apply]; exact Polynomial.rootMultiplicity_eq_natTrailingDegree
  rw [hμt]
  exact mt Polynomial.trailingCoeff_eq_zero.1 ht


/-- **Roth–Ruckenstein's prefixes, truncated, without the fallback** (it returns nothing where
`prefixesTruncD` would fall back; it never does at precision `W + 1`, `prefixesTruncD_eq_NF`). The
substitution is the butterfly's (`substituteBF`, `Fast/TaylorShift.lean`), `substituteFast`
(`substituteBF_eq`). -/
@[expose] def prefixesNF (fieldRoots : FieldRootContext F) :
    ℕ → CBivariate F → ℕ → ℕ → CPolynomial F → Array (CPolynomial F)
  | 0, _q, _M, _depth, pref => #[pref]
  | fuel + 1, q, M, depth, pref =>
    match CBivariate.xAdicOrder? q with
    | some s =>
      if s < M then
        let Qn := divXPowerFast q s
        (rootsInFieldForNonzeroEquation fieldRoots (initialCoeffFast Qn)).foldl
          (fun out a ↦
            out ++ prefixesNF fieldRoots fuel
              (CBivariate.truncateX (substituteBF Qn a) (M - s)) (M - s) (depth + 1)
              (extendPrefix pref depth a))
          #[]
      else #[]
    | none => #[]

omit [DecidableEq F] in
theorem exists_coeff_ne_zero {S : CBivariate F} (h : S ≠ 0) :
    ∃ i j, CBivariate.coeff S i j ≠ 0 := by
  by_contra hall
  push Not at hall
  exact h (CBivariate.eq_iff_coeff.2 fun i j ↦ by rw [hall i j, CBivariate.coeff_zero])

/-- The invariant of the truncated recursion at precision `M`, remaining fuel `fuel`: every
nonzero coefficient `X^i·Y^j` has `i + j·(fuel − 1) < M`. -/
@[expose] def NFInv (fuel M : ℕ) (S : CBivariate F) : Prop :=
  ∀ i j, CBivariate.coeff S i j ≠ 0 → i + j * (fuel - 1) < M

omit [DecidableEq F] in
/-- A nonzero polynomial under the invariant has its order seen below the precision. -/
theorem xAdicOrder?_truncateX_of_nfInv {fuel M : ℕ} {S : CBivariate F} (hS : S ≠ 0)
    (hI : NFInv fuel M S) :
    ∃ s, CBivariate.xAdicOrder? (CBivariate.truncateX S M) = some s ∧ s < M ∧
      CBivariate.xAdicOrder? S = some s := by
  obtain ⟨i, j, hij⟩ := exists_coeff_ne_zero hS
  have hiM : i < M := by have := hI i j hij; omega
  have ht : CBivariate.coeff (CBivariate.truncateX S M) i j ≠ 0 := by
    rw [cbivar_coeff_truncateX]; simpa [hiM] using hij
  obtain ⟨s, hs, -⟩ := xAdicOrder?_le_of_coeff_ne_zero ht
  obtain ⟨hsM, hS'⟩ := xAdicOrder?_of_truncateX hs
  exact ⟨s, hs, hsM, hS'⟩

/-- **The child keeps the invariant, and is nonzero.** -/
theorem nfInv_child [CharP F 2] {fuel M s : ℕ} {S : CBivariate F}
    (hI : NFInv (fuel + 2) M S) (hs : CBivariate.xAdicOrder? S = some s) (a : F) :
    substituteFast (CBivariate.divXPower S s) a ≠ 0 ∧
      NFInv (fuel + 1) (M - s) (substituteFast (CBivariate.divXPower S s) a) := by
  refine ⟨?_, ?_⟩
  · -- `P = Qn(0, Y)` is row `X^s` of `S`, nonzero, so the diagonal coefficient is nonzero
    have hP : initialCoefficientPolynomial (CBivariate.divXPower S s) ≠ 0 := by
      obtain ⟨y, -, hy⟩ := cbivar_xAdicOrder?_some_exists hs
      intro h0
      apply hy
      have := congrArg (fun p ↦ CPolynomial.coeff p y) h0
      simp only [coeff_initialCoefficientPolynomial, cbivar_coeff_divXPower, Nat.zero_add,
        CPolynomial.coeff_zero] at this
      exact this
    intro h0
    apply coeff_substituteFast_diag_ne_zero _ a hP
    rw [h0, CBivariate.coeff_zero]
  · intro i j hij
    rw [coeff_substituteFast, substCoeff] at hij
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
    split at hy
    · rename_i hc
      have hne : CBivariate.coeff S (i - j + s) y ≠ 0 := by
        intro h0
        apply hy
        rw [← cbivariate_coeff_eq, cbivar_coeff_divXPower, h0]; ring
      have h1 := hI _ _ hne
      have h2 : j * fuel ≤ y * fuel := Nat.mul_le_mul_right fuel hc.1
      have h3 : y * (fuel + 2 - 1) = y * fuel + y := by
        rw [show fuel + 2 - 1 = fuel + 1 by omega]; ring
      rw [h3] at h1
      rw [show fuel + 1 - 1 = fuel by omega]
      omega
    · exact absurd rfl hy

/-- **Without the fallback, the same prefixes**: on a nonzero polynomial under the invariant,
`prefixesTruncD` never falls back and is `prefixesNF`. -/
theorem prefixesTruncD_eq_NF [CharP F 2] (fieldRoots : FieldRootContext F) (fuel : ℕ) :
    ∀ (S : CBivariate F) (M : ℕ) (Q₀ : CBivariate F) (path : List F) (depth : ℕ)
      (pref : CPolynomial F), S ≠ 0 → NFInv fuel M S →
      prefixesTruncD fieldRoots fuel (CBivariate.truncateX S M) M Q₀ path depth pref =
        prefixesNF fieldRoots fuel (CBivariate.truncateX S M) M depth pref := by
  induction fuel with
  | zero => intro S M Q₀ path depth pref _ _; rfl
  | succ fuel ih =>
    intro S M Q₀ path depth pref hS hI
    obtain ⟨s, hq, hsM, hS'⟩ := xAdicOrder?_truncateX_of_nfInv hS hI
    rw [prefixesTruncD, prefixesNF, hq]
    simp only [hsM, ↓reduceIte, substituteBF_eq]
    rw [divXPowerFast_eq, divXPower_truncateX]
    refine congrArg (fun f ↦ Array.foldl f #[] _) (funext fun out ↦ funext fun a ↦ ?_)
    rw [truncateX_substituteFast]
    congr 1
    cases fuel with
    | zero => rfl
    | succ fuel =>
      obtain ⟨hne, hI'⟩ := nfInv_child hI hS' a
      exact ih _ _ _ _ _ _ hne hI'

open LeanVM.Extraction LeanVM.Parameters in
/-- **At precision `W + 1`, on an interpolation polynomial, the truncated recursion is
`prefixesNF`.** -/
theorem prefixesNF_eq_truncD {points : Array (K × K)} {params : GSInterpParams} {Q : CBivariate K}
    (hv : ValidInterpolationWitness points params Q) :
    prefixesNF fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q (params.weightedDegreeBound + 1))
        (params.weightedDegreeBound + 1) 0 default =
      prefixesTruncD fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q params.messageDegree) params.messageDegree Q [] 0 default := by
  have hw := (CBivariate.natWeightedDegree_le_iff_coeff Q 1 (yWeight params) _).1 hv.2.1
  have hI : NFInv params.messageDegree (params.weightedDegreeBound + 1) Q := by
    intro i j hij
    have := hw i j hij
    simp only [yWeight] at this
    have e : j * (params.messageDegree - 1) = (params.messageDegree - 1) * j := Nat.mul_comm _ _
    omega
  rw [← prefixesTruncD_eq_NF fieldRootCtxFast _ Q _ Q [] 0 default hv.1 hI,
    prefixesTruncD_eq, prefixesTrunc_eq fieldRootCtxFast _ Q _ (fun _ ↦ replayPath Q []) 0 default rfl,
    prefixesTruncD_eq, prefixesTrunc_eq fieldRootCtxFast _ Q _ (fun _ ↦ replayPath Q []) 0 default rfl]

open LeanVM.Extraction LeanVM.Parameters in
/-- **`gsRunNoCheck` without the fallback**: Roth–Ruckenstein truncated at precision `W + 1`. -/
@[expose] def gsRunNF (I : GSInterpContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) : Array (CPolynomial K) :=
  match I.interpolate points params with
  | none => #[]
  | some Q =>
    (prefixesNF fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1)
        0 default).filter fun p ↦
      degreeLtBool p params.messageDegree && passesCandidateDistance points radius p

open LeanVM.Extraction LeanVM.Parameters in
/-- **The lane runner without the fallback**: `gsRunDistinct` with Roth–Ruckenstein truncated at
precision `W + 1` (`prefixesNF`, no fallback code). -/
@[expose] def gsRunDistinctNF (points : Array (K × K)) (params : GSInterpParams) (radius : ℕ) :
    Array (CPolynomial K) :=
  match interpolateDistinct points params with
  | none => #[]
  | some Q =>
    (prefixesNF fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1)
        0 default).filter fun p ↦
      degreeLtBool p params.messageDegree && passesDistanceFast points radius p

open LeanVM.Extraction LeanVM.Parameters in
/-- **`gsRunDistinctNF` is `gsRunDistinct`** on distinct points. -/
theorem gsRunDistinctNF_eq {points : Array (K × K)} (h : DistinctXCoordinates points)
    (params : GSInterpParams) (radius : ℕ) :
    gsRunDistinctNF points params radius = gsRunDistinct points params radius := by
  rw [gsRunDistinctNF, gsRunDistinct]
  cases hQ : interpolateDistinct points params with
  | none => rfl
  | some Q =>
    dsimp only
    rw [prefixesNF_eq_truncD
      (interpContextFast.sound points params Q (by rw [← interpolateDistinct_eq h]; exact hQ))]

open LeanVM.Extraction LeanVM.Parameters in
/-- The lane runner's points are distinct below `2^64` columns. -/
theorem distinct_lanePointsS (n : ℕ) (hn : n ≤ 2 ^ 64) (S : ℕ → ℕ → K) (u : ℕ) :
    DistinctXCoordinates (lanePointsS n S u) := by
  rw [DistinctXCoordinates, lanePointsS, Array.toList_ofFn, List.map_ofFn]
  exact List.nodup_ofFn.2 (LaneProofs.domainEmb n hn).injective

end

end LeanVM.Extraction.Fast
