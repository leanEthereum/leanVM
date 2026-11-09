/-
  LeanVM.Protocol.ToArkLib.GrandProductPoly

  The grand-product polynomial of a multiset of tuples under the linear fingerprint: it
  determines the multiset, padding leaves `1 − π_A(d)` or not, and two different multisets give
  equal values at few points of a finite field. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToCompPoly.Fingerprint
public import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Roots

/-!
# Grand products of linear fingerprints

A tuple has `m` slots, and its fingerprint is the linear form `π_A(t) = Σ_i A_i t_i`
(`fingerprintPoly`, `LeanVM.Protocol.ToCompPoly.Fingerprint`). The grand product of a multiset
`M` of tuples is `grandProductPoly M = Π_{t ∈ M} (X − π_A(t))`, a polynomial in the `m` weights
and one more variable, `X`, indexed by `none`. A padding leaf is `1 − π_A(d)` for a tuple `d`
(`padLeafPoly`): what a padding row's leaf becomes when the row holds the tuple `p + d`, `p` the
public padding row's (`doc/leanvm/body/08-end-to-end-protocol.tex`, Proposition `prop:pad`).

* Over an integral domain the polynomial determines the multiset, multiplicities included
  (`grandProductPoly_injective`): read as a polynomial in `X` over the weights, it is monic and
  its roots are the fingerprints, and fingerprints determine their tuples. No bound relates the
  characteristic to the multiset's size.
* A padded product, padding leaves times a grand product, determines the grand product's
  multiset whatever the padding (`paddedProductPoly_eq`): the leaves `1 − π_A(d)` involve no `X`
  and have constant coefficient `1`, so their product is a nonzero constant in `X`.
* Every factor has total degree at most one, so two different multisets of at most `cap` leaves
  differ by a nonzero polynomial of degree at most `cap`, which vanishes at no more than
  `cap · |F|^m` of the `|F|^(m+1)` points over a finite field `F`
  (`card_grandProduct_collision_le`, `card_paddedProduct_collision_le`, by ArkLib's counting
  Schwartz-Zippel). The multisets are fixed before the point.

The product argument uses Mathlib's `Polynomial.roots_multiset_prod_X_sub_C`. Requested upstream,
for the multilinear fingerprint it replaces, as
[ArkLib #901](https://github.com/Verified-zkEVM/ArkLib/issues/901).
-/

namespace LeanVM.Protocol

@[expose] public section

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The product in a separate univariate challenge over the fingerprint coefficient ring. -/
noncomputable def grandProductUnivariate (M : Multiset (Vector R m)) :
    Polynomial (MvPolynomial (Fin m) R) :=
  (M.map fun t ↦ Polynomial.X - Polynomial.C (fingerprintPoly t)).prod

/-- The same grand product with the product and fingerprint challenges as separate variables. -/
noncomputable def grandProductPoly (M : Multiset (Vector R m)) :
    MvPolynomial (Option (Fin m)) R :=
  (M.map fingerprintFactorPoly).prod

/-- A padding leaf, `1 − π_A(d)`, in the weights of the joint variables: it involves no `X`. -/
noncomputable def padLeafPoly (d : Vector R m) : MvPolynomial (Option (Fin m)) R :=
  1 - MvPolynomial.rename some (fingerprintPoly d)

/-- The product of the padding leaves of a multiset of tuples. -/
noncomputable def padProductPoly (D : Multiset (Vector R m)) : MvPolynomial (Option (Fin m)) R :=
  (D.map padLeafPoly).prod

/-- A grand product times padding leaves: a bus side whose padding rows differ from the public
padding row by the tuples of `D` (`doc/leanvm`, Proposition `prop:pad`). -/
noncomputable def paddedProductPoly (D M : Multiset (Vector R m)) :
    MvPolynomial (Option (Fin m)) R :=
  padProductPoly D * grandProductPoly M

/-- Renaming by `some` lands in the constant coefficients of the polynomial in the variable
`none`. -/
private theorem optionEquivLeft_rename_some {R σ : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    MvPolynomial.optionEquivLeft R σ (MvPolynomial.rename some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The joint-variable and univariate representations agree through the standard equivalence. -/
theorem optionEquivLeft_grandProductPoly (M : Multiset (Vector R m)) :
    MvPolynomial.optionEquivLeft R (Fin m) (grandProductPoly M) = grandProductUnivariate M := by
  simp [grandProductPoly, grandProductUnivariate, map_multiset_prod, Multiset.map_map,
    Function.comp_def, fingerprintFactorPoly, optionEquivLeft_rename_some]

/-- Evaluation of the symbolic grand product is the actual product of fingerprint factors. -/
theorem eval₂_grandProductPoly {S : Type*} [CommRing S] (M : Multiset (Vector R m))
    (φ : R →+* S) (α : Fin m → S) (β : S) :
    MvPolynomial.eval₂ φ (fun i ↦ i.elim β α) (grandProductPoly M) =
      (M.map fun t ↦ β - ∑ i : Fin m, α i * φ t[i]).prod := by
  change MvPolynomial.eval₂Hom φ (fun i ↦ i.elim β α) (grandProductPoly M) = _
  simp only [grandProductPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    MvPolynomial.coe_eval₂Hom, eval₂_fingerprintFactorPoly]

/-- Evaluation of the padding leaves is the product of `1 − π_α(d)`. -/
theorem eval₂_padProductPoly {S : Type*} [CommRing S] (D : Multiset (Vector R m))
    (φ : R →+* S) (α : Fin m → S) (β : S) :
    MvPolynomial.eval₂ φ (fun i ↦ i.elim β α) (padProductPoly D) =
      (D.map fun d ↦ (1 : S) - ∑ i : Fin m, α i * φ d[i]).prod := by
  change MvPolynomial.eval₂Hom φ (fun i ↦ i.elim β α) (padProductPoly D) = _
  simp only [padProductPoly, padLeafPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one,
    MvPolynomial.eval₂_rename]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun d _ ↦ by
    rw [show (fun x : Fin m ↦ (some x).elim β α) = α from rfl, eval₂_fingerprintPoly])

/-- Grand products commute with coefficient maps, including noninjective maps. -/
theorem map_grandProductPoly {S : Type*} [CommRing S] (φ : R →+* S) (M : Multiset (Vector R m)) :
    MvPolynomial.map φ (grandProductPoly M) = grandProductPoly (M.map (Vector.map φ)) := by
  simp [grandProductPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    fingerprintFactorPoly, MvPolynomial.map_rename, map_fingerprintPoly]

/-- Padding leaves commute with coefficient maps. -/
theorem map_padProductPoly {S : Type*} [CommRing S] (φ : R →+* S) (D : Multiset (Vector R m)) :
    MvPolynomial.map φ (padProductPoly D) = padProductPoly (D.map (Vector.map φ)) := by
  simp [padProductPoly, padLeafPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    MvPolynomial.map_rename, map_fingerprintPoly]

/-- An injective coefficient embedding preserves the complete multiset of tuples. -/
theorem map_tupleMultiset_injective {S : Type*} [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) :
    Function.Injective (Multiset.map (Vector.map (n := m) φ)) :=
  Multiset.map_injective fun _ _ h ↦ (Vector.map_inj_right fun _ _ h ↦ hφ h).mp h

/-- Every tuple contributes at most one to the joint total degree. -/
theorem totalDegree_grandProductPoly (M : Multiset (Vector R m)) :
    (grandProductPoly M).totalDegree ≤ M.card := by
  refine (MvPolynomial.totalDegree_multiset_prod _).trans ?_
  simpa using Multiset.sum_le_card_nsmul (M.map fun t ↦ (fingerprintFactorPoly t).totalDegree) 1
    (by simpa using fun t (_ : t ∈ M) ↦ totalDegree_fingerprintFactorPoly t)

/-- Every padding leaf contributes at most one to the joint total degree. -/
theorem totalDegree_padProductPoly (D : Multiset (Vector R m)) :
    (padProductPoly D).totalDegree ≤ D.card := by
  refine (MvPolynomial.totalDegree_multiset_prod _).trans ?_
  have hleaf : ∀ d : Vector R m, (padLeafPoly d).totalDegree ≤ 1 := fun d ↦
    (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp)
      ((MvPolynomial.totalDegree_rename_le _ _).trans (totalDegree_fingerprintPoly d)))
  simpa using Multiset.sum_le_card_nsmul (D.map fun d ↦ (padLeafPoly d).totalDegree) 1
    (by simpa using fun d (_ : d ∈ D) ↦ hleaf d)

/-- A padded product has total degree at most one per leaf, padding or not. -/
theorem totalDegree_paddedProductPoly (D M : Multiset (Vector R m)) :
    (paddedProductPoly D M).totalDegree ≤ D.card + M.card :=
  (MvPolynomial.totalDegree_mul _ _).trans
    (Nat.add_le_add (totalDegree_padProductPoly D) (totalDegree_grandProductPoly M))

section Domain

variable [IsDomain R]

/-- The roots are exactly the fingerprints, with their natural multiplicities. -/
theorem roots_grandProductUnivariate (M : Multiset (Vector R m)) :
    (grandProductUnivariate M).roots = M.map fingerprintPoly := by
  have h := Polynomial.roots_multiset_prod_X_sub_C (M.map fingerprintPoly)
  simpa only [Multiset.map_map, Function.comp_def, grandProductUnivariate] using h

/-- Symbolic grand products determine tuple multisets in every characteristic. -/
theorem grandProductPoly_injective :
    Function.Injective (grandProductPoly (R := R) (m := m)) := by
  intro M N h
  have hu := congrArg (MvPolynomial.optionEquivLeft R (Fin m)) h
  rw [optionEquivLeft_grandProductPoly, optionEquivLeft_grandProductPoly] at hu
  have hr := congrArg Polynomial.roots hu
  rw [roots_grandProductUnivariate, roots_grandProductUnivariate] at hr
  exact Multiset.map_injective fingerprintPoly_injective hr

/-- Distinct multisets yield a nonzero difference polynomial without a cardinality premise. -/
theorem grandProduct_difference_ne_zero {M N : Multiset (Vector R m)} (h : M ≠ N) :
    grandProductPoly M - grandProductPoly N ≠ 0 :=
  fun hz ↦ h (grandProductPoly_injective (sub_eq_zero.mp hz))

/-- The padding leaves are a nonzero constant in `X`: each has constant coefficient `1`. -/
private theorem optionEquivLeft_padProductPoly (D : Multiset (Vector R m)) :
    MvPolynomial.optionEquivLeft R (Fin m) (padProductPoly D) =
        Polynomial.C (D.map fun d ↦ 1 - fingerprintPoly d).prod ∧
      (D.map fun d ↦ 1 - fingerprintPoly d).prod ≠ 0 := by
  refine ⟨?_, Multiset.prod_ne_zero fun h0 ↦ ?_⟩
  · simp [padProductPoly, padLeafPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
      optionEquivLeft_rename_some]
  · obtain ⟨d, -, h0⟩ := Multiset.mem_map.mp h0
    have := congrArg MvPolynomial.constantCoeff h0
    rw [map_sub, map_one, constantCoeff_fingerprintPoly, sub_zero, map_zero] at this
    exact one_ne_zero this

/-- **Padded grand products determine their tuples** (`doc/leanvm`, Proposition `prop:pad`): equal
padded products have equal multisets of tuples, whatever the padding. As a polynomial in `X`, a
padded product is a nonzero constant times the grand product, so it has the same roots. -/
theorem paddedProductPoly_eq {D D' M N : Multiset (Vector R m)}
    (h : paddedProductPoly D M = paddedProductPoly D' N) : M = N := by
  have hu := congrArg (MvPolynomial.optionEquivLeft R (Fin m)) h
  simp only [paddedProductPoly, map_mul, (optionEquivLeft_padProductPoly D).1,
    (optionEquivLeft_padProductPoly D').1, optionEquivLeft_grandProductPoly] at hu
  have hr := congrArg Polynomial.roots hu
  rw [Polynomial.roots_C_mul _ (optionEquivLeft_padProductPoly D).2,
    Polynomial.roots_C_mul _ (optionEquivLeft_padProductPoly D').2,
    roots_grandProductUnivariate, roots_grandProductUnivariate] at hr
  exact Multiset.map_injective fingerprintPoly_injective hr

end Domain

/-- A common cardinality cap bounds the degree of the difference; the cardinalities may differ. -/
theorem totalDegree_grandProduct_difference_le (M N : Multiset (Vector R m)) {cap : ℕ}
    (hM : M.card ≤ cap) (hN : N.card ≤ cap) :
    (grandProductPoly M - grandProductPoly N).totalDegree ≤ cap :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le ((totalDegree_grandProductPoly M).trans hM)
    ((totalDegree_grandProductPoly N).trans hN))

section FiniteField

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Two different multisets of at most `cap` tuples have grand products that agree at no more
than `cap · |F|^m` of the `|F|^(m+1)` points. -/
theorem card_grandProduct_collision_le (M N : Multiset (Vector F m)) (hne : M ≠ N) {cap : ℕ}
    (hM : M.card ≤ cap) (hN : N.card ≤ cap) :
    (Finset.univ.filter fun x : Option (Fin m) → F ↦
      MvPolynomial.eval x (grandProductPoly M) = MvPolynomial.eval x (grandProductPoly N)).card ≤
      cap * Fintype.card F ^ m := by
  have h := MvPolynomial.card_zeros_le_of_totalDegree_le
    (grandProductPoly M - grandProductPoly N) (grandProduct_difference_ne_zero hne)
    (totalDegree_grandProduct_difference_le M N hM hN)
  simpa only [MvPolynomial.eval_sub, sub_eq_zero, Fintype.card_option, Fintype.card_fin,
    Nat.add_sub_cancel] using h

/-- **Proposition `prop:pad`, counting form**: two sides with different multisets of tuples and
at most `cap` leaves each, padding included, have padded products that agree at no more than
`cap · |F|^m` of the `|F|^(m+1)` points, whatever the padding. -/
theorem card_paddedProduct_collision_le {D D' M N : Multiset (Vector F m)} (hne : M ≠ N)
    {cap : ℕ} (hM : D.card + M.card ≤ cap) (hN : D'.card + N.card ≤ cap) :
    (Finset.univ.filter fun x : Option (Fin m) → F ↦
      MvPolynomial.eval x (paddedProductPoly D M) =
        MvPolynomial.eval x (paddedProductPoly D' N)).card ≤ cap * Fintype.card F ^ m := by
  have hd : paddedProductPoly D M - paddedProductPoly D' N ≠ 0 :=
    fun hz ↦ hne (paddedProductPoly_eq (sub_eq_zero.mp hz))
  have hdeg : (paddedProductPoly D M - paddedProductPoly D' N).totalDegree ≤ cap :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le
      ((totalDegree_paddedProductPoly D M).trans hM)
      ((totalDegree_paddedProductPoly D' N).trans hN))
  have h := MvPolynomial.card_zeros_le_of_totalDegree_le _ hd hdeg
  simpa only [MvPolynomial.eval_sub, sub_eq_zero, Fintype.card_option, Fintype.card_fin,
    Nat.add_sub_cancel, one_mul] using h

end FiniteField

end
end LeanVM.Protocol
