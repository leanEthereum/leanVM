/-
  LeanVM.Protocol.Fingerprint

  The fingerprint of a bus tuple and the product of one side of the bus at the challenges
  `(α, β)`, with the two facts the bus rests on: the product polynomial determines the multiset
  of tuples (Lemma 5.2), and unequal multisets of at most `N` tuples give equal products at no
  more than a `4·N / |E|` fraction of the challenges (Theorem 5.1).
-/

module

public import LeanVM.Protocol.Field
public import LeanVM.Protocol.ToArkLib.GrandProductPoly
public import LeanVM.Protocol.ToCompPoly.Multilinear
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Fingerprints and the products of the bus

Specification §5.2 (`doc/leanvm/body/05-arithmetization.tex:22-59` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`). A bus tuple is sixteen elements of `K`. The verifier
draws `α ∈ E⁴` and maps a tuple `t` to `π_α(t) = Σ_{i<16} eq(α, i)·t_i` (`fingerprint`), where
`eq(α, i)` is the equality kernel at `α` and the four bits of `i`, low bit first: the tuple read
as a table on four variables and evaluated at `α`. The bit order is the one §5.2 now states
(`:24-26`), the specification's convention for an integer's bits (Annex D,
`d-novel-basis.tex:6`; §8, `08-end-to-end-protocol.tex:9`), and that of the deployed weights (the
prover's `crates/leanvm_core/src/leaf.rs:81-90`, the verifier's `eq_kernel`,
`crates/verifier/src/multilinear.rs:7-19`, at `crates/verifier/src/bus.rs:114`). It then draws
`β ∈ E`, and a side of the bus with the multiset `P` of tuples has the product
`Π_{t ∈ P} (β − π_α(t))` (`sideProduct`).

Over the five formal variables `A_0, …, A_3, X` the product is the polynomial
`Π_P = grandProductPoly P` of `LeanVM.Protocol.ToArkLib.GrandProductPoly`, with coefficients in
`K`; `sideProduct` is its value at `(α, β)` (`sideProduct_eq_eval₂`).

* Lemma 5.2 (`sideProduct_poly_eq_iff`): `Π_P = Π_Q` exactly when `P = Q`, multiplicities
  included. The specification leaves its proof `TODO`; it is unique factorization, carried out
  on the roots of `Π_P` as a polynomial in `X`.
* Theorem 5.1 (`card_sideProduct_collision_le`, `sideProduct_collision`): for `P ≠ Q` of at most
  `N` tuples each, at most `4·N·|E|⁴` of the `|E|⁵` challenges give equal products, so a uniform
  challenge does with probability at most `4·N / |E|`. The `4` is the total degree of a factor
  `β − π_α(t)` in `(α, β)`: `π_α` is multilinear in the four coordinates of `α`, and `β` is a
  separate term of degree one. The bound is nearly attained: a tuple whose fingerprint is
  `α_0 α_1 α_2 α_3` and the zero tuple collide at more than `3·|E|⁴` challenges. The multisets
  are fixed before the challenge is drawn.
* Proposition `prop:pad` (`card_paddedSideProduct_collision_le`): a side whose padding rows add
  leaves `π_α(u)` (`padProduct`) for tuples `u` that are not zero collides with another at no
  more than the same `4·N·|E|⁴` challenges when its tuples `P ≠ Q`, `N` now counting the padding
  leaves too: a padded product is a nonzero polynomial in `α` times `Π_P`, so it still determines
  `P` (`paddedProductPoly_eq`). The padding tuples may be anything else, chosen by the prover.

Written from the specification; the bit order of the weights was then checked against the
deployed verifier.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval OracleComp
open scoped ENNReal

@[expose] public section

/-- The fingerprint's weights: `eq(α, i)` for the sixteen coordinates `i`, the bits of `i` low
first. -/
def fingerprintWeights (α : Fin 4 → E) : CMlPolynomialEval E 4 := lagrangeBasis (Vector.ofFn α)

/-- The fingerprint of a bus tuple (§5.2): `π_α(t) = Σ_{i<16} eq(α, i)·t_i`, the weights computed
once. -/
def fingerprint (α : Fin 4 → E) (t : Vector K 16) : E :=
  let w := fingerprintWeights α
  ∑ i : Fin 16, w[i.val] * ofK t[i]

/-- The fingerprint is the extension of the tuple, read as a table on four variables, at `α`. -/
theorem fingerprint_eq_eval₂Mle (α : Fin 4 → E) (t : Vector K 16) :
    fingerprint α t = eval₂Mle (n := 4) t (algebraMap K E) (Vector.ofFn α) := by
  simp only [fingerprint, fingerprintWeights]
  rw [eval₂Mle, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map,
    Extension.Ext.algebraMap_eq_ofBase]
  exact mul_comm _ _

/-- The product of one side of the bus at the challenges `(α, β)`: `Π_{t ∈ P} (β − π_α(t))`. -/
def sideProduct (α : Fin 4 → E) (β : E) (P : Multiset (Vector K 16)) : E :=
  (P.map fun t ↦ β - fingerprint α t).prod

/-- The product is the value at `(α, β)` of the product polynomial, `A_i ↦ α_i` and `X ↦ β`. -/
theorem sideProduct_eq_eval₂ (α : Fin 4 → E) (β : E) (P : Multiset (Vector K 16)) :
    sideProduct α β P =
      MvPolynomial.eval₂ (algebraMap K E) (fun i ↦ i.elim β α) (grandProductPoly (n := 4) P) := by
  have h := eval₂_grandProductPoly (n := 4) P (algebraMap K E) (Vector.ofFn α) β
  have hpt : (fun i : Option (Fin 4) ↦ i.elim β fun j ↦ (Vector.ofFn α)[j]) =
      fun i ↦ i.elim β α :=
    funext fun i ↦ by cases i <;> simp
  rw [hpt] at h
  rw [h, sideProduct]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun t _ ↦ by rw [fingerprint_eq_eval₂Mle])

/-- The fingerprint of `1 − a + b`, slot by slot, is `1 − π_α(a) + π_α(b)`: the weights sum to
`1`. -/
theorem fingerprint_one_sub_add (α : Fin 4 → E) (a b : Vector K 16) :
    fingerprint α (Vector.ofFn fun i ↦ 1 - a[i] + b[i]) =
      1 - fingerprint α a + fingerprint α b := by
  have hw : ∑ i : Fin 16, (fingerprintWeights α)[i.val] = 1 := by
    have h1 := sumCube_lagrangeBasis (Vector.ofFn α)
    simpa [sumCube, fingerprintWeights] using h1
  have hk (i : Fin 16) : ofK (1 - a[i.val] + b[i.val]) = 1 - ofK a[i.val] + ofK b[i.val] := by
    change algebraMap K E _ = _
    rw [map_add, map_sub, map_one]
    rfl
  simp only [fingerprint, Fin.getElem_fin, Vector.getElem_ofFn]
  simp only [hk, mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib, hw]

/-- The product of the fingerprints of a multiset of tuples: a side's padding leaves
(`doc/leanvm`, Proposition `prop:pad`). -/
def padProduct (α : Fin 4 → E) (U : Multiset (Vector K 16)) : E :=
  (U.map (fingerprint α)).prod

/-- The padding product is the value at `α` of the product of the fingerprint polynomials. -/
theorem padProduct_eq_eval₂ (α : Fin 4 → E) (β : E) (U : Multiset (Vector K 16)) :
    padProduct α U =
      MvPolynomial.eval₂ (algebraMap K E) (fun i ↦ i.elim β α) (fingerprintProdPoly (n := 4) U) := by
  have h := eval₂_fingerprintProdPoly (n := 4) U (algebraMap K E) (Vector.ofFn α) β
  have hpt : (fun i : Option (Fin 4) ↦ i.elim β fun j ↦ (Vector.ofFn α)[j]) =
      fun i ↦ i.elim β α :=
    funext fun i ↦ by cases i <;> simp
  rw [hpt] at h
  rw [h, padProduct]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun t _ ↦ by rw [fingerprint_eq_eval₂Mle])

/-- **Lemma 5.2**: the product polynomial determines the multiset of tuples. -/
theorem sideProduct_poly_eq_iff (P Q : Multiset (Vector K 16)) :
    grandProductPoly (n := 4) P = grandProductPoly (n := 4) Q ↔ P = Q :=
  ⟨fun h ↦ grandProductPoly_injective h, congrArg _⟩

/-- The pairs `(α, β)` are the points of the five formal variables: `A_i ↦ α_i`, `X ↦ β`. -/
private def challengeEquiv : (Fin 4 → E) × E ≃ (Option (Fin 4) → E) where
  toFun ab := fun i ↦ i.elim ab.2 ab.1
  invFun x := (fun i ↦ x (some i), x none)
  left_inv _ := rfl
  right_inv x := funext fun i ↦ by cases i <;> rfl

/-- **Theorem 5.1**, counting form: two different multisets of at most `N` tuples each have
equal products at no more than `4·N·|E|⁴` challenges `(α, β)`. -/
theorem card_sideProduct_collision_le {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) {N : ℕ}
    (hP : P.card ≤ N) (hQ : Q.card ≤ N) :
    Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 P = sideProduct ab.1 ab.2 Q} ≤
      4 * N * Nat.card E ^ 4 := by
  classical
  -- The tuples read in `E`: the polynomials over `E`, their values at the points of `E⁵`.
  let φ := algebraMap K E
  let P' := P.map (CMlPolynomialEval.map (n := 4) φ)
  let Q' := Q.map (CMlPolynomialEval.map (n := 4) φ)
  have hne' : P' ≠ Q' := fun h ↦ hne (map_tupleMultiset_injective φ φ.injective h)
  have hval (ab : (Fin 4 → E) × E) (M : Multiset (Vector K 16)) :
      sideProduct ab.1 ab.2 M = MvPolynomial.eval (challengeEquiv ab)
        (grandProductPoly (M.map (CMlPolynomialEval.map (n := 4) φ))) := by
    rw [sideProduct_eq_eval₂, ← map_grandProductPoly, MvPolynomial.eval_map]
    rfl
  have hcount := card_grandProduct_collision_le P' Q' hne' (cap := N) (by simpa [P'] using hP)
    (by simpa [Q'] using hQ)
  rw [Nat.card_congr (challengeEquiv.subtypeEquiv (q := fun x ↦
      MvPolynomial.eval x (grandProductPoly P') = MvPolynomial.eval x (grandProductPoly Q'))
      fun ab ↦ by rw [hval, hval]),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  exact hcount.trans_eq (by simp)

/-- **Proposition `prop:pad`, counting form**: two sides whose tuples `P ≠ Q` come with padding
leaves the fingerprints of `U` and `V`, none of them a zero tuple, and at most `N` leaves each,
have equal products at no more than `4·N·|E|⁴` challenges `(α, β)`, whatever the padding. -/
theorem card_paddedSideProduct_collision_le {P Q U V : Multiset (Vector K 16)} (hne : P ≠ Q)
    (hU : ∀ u ∈ U, ∃ i : Fin 16, u[i] ≠ 0) (hV : ∀ v ∈ V, ∃ i : Fin 16, v[i] ≠ 0) {N : ℕ}
    (hP : U.card + P.card ≤ N) (hQ : V.card + Q.card ≤ N) :
    Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 P * padProduct ab.1 U =
      sideProduct ab.1 ab.2 Q * padProduct ab.1 V} ≤ 4 * N * Nat.card E ^ 4 := by
  classical
  let φ := algebraMap K E
  let m := Multiset.map (CMlPolynomialEval.map (n := 4) φ)
  have hne' : m P ≠ m Q := fun h ↦ hne (map_tupleMultiset_injective φ φ.injective h)
  have hnz (W : Multiset (Vector K 16)) (hW : ∀ w ∈ W, ∃ i : Fin 16, w[i] ≠ 0) :
      ∀ w ∈ m W, ∃ i : Fin (2 ^ 4), w[i] ≠ 0 := by
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hw'
    obtain ⟨i, hi⟩ := hW w hw
    refine ⟨i, ?_⟩
    simp only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map]
    exact fun h0 ↦ hi (φ.injective (h0.trans (map_zero φ).symm))
  have hval (ab : (Fin 4 → E) × E) (M W : Multiset (Vector K 16)) :
      sideProduct ab.1 ab.2 M * padProduct ab.1 W =
        MvPolynomial.eval (challengeEquiv ab) (paddedProductPoly (m W) (m M)) := by
    rw [sideProduct_eq_eval₂ _ ab.2, padProduct_eq_eval₂ _ ab.2, paddedProductPoly,
      MvPolynomial.eval_mul, ← map_grandProductPoly, ← map_fingerprintProdPoly,
      MvPolynomial.eval_map, MvPolynomial.eval_map, mul_comm]
    rfl
  have hcount := card_paddedProduct_collision_le (hnz U hU) (hnz V hV) hne' (cap := N)
    (by simpa [m] using hP) (by simpa [m] using hQ)
  rw [Nat.card_congr (challengeEquiv.subtypeEquiv (q := fun x ↦
      MvPolynomial.eval x (paddedProductPoly (m U) (m P)) =
        MvPolynomial.eval x (paddedProductPoly (m V) (m Q)))
      fun ab ↦ by rw [hval, hval]),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  exact hcount.trans_eq (by simp)

/-- **Theorem 5.1**: two different multisets of at most `N` tuples each have equal products at
a uniform challenge `(α, β)` with probability at most `4·N / |E|`. -/
theorem sideProduct_collision {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) {N : ℕ}
    (hP : P.card ≤ N) (hQ : Q.card ≤ N) :
    Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[sideProduct ab.1 ab.2 P = sideProduct ab.1 ab.2 Q] ≤
      (4 * N : ℕ) / (Fintype.card E : ℝ≥0∞) := by
  classical
  have hcard : Fintype.card ((Fin 4 → E) × E) = Fintype.card E * Fintype.card E ^ 4 := by
    simp [mul_comm]
  have hdiv : ((4 * N : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) =
      ((4 * N * Fintype.card E ^ 4 : ℕ) : ℝ≥0∞) / (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞) := by
    rw [hcard, Nat.cast_mul (4 * N), Nat.cast_mul (Fintype.card E),
      ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero))
        (ENNReal.natCast_ne_top _)]
  rw [hdiv, SampleableType.prEvent_uniformSample_le_div_iff, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact card_sideProduct_collision_le hne hP hQ

end
end LeanVM.Protocol
