/-
  LeanVM.Protocol.Fingerprint

  The fingerprint of a bus tuple and the product of one side of the bus at the challenges
  `(α, β)`, with the two facts the bus rests on: the product polynomial determines the multiset
  of tuples (Lemma 5.2), and unequal multisets of at most `N` tuples give equal products at no
  more than an `N / |E|` fraction of the challenges (Theorem 5.1), padding leaves or not
  (Proposition `prop:pad`).
-/

module

public import Statement.Field
public import LeanVM.Protocol.ToArkLib.GrandProductPoly

/-!
# Fingerprints and the products of the bus

Specification §5.2 (`doc/leanvm/body/05-arithmetization.tex`, "Fingerprint" to the proof of
Theorem `th:product_check`, at leanVM `f128`; the verifier's `crates/verifier/src/bus.rs`,
`verify_bus_balance`, and the prover's `crates/leanvm_core/src/leaf.rs`). A bus tuple is sixteen
elements of `K`. After a grind the verifier draws one weight per slot, `α ∈ E^16`, and maps a
tuple `t` to `π_α(t) = Σ_{ι<16} α_ι·t_ι` (`fingerprint`), linear in the challenges. It then draws
`β ∈ E`, and a side of the bus with the multiset `P` of tuples has the product
`Π_{t ∈ P} (β − π_α(t))` (`sideProduct`).

Over the seventeen formal variables `A_0, …, A_15, X` the product is the polynomial
`Π_P = grandProductPoly P` of `LeanVM.Protocol.ToArkLib.GrandProductPoly`, with coefficients in
`K`; `sideProduct` is its value at `(α, β)` (`sideProduct_eq_eval₂`).

* Lemma 5.2 (`sideProduct_poly_eq_iff`): `Π_P = Π_Q` exactly when `P = Q`, multiplicities
  included: the `A_ι` are distinct variables, so distinct tuples give distinct, monic, degree-one
  factors in `X`, and unique factorization recovers `P`.
* Theorem 5.1 (`card_sideProduct_collision_le`): for `P ≠ Q` of at most `N` tuples each, at most
  `N·|E|^16` of the `|E|^17` challenges give equal products, an `N / |E|` fraction
  (`sideProduct_collision_ratio_le`): each factor `β − π_α(t)` has total degree one in `(α, β)`.
  The multisets are fixed before the challenge is drawn.
* Proposition `prop:pad` (`card_paddedSideProduct_collision_le`): a padding row of a flush block
  holding the tuple `t` while the public padding row `p` flushes `t(p)` has the leaf
  `(β − π_α(t)) + 1 − (β − π_α(t(p))) = 1 − π_α(t − t(p))` (`padLeaf_eq`), independent of `β`, a
  nonzero polynomial in `α` (constant term `1`) whatever the row holds. A side whose padding rows
  differ from the public one by the tuples `D` has the product `Π_P(α, β) · Π_{d ∈ D}(1 − π_α(d))`
  (`padProduct`); two such sides with `P ≠ Q` and at most `N` leaves each collide at no more than
  the same `N·|E|^16` challenges, whatever the padding. Honest padding rows, `D` all zero, give
  the factor `1` (`padProduct_zero`).

The count tree is not fingerprinted: it weighs its count cells alone, at `β = 0`
(`bus.rs`, `N_TREES`), and its root `R_c ≠ 0` forces every executed count to be nonzero whatever
its padding leaves (`08-end-to-end-protocol.tex`, after Proposition `prop:pad`).

Counts are `Nat.card`s, so no enumeration of `E` is assumed. Written from the specification.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters
open scoped ENNReal

@[expose] public section

/-- The fingerprint's weights: `α_ι` for the sixteen slots `ι`, the bits of `ι` low first. -/
def fingerprintWeights (α : Fin 16 → E) : Vector E 16 := Vector.ofFn α

/-- The fingerprint of a bus tuple (§5.2): `π_α(t) = Σ_{ι<16} α_ι·t_ι`. -/
def fingerprint (α : Fin 16 → E) (t : Vector K 16) : E :=
  let w := fingerprintWeights α
  ∑ i : Fin 16, w[i.val] * ofK t[i]

/-- The fingerprint is the value at `α` of the tuple's symbolic fingerprint. -/
theorem fingerprint_eq_eval₂ (α : Fin 16 → E) (t : Vector K 16) :
    fingerprint α t = MvPolynomial.eval₂ (algebraMap K E) α (fingerprintPoly t) := by
  rw [eval₂_fingerprintPoly]
  simp [fingerprint, fingerprintWeights]

/-- The fingerprint of a slotwise difference is the difference of the fingerprints: `π_α` is
linear. -/
theorem fingerprint_sub (α : Fin 16 → E) (a b : Vector K 16) :
    fingerprint α (Vector.ofFn fun i ↦ a[i] - b[i]) = fingerprint α a - fingerprint α b := by
  simp only [fingerprint, Fin.getElem_fin, Vector.getElem_ofFn, ← Finset.sum_sub_distrib,
    ← mul_sub]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change _ * algebraMap K E _ = _ * (algebraMap K E _ - algebraMap K E _)
  rw [map_sub]

/-- **A padding row's leaf** (Proposition `prop:pad`): the leaf `β − π_α(t)` of the row's tuple
`t`, plus `1 − (β − π_α(t(p)))` for the public padding row `p`, is `1 − π_α(t − t(p))`, whatever
`β`. -/
theorem padLeaf_eq (α : Fin 16 → E) (β : E) (t tp : Vector K 16) :
    β - fingerprint α t + (1 - (β - fingerprint α tp)) =
      1 - fingerprint α (Vector.ofFn fun i ↦ t[i] - tp[i]) := by
  rw [fingerprint_sub]
  ring

/-- The product of one side of the bus at the challenges `(α, β)`: `Π_{t ∈ P} (β − π_α(t))`. -/
def sideProduct (α : Fin 16 → E) (β : E) (P : Multiset (Vector K 16)) : E :=
  (P.map fun t ↦ β - fingerprint α t).prod

/-- The product of a side's padding leaves `1 − π_α(d)`, `d` a padding row's tuple minus the
public padding row's (Proposition `prop:pad`). -/
def padProduct (α : Fin 16 → E) (D : Multiset (Vector K 16)) : E :=
  (D.map fun d ↦ 1 - fingerprint α d).prod

/-- The joint variables' point of `(α, β)`: `A_ι ↦ α_ι`, `X ↦ β`. -/
private def challengeEquiv : (Fin 16 → E) × E ≃ (Option (Fin 16) → E) where
  toFun ab := fun i ↦ i.elim ab.2 ab.1
  invFun x := (fun i ↦ x (some i), x none)
  left_inv _ := rfl
  right_inv x := funext fun i ↦ by cases i <;> rfl

/-- The product is the value at `(α, β)` of the product polynomial. -/
theorem sideProduct_eq_eval₂ (α : Fin 16 → E) (β : E) (P : Multiset (Vector K 16)) :
    sideProduct α β P =
      MvPolynomial.eval₂ (algebraMap K E) (fun i ↦ i.elim β α) (grandProductPoly P) := by
  rw [eval₂_grandProductPoly, sideProduct]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun t _ ↦ by
    rw [fingerprint_eq_eval₂, eval₂_fingerprintPoly])

/-- The padding product is the value at `α` of the padding leaves' polynomial. -/
theorem padProduct_eq_eval₂ (α : Fin 16 → E) (β : E) (D : Multiset (Vector K 16)) :
    padProduct α D =
      MvPolynomial.eval₂ (algebraMap K E) (fun i ↦ i.elim β α) (padProductPoly D) := by
  rw [eval₂_padProductPoly, padProduct]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun d _ ↦ by
    rw [fingerprint_eq_eval₂, eval₂_fingerprintPoly])

/-- With honest padding rows every padding leaf is `1`. -/
theorem padProduct_zero (α : Fin 16 → E) {D : Multiset (Vector K 16)}
    (hD : ∀ d ∈ D, ∀ i : Fin 16, d[i] = 0) : padProduct α D = 1 := by
  refine Multiset.prod_eq_one fun e he ↦ ?_
  obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp he
  have : fingerprint α d = 0 := by
    simp only [fingerprint, Fin.getElem_fin]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [show d[i.val] = 0 from hD d hd i]
    exact mul_eq_zero_of_right _ (map_zero (algebraMap K E))
  rw [this, sub_zero]

/-- **Lemma 5.2**: the product polynomial determines the multiset of tuples. -/
theorem sideProduct_poly_eq_iff (P Q : Multiset (Vector K 16)) :
    grandProductPoly P = grandProductPoly Q ↔ P = Q :=
  ⟨fun h ↦ grandProductPoly_injective h, congrArg _⟩

/-- The value of a polynomial over `K` at `(α, β)`, read over `E`. -/
private theorem eval₂_eq_eval_map (p : MvPolynomial (Option (Fin 16)) K) (ab : (Fin 16 → E) × E) :
    MvPolynomial.eval₂ (algebraMap K E) (fun i ↦ i.elim ab.2 ab.1) p =
      MvPolynomial.eval (challengeEquiv ab) (MvPolynomial.map (algebraMap K E) p) := by
  rw [MvPolynomial.eval_map]
  rfl

/-- **Proposition `prop:pad`, counting form**: two sides whose tuples `P ≠ Q` come with padding
leaves `1 − π_α(d)` for the tuples of `D` and `D'`, whatever they are, and at most `N` leaves
each, have equal products at no more than `N·|E|^16` challenges `(α, β)`. -/
theorem card_paddedSideProduct_collision_le {P Q D D' : Multiset (Vector K 16)} (hne : P ≠ Q)
    {N : ℕ} (hP : D.card + P.card ≤ N) (hQ : D'.card + Q.card ≤ N) :
    Nat.card {ab : (Fin 16 → E) × E // sideProduct ab.1 ab.2 P * padProduct ab.1 D =
      sideProduct ab.1 ab.2 Q * padProduct ab.1 D'} ≤ N * Nat.card E ^ 16 := by
  classical
  let := Fintype.ofFinite E
  let φ := algebraMap K E
  let mp := Multiset.map (Vector.map (n := 16) φ)
  have hne' : mp P ≠ mp Q := fun h ↦ hne (map_tupleMultiset_injective φ φ.injective h)
  have hval (ab : (Fin 16 → E) × E) (M W : Multiset (Vector K 16)) :
      sideProduct ab.1 ab.2 M * padProduct ab.1 W =
        MvPolynomial.eval (challengeEquiv ab) (paddedProductPoly (mp W) (mp M)) := by
    rw [sideProduct_eq_eval₂ _ ab.2, padProduct_eq_eval₂ _ ab.2, eval₂_eq_eval_map,
      eval₂_eq_eval_map, map_grandProductPoly, map_padProductPoly, paddedProductPoly,
      MvPolynomial.eval_mul, mul_comm]
  have hcount := card_paddedProduct_collision_le (D := mp D) (D' := mp D') hne' (cap := N)
    (by simpa [mp] using hP) (by simpa [mp] using hQ)
  rw [Nat.card_congr (challengeEquiv.subtypeEquiv (q := fun x ↦
      MvPolynomial.eval x (paddedProductPoly (mp D) (mp P)) =
        MvPolynomial.eval x (paddedProductPoly (mp D') (mp Q)))
      fun ab ↦ by rw [hval, hval]),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  exact hcount

/-- **Theorem 5.1, counting form**: two different multisets of at most `N` tuples each have
equal products at no more than `N·|E|^16` challenges `(α, β)`. -/
theorem card_sideProduct_collision_le {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) {N : ℕ}
    (hP : P.card ≤ N) (hQ : Q.card ≤ N) :
    Nat.card {ab : (Fin 16 → E) × E // sideProduct ab.1 ab.2 P = sideProduct ab.1 ab.2 Q} ≤
      N * Nat.card E ^ 16 := by
  have h := card_paddedSideProduct_collision_le (D := 0) (D' := 0) hne
    (by simpa using hP) (by simpa using hQ)
  simpa [padProduct] using h

/-- **Theorem 5.1**: two different multisets of at most `N` tuples each have equal products at
an `N / |E|` fraction of the challenges `(α, β)` at most. -/
theorem sideProduct_collision_ratio_le {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) {N : ℕ}
    (hP : P.card ≤ N) (hQ : Q.card ≤ N) :
    (Nat.card {ab : (Fin 16 → E) × E // sideProduct ab.1 ab.2 P = sideProduct ab.1 ab.2 Q} :
        ℝ≥0∞) / (Nat.card ((Fin 16 → E) × E) : ℝ≥0∞) ≤ N / (Nat.card E : ℝ≥0∞) := by
  have hc : Nat.card ((Fin 16 → E) × E) = Nat.card E * Nat.card E ^ 16 := by
    simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin]
    ring
  have hpos : Nat.card E ≠ 0 := Nat.card_pos.ne'
  have hE' : (Nat.card E : ℝ≥0∞) ^ 16 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hpos)
  have hT : (Nat.card E : ℝ≥0∞) ^ 16 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [hc, Nat.cast_mul, Nat.cast_pow]
  calc _ ≤ ((N * Nat.card E ^ 16 : ℕ) : ℝ≥0∞) /
        ((Nat.card E : ℝ≥0∞) * (Nat.card E : ℝ≥0∞) ^ 16) := by
        gcongr
        exact_mod_cast card_sideProduct_collision_le hne hP hQ
    _ = N / (Nat.card E : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_pow, ENNReal.mul_div_mul_right _ _ hE' hT]

end
end LeanVM.Protocol
