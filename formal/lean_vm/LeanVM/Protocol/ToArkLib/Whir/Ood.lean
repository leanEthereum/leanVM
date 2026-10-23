/-
  LeanVM.Protocol.ToArkLib.Whir.Ood

  Out-of-domain separation: the number of points at which two distinct multilinear tables have
  the same extension, and at which some pair of a finite list collides. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Out-of-domain separation

Annex B of the leanVM specification (leanVM `127510d1`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), `lem:ood`, in count form, for CompPoly's
hypercube tables `CMlPolynomialEval F κ` and their multilinear extension `evalMle`, evaluated at
points `z : Vector F κ`.

* `card_evalMle_eq_le`: the Schwartz-Zippel count for multilinear extensions. Two distinct
  tables on `κ` variables have the same extension at at most `κ |F|^(κ-1)` points. The proof is
  an induction on `κ` through CompPoly's recursive evaluation, which interpolates the low
  coordinate first (`evalMle_evalMleStep`): at a point whose tail separates neither half the
  extension is affine in the head and vanishes once, elsewhere it can vanish everywhere.
* `card_ood_collision_le`: for a finite set `L` of tables, at most `C(|L|, 2) κ |F|^(κ-1)` points
  `z` have two distinct members with equal extensions at `z`, a union over the `C(|L|, 2)`
  unordered pairs.
* `card_ood_collision_image_le`: the same for a list decoded injectively into tables, the form the
  round-by-round analysis consumes (distinct interleaved codewords decode to distinct tables).

Points are counted in `Vector F κ` with the finite-type instance of VCVio
(`instFintypeVector`); `card_vector_eq_pow` gives its size `|F|^κ`.
-/

namespace LeanVM.Protocol.Whir

open Finset CompPoly CMlPolynomialEval

@[expose] public section

variable {F : Type*} [CommRing F]

/-- The even-indexed half of a table on `κ + 1` variables: its restriction to coordinate `0`
equal to `0`. -/
def evens {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) : CMlPolynomialEval F κ :=
  Vector.ofFn fun j : Fin (2 ^ κ) ↦ g.get ⟨2 * j.val, by have := j.isLt; rw [pow_succ]; omega⟩

/-- The odd-indexed half of a table on `κ + 1` variables: its restriction to coordinate `0`
equal to `1`. -/
def odds {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) : CMlPolynomialEval F κ :=
  Vector.ofFn fun j : Fin (2 ^ κ) ↦ g.get ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ]; omega⟩

/-- One interpolation step is the affine combination of the two halves' extensions. -/
theorem evalMle_evalMleStep {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) (a : F)
    (w : Vector F κ) :
    evalMle (evalMleStep g a) w = (1 - a) * evalMle (evens g) w + a * evalMle (odds g) w := by
  simp only [evalMle_eq_sum, evalMleStep, evens, odds, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  ring

/-- The extension at a point is the affine combination, at its head, of the halves' extensions at
its tail. -/
theorem evalMle_succ {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) (z : Vector F (κ + 1)) :
    evalMle g z = (1 - z.head) * evalMle (evens g) z.tail + z.head * evalMle (odds g) z.tail := by
  rw [← evalMle_evalMleStep]
  rfl

omit [CommRing F] in
/-- Two tables with the same halves are equal. -/
theorem eq_of_evens_eq_of_odds_eq {κ : ℕ} {g g' : CMlPolynomialEval F (κ + 1)}
    (he : evens g = evens g') (ho : odds g = odds g') : g = g' := by
  ext i hi
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · have hj : j < 2 ^ κ := by rw [pow_succ] at hi; omega
    have := congrArg (·[j]) he
    simpa [evens, Vector.get_eq_getElem] using this
  · have hj : j < 2 ^ κ := by rw [pow_succ] at hi; omega
    have := congrArg (·[j]) ho
    simpa [odds, Vector.get_eq_getElem] using this

section Count

variable [IsDomain F] [Fintype F] [DecidableEq F]

omit [CommRing F] [IsDomain F] [DecidableEq F] in
/-- There are `|F|^κ` points. -/
theorem card_vector_eq_pow (κ : ℕ) : Fintype.card (Vector F κ) = Fintype.card F ^ κ := by
  rw [Fintype.card_congr (arrayVectorEquivFin F κ), Fintype.card_fun, Fintype.card_fin]

/-- An affine function `A + a (B - A)` of `a` that is not identically zero vanishes at most once. -/
private theorem card_affine_eq_zero_le (A B : F) (h : ¬ (A = 0 ∧ B = 0)) :
    (univ.filter fun a : F ↦ (1 - a) * A + a * B = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a₁ h₁ a₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  by_contra hne
  have hBA : B = A := by
    have : (a₁ - a₂) * (B - A) = 0 := by linear_combination h₁.2 - h₂.2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact sub_eq_zero.mp h
  apply h
  have hA : A = 0 := by rw [hBA] at h₁; linear_combination h₁.2
  exact ⟨hA, hBA.trans hA⟩

/-- **Schwartz-Zippel for multilinear extensions.** Two distinct tables on `κ` variables have the
same multilinear extension at at most `κ |F|^(κ-1)` points. -/
theorem card_evalMle_eq_le : ∀ {κ : ℕ} {g g' : CMlPolynomialEval F κ}, g ≠ g' →
    (univ.filter fun z : Vector F κ ↦ evalMle g z = evalMle g' z).card ≤
      κ * Fintype.card F ^ (κ - 1)
  | 0, g, g', hne => by
    refine (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun z _ hz ↦ hne ?_)).le
    ext i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simpa [evalMle_zero, Vector.get_eq_getElem] using hz
  | κ + 1, g, g', hne => by
    set q := Fintype.card F
    -- The differences of the halves' extensions.
    let A : Vector F κ → F := fun w ↦ evalMle (evens g) w - evalMle (evens g') w
    let B : Vector F κ → F := fun w ↦ evalMle (odds g) w - evalMle (odds g') w
    -- The doubly degenerate tails are few, by induction on a separated half.
    have hdeg : (univ.filter fun w : Vector F κ ↦ A w = 0 ∧ B w = 0).card ≤
        κ * q ^ (κ - 1) := by
      by_cases he : evens g = evens g'
      · have ho : odds g ≠ odds g' := fun ho ↦ hne (eq_of_evens_eq_of_odds_eq he ho)
        refine (Finset.card_le_card fun w hw ↦ ?_).trans (card_evalMle_eq_le ho)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hw ⊢
        exact sub_eq_zero.mp hw.2
      · refine (Finset.card_le_card fun w hw ↦ ?_).trans (card_evalMle_eq_le he)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A] at hw ⊢
        exact sub_eq_zero.mp hw.1
    -- Split a point into its head and tail.
    let P : F × Vector F κ → Prop := fun p ↦ (1 - p.1) * A p.2 + p.1 * B p.2 = 0
    have hsplit : (univ.filter fun z : Vector F (κ + 1) ↦ evalMle g z = evalMle g' z).card ≤
        (univ.filter P).card := by
      refine Finset.card_le_card_of_injOn (fun z ↦ (z.head, z.tail)) (fun z hz ↦ ?_)
        (fun z₁ _ z₂ _ h ↦ ?_)
      · simp only [coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
        rw [evalMle_succ, evalMle_succ] at hz
        simp only [P, A, B]
        linear_combination hz
      · simp only [Prod.mk.injEq] at h
        ext i hi
        cases i with
        | zero => simpa [Vector.head] using h.1
        | succ i =>
          have := congrArg (·[i]) h.2
          simpa [Vector.tail, Nat.add_comm] using this
    have hfiber : (univ.filter P).card =
        ∑ w : Vector F κ, (univ.filter fun a : F ↦ (1 - a) * A w + a * B w = 0).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl fun w _ ↦ (Finset.card_filter _ _).symm
    have hbound : ∀ w : Vector F κ,
        (univ.filter fun a : F ↦ (1 - a) * A w + a * B w = 0).card ≤
          1 + q * (if A w = 0 ∧ B w = 0 then 1 else 0) := by
      intro w
      split_ifs with h
      · exact (Finset.card_le_univ _).trans (by omega)
      · exact (card_affine_eq_zero_le _ _ h).trans (by omega)
    have hsum : ∑ w : Vector F κ, (1 + q * (if A w = 0 ∧ B w = 0 then 1 else 0)) =
        q ^ κ + q * (univ.filter fun w : Vector F κ ↦ A w = 0 ∧ B w = 0).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter]
      simp [card_vector_eq_pow, q]
    calc
      _ ≤ (univ.filter P).card := hsplit
      _ ≤ q ^ κ + q * (κ * q ^ (κ - 1)) := by
        rw [hfiber, ← add_le_add_iff_left 0, zero_add, zero_add]
        exact (Finset.sum_le_sum fun w _ ↦ hbound w).trans
          (hsum.le.trans (Nat.add_le_add_left (Nat.mul_le_mul_left q hdeg) _))
      _ = (κ + 1) * q ^ (κ + 1 - 1) := by
        rcases κ with _ | κ
        · simp
        · simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- **Out-of-domain separation** (Annex B, `lem:ood`, count form). For a finite set `L` of tables
on `κ` variables, at most `C(|L|, 2) κ |F|^(κ-1)` points `z` have two distinct members whose
extensions agree at `z`. -/
theorem card_ood_collision_le {κ : ℕ} (L : Finset (CMlPolynomialEval F κ))
    [DecidablePred fun z : Vector F κ ↦ ∃ g ∈ L, ∃ g' ∈ L, g ≠ g' ∧ evalMle g z = evalMle g' z] :
    (univ.filter fun z : Vector F κ ↦
        ∃ g ∈ L, ∃ g' ∈ L, g ≠ g' ∧ evalMle g z = evalMle g' z).card ≤
      L.card.choose 2 * (κ * Fintype.card F ^ (κ - 1)) := by
  classical
  let bad : Finset (CMlPolynomialEval F κ) → Finset (Vector F κ) := fun P ↦
    univ.filter fun z ↦ ∀ g ∈ P, ∀ g' ∈ P, evalMle g z = evalMle g' z
  calc
    _ ≤ ((L.powersetCard 2).biUnion bad).card := by
      refine Finset.card_le_card fun z hz ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨g, hg, g', hg', hne, heq⟩ := hz
      refine Finset.mem_biUnion.mpr ⟨{g, g'}, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.insert_subset hg (Finset.singleton_subset_iff.mpr hg'),
          Finset.card_pair hne⟩
      · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        rintro a (rfl | rfl) b (rfl | rfl) <;> simp [heq]
    _ ≤ ∑ P ∈ L.powersetCard 2, (bad P).card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ L.powersetCard 2, κ * Fintype.card F ^ (κ - 1) := by
      refine Finset.sum_le_sum fun P hP ↦ ?_
      obtain ⟨g, g', hne, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hP).2
      refine (Finset.card_le_card fun z hz ↦ ?_).trans (card_evalMle_eq_le hne)
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz g (by simp) g' (by simp)
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

/-- **Out-of-domain separation for a decoded list.** If a finite list decodes injectively into
tables on `κ` variables, at most `C(|L|, 2) κ |F|^(κ-1)` points separate two distinct members
badly, i.e. give their decoded tables equal extensions. -/
theorem card_ood_collision_image_le {X : Type*} {κ : ℕ} (L : Finset X)
    (dec : X → CMlPolynomialEval F κ) (hinj : Set.InjOn dec L)
    [DecidablePred fun z : Vector F κ ↦
      ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ evalMle (dec U) z = evalMle (dec U') z] :
    (univ.filter fun z : Vector F κ ↦
        ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ evalMle (dec U) z = evalMle (dec U') z).card ≤
      L.card.choose 2 * (κ * Fintype.card F ^ (κ - 1)) := by
  classical
  rw [← Finset.card_image_of_injOn hinj]
  refine (Finset.card_le_card fun z hz ↦ ?_).trans (card_ood_collision_le (L.image dec))
  rw [Finset.mem_filter] at hz ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨U, hU, U', hU', hne, heq⟩ := hz.2
  exact ⟨dec U, Finset.mem_image_of_mem _ hU, dec U', Finset.mem_image_of_mem _ hU',
    fun h ↦ hne (hinj hU hU' h), heq⟩

end Count

end
end LeanVM.Protocol.Whir
