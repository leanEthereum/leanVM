/-
  LeanVM.Protocol.ToArkLib.Whir.Ood

  Out-of-domain separation: the number of points at which two distinct multilinear tables have
  the same extension, and at which some pair of a finite list collides. Candidate for ArkLib.
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import CompPoly.Multilinear.Basic
import CompPoly.Multilinear.Unique
import ToMathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Out-of-domain separation

Annex B of the leanVM specification (leanVM `127510d1`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), `lem:ood`, in count form, for CompPoly's
hypercube tables `CMlPolynomialEval F κ` and their multilinear extension `evalMle`, evaluated at
points `z : Vector F κ`.

* `card_evalMle_eq_le`: the Schwartz-Zippel count for multilinear extensions. Two distinct
  tables on `κ` variables have the same extension at at most `κ |F|^(κ-1)` points: the
  difference of the extensions is a nonzero polynomial of total degree at most `κ`, and VCVio's
  `MvPolynomial.card_zeros_le_of_totalDegree_le` counts its zeros.
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

section Count

variable [IsDomain F] [Fintype F] [DecidableEq F]

omit [CommRing F] [IsDomain F] [DecidableEq F] in
/-- There are `|F|^κ` points. -/
theorem card_vector_eq_pow (κ : ℕ) : Fintype.card (Vector F κ) = Fintype.card F ^ κ := by
  rw [Fintype.card_congr (arrayVectorEquivFin F κ), Fintype.card_fun, Fintype.card_fin]

omit [Fintype F] [DecidableEq F] in
/-- The multilinear extension of a table as a polynomial, `Σ_i g_i ∏_j (X_j or 1 - X_j)`. -/
private theorem exists_mvPolynomial_evalMle {κ : ℕ} (g : CMlPolynomialEval F κ) :
    ∃ P : MvPolynomial (Fin κ) F, P.totalDegree ≤ κ ∧ ∀ z : Vector F κ,
      MvPolynomial.eval z.get P = evalMle g z := by
  refine ⟨∑ i : Fin (2 ^ κ), MvPolynomial.C g[i] * ∏ j : Fin κ,
      if (BitVec.ofFin i).getLsb j then MvPolynomial.X j else 1 - MvPolynomial.X j, ?_, fun z ↦ ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun i _ ↦
      (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum fun j _ ↦ ?_).trans
      (b := ∑ _j : Fin κ, 1) (by simp))
    split
    · exact (MvPolynomial.totalDegree_X j).le
    · exact (MvPolynomial.totalDegree_sub _ _).trans
        (max_le (by simp) (MvPolynomial.totalDegree_X j).le)
  · simp [eval_mle_eq_eval, eval, Vector.dotProduct_eq_root_dotProduct, dotProduct,
      lagrangeBasis_getElem, apply_ite]

/-- **Schwartz-Zippel for multilinear extensions.** Two distinct tables on `κ` variables have the
same multilinear extension at at most `κ |F|^(κ-1)` points. -/
theorem card_evalMle_eq_le {κ : ℕ} {g g' : CMlPolynomialEval F κ} (hne : g ≠ g') :
    (univ.filter fun z : Vector F κ ↦ evalMle g z = evalMle g' z).card ≤
      κ * Fintype.card F ^ (κ - 1) := by
  obtain ⟨P, hP, hPg⟩ := exists_mvPolynomial_evalMle g
  obtain ⟨P', hP', hPg'⟩ := exists_mvPolynomial_evalMle g'
  have hne0 : P - P' ≠ 0 := fun h ↦ hne <| ext_of_eval_vertex fun i ↦ by
    rw [← eval_mle_eq_eval, ← eval_mle_eq_eval, ← hPg, ← hPg', ← sub_eq_zero, ← map_sub, h,
      map_zero]
  refine le_trans ?_ ((MvPolynomial.card_zeros_le_of_totalDegree_le _ hne0
    ((MvPolynomial.totalDegree_sub _ _).trans (max_le hP hP'))).trans (by simp))
  refine Finset.card_le_card_of_injOn (fun z ↦ z.get) (fun z hz ↦ ?_) fun z₁ _ z₂ _ h ↦ ?_
  · simp only [coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
    rw [map_sub, hPg, hPg', hz, sub_self]
  · exact Vector.ext fun i hi ↦ congrFun h ⟨i, hi⟩

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
