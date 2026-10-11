import Whir.AdditiveCode
import Whir.MutualAgreement
import Whir.FieldEquivalence
import Mathlib.LinearAlgebra.Lagrange

/-! Initial candidates cannot acquire extension-field coefficients or nonzero padded
lanes: enough authenticated base-field evaluations force polynomial descent.
The novel-basis corollaries use the actual additive encoder polynomial. -/
namespace Whir.BaseCandidateDescent

open Polynomial Classical
open scoped BigOperators
noncomputable section

variable {K E I : Type*} [Field K] [Field E]

/-- Interpolate the committed values over the base field, then use polynomial
uniqueness over the extension. No decoder or descent property is assumed. -/
theorem polynomial_descent (embed : K →+* E) (s : Finset I)
    (domain values : I → K) (hinj : Set.InjOn domain s)
    (k : ℕ) (p : E[X]) (hp : p.degree < k) (hsize : k ≤ s.card)
    (hmatch : ∀ i ∈ s, p.eval (embed (domain i)) = embed (values i)) :
    ∃ q : K[X], q.degree < k ∧ q.map embed = p := by
  classical
  let q := Lagrange.interpolate s domain values
  have heq : p = q.map embed := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq s
      (fun i hi j hj hij => hinj hi hj (embed.injective hij))
      (hp.trans_le (by exact_mod_cast hsize))
    · simpa [q] using Lagrange.degree_interpolate_lt values hinj
    · intro i hi
      rw [hmatch i hi, Polynomial.eval_map_apply]
      exact congrArg embed (Lagrange.eval_interpolate_at_node values hinj hi).symm
  refine ⟨q, ?_, heq.symm⟩
  simpa [heq] using hp

/-- Zero padding is forced by the same root bound, including dimension zero. -/
theorem polynomial_zero (embed : K →+* E) (s : Finset I)
    (domain : I → K) (hinj : Set.InjOn domain s)
    (k : ℕ) (p : E[X]) (hp : p.degree < k) (hsize : k ≤ s.card)
    (hzero : ∀ i ∈ s, p.eval (embed (domain i)) = 0) : p = 0 := by
  exact Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero s
    (fun i hi j hj hij => hinj hi hj (embed.injective hij))
    (hp.trans_le (by exact_mod_cast hsize)) hzero

/-- The restriction applies to the exact `ofFn` coefficient interpretation of
`MutualAgreement.rsCode` and `CodingBounds`, not a separately postulated decoder. -/
theorem coefficients_descent (embed : K →+* E) (s : Finset I)
    (domain values : I → K) (hinj : Set.InjOn domain s)
    (k : ℕ) (a : Fin k → E) (hsize : k ≤ s.card)
    (hmatch : ∀ i ∈ s, (Polynomial.ofFn k a).eval (embed (domain i)) =
      embed (values i)) :
    ∃ b : Fin k → K, ∀ j, embed (b j) = a j := by
  obtain ⟨q, _, hq⟩ := polynomial_descent embed s domain values hinj k
    (Polynomial.ofFn k a) (Polynomial.ofFn_degree_lt a) hsize hmatch
  refine ⟨fun j => q.coeff j, fun j => ?_⟩
  have h := congrArg (fun p : E[X] => p.coeff j) hq
  simpa [Polynomial.ofFn_coeff_eq_val_of_lt a j.isLt] using h

theorem coefficients_zero (embed : K →+* E) (s : Finset I)
    (domain : I → K) (hinj : Set.InjOn domain s)
    (k : ℕ) (a : Fin k → E) (hsize : k ≤ s.card)
    (hzero : ∀ i ∈ s, (Polynomial.ofFn k a).eval (embed (domain i)) = 0) :
    ∀ j, a j = 0 := by
  have hp := polynomial_zero embed s domain hinj k (Polynomial.ofFn k a)
    (Polynomial.ofFn_degree_lt a) hsize hzero
  intro j
  have h := congrArg (fun p : E[X] => p.coeff j) hp
  simpa [Polynomial.ofFn_coeff_eq_val_of_lt a j.isLt] using h

/-- Every close RS word has base-field coefficients on the entire domain, not
just on its agreement set. -/
theorem rsCode_descent (embed : K →+* E) (s : Finset I)
    (domain values : I → K) (hinj : Set.InjOn domain s)
    (k : ℕ) (w : I → E)
    (hw : w ∈ MutualAgreement.rsCode (fun i => embed (domain i)) k)
    (hsize : k ≤ s.card) (hmatch : ∀ i ∈ s, w i = embed (values i)) :
    ∃ b : Fin k → K, ∀ i,
      w i = embed ((Polynomial.ofFn k b).eval (domain i)) := by
  obtain ⟨p, hp, heval⟩ := (MutualAgreement.mem_rsCode _ _ _).mp hw
  obtain ⟨q, hq, hmap⟩ := polynomial_descent embed s domain values hinj k p hp hsize
    (fun i hi => (heval i).trans (hmatch i hi))
  have hmem : (fun i => q.eval (domain i)) ∈ MutualAgreement.rsCode domain k :=
    (MutualAgreement.mem_rsCode _ _ _).mpr ⟨q, hq, fun _ => rfl⟩
  obtain ⟨b, hb⟩ := (MutualAgreement.mem_rsCode_iff_coefficients _ _ _).mp hmem
  refine ⟨b, fun i => ?_⟩
  rw [hb i, ← Polynomial.eval_map_apply, hmap, heval]

open AdditiveCode

@[simp] theorem map_subspace (embed : K →+* E) (v : ℕ → K) (n : ℕ) :
    (subspace v n).map embed = subspace (fun i => embed (v i)) n := by
  induction n with
  | zero => simp [subspace]
  | succ n ih =>
    simp only [subspace, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C]
    rw [← Polynomial.eval_map_apply, ih]

@[simp] theorem map_normalized (embed : K →+* E) (v : ℕ → K) (n : ℕ) :
    (normalized v n).map embed = normalized (fun i => embed (v i)) n := by
  simp only [normalized, Polynomial.map_mul, Polynomial.map_C, map_inv₀]
  rw [← Polynomial.eval_map_apply, map_subspace]

@[simp] theorem map_novel (embed : K →+* E) (v : ℕ → K) (n j : ℕ) :
    (novel v n j).map embed = novel (fun i => embed (v i)) n j := by
  induction n generalizing j with
  | zero => simp [novel]
  | succ n ih =>
    simp only [novel]
    split_ifs <;> simp [ih]

@[simp] theorem map_polynomial (embed : K →+* E) (v : ℕ → K) (n : ℕ)
    (a : Fin (2^n) → K) :
    (polynomial v n a).map embed =
      polynomial (fun i => embed (v i)) n (fun j => embed (a j)) := by
  simp [polynomial, Polynomial.map_sum]

/-- Binary independence is preserved by the field embedding; hence the
extension novel-basis decoder is proved injective, never assumed injective. -/
theorem independent_map (embed : K →+* E) (v : ℕ → K) (n : ℕ)
    (h : Independent v n) : Independent (fun i => embed (v i)) n := by
  have hspan (m : ℕ) : binarySpan (fun i => embed (v i)) m = embed '' binarySpan v m := by
    induction m with
    | zero => simp [binarySpan]
    | succ m ih =>
      rw [binarySpan, ih, binarySpan, Set.image_union]
      congr 1
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z + v m, ⟨z, hz, rfl⟩, map_add embed z (v m)⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨embed z, ⟨z, hz, rfl⟩, (map_add embed z (v m)).symm⟩
  intro i hi hm
  rw [hspan] at hm
  obtain ⟨x, hx, he⟩ := hm
  exact h i hi (embed.injective he ▸ hx)

/-- A close initial novel-basis candidate is the embedding of a base-field
message. This is the message to which concrete GF2^64 bit decomposition applies. -/
theorem novel_coefficients_descent [CharP K 2] [CharP E 2]
    (embed : K →+* E) (v : ℕ → K) (n : ℕ) (hv : Independent v n)
    (s : Finset I) (domain values : I → K) (hinj : Set.InjOn domain s)
    (a : Fin (2^n) → E) (hsize : 2^n ≤ s.card)
    (hmatch : ∀ i ∈ s,
      (polynomial (fun j => embed (v j)) n a).eval (embed (domain i)) =
        embed (values i)) :
    ∃ b : Fin (2^n) → K, ∀ j, embed (b j) = a j := by
  have hvE := independent_map embed v n hv
  obtain ⟨q, hq, heq⟩ := polynomial_descent embed s domain values hinj (2^n)
    (polynomial (fun j => embed (v j)) n a)
    (by simpa using polynomial_degree_lt hvE a) hsize hmatch
  obtain ⟨b, hb⟩ := (polynomial_surjective hv q).mpr (by simpa using hq)
  have he : (fun j => embed (b j)) = a := by
    apply polynomial_injective hvE
    rw [← map_polynomial, hb, heq]
  exact ⟨b, fun j => congrFun he j⟩

theorem novel_coefficients_zero [CharP K 2] [CharP E 2]
    (embed : K →+* E) (v : ℕ → K) (n : ℕ) (hv : Independent v n)
    (s : Finset I) (domain : I → K) (hinj : Set.InjOn domain s)
    (a : Fin (2^n) → E) (hsize : 2^n ≤ s.card)
    (hzero : ∀ i ∈ s,
      (polynomial (fun j => embed (v j)) n a).eval (embed (domain i)) = 0) :
    ∀ j, a j = 0 := by
  have hvE := independent_map embed v n hv
  have hp := polynomial_zero embed s domain hinj (2^n)
    (polynomial (fun j => embed (v j)) n a)
    (by simpa using polynomial_degree_lt hvE a) hsize hzero
  have ha : a = 0 := polynomial_injective hvE (by simpa [polynomial] using hp)
  intro j
  exact congrFun ha j

/-- The Johnson threshold implies strictly more than the degree bound. -/
theorem johnson_threshold_gt_degree (N D t : ℕ) (hD : D ≤ N)
    (hthreshold : N * D < t^2) : D < t := by
  by_contra h
  have ht : t ≤ D := by omega
  nlinarith

/-- Thus any agreement set of size at least `t > D` determines all `D+1`
coefficients, including base-field and zero-padding restrictions above. -/
theorem enough_matches (s : Finset I) (D t : ℕ)
    (ht : D < t) (hclose : t ≤ s.card) : D + 1 ≤ s.card := by omega

/-- Same-set interleaved candidates restrict lane by lane. The threshold is
strictly above the encoder's degree bound; absent lanes are forced to zero. -/
theorem interleaved_novel_restriction {L : Type*} [CharP K 2] [CharP E 2]
    (embed : K →+* E) (v : ℕ → K) (n : ℕ) (hv : Independent v n)
    (s : Finset I) (domain : I → K) (hinj : Set.InjOn domain s)
    (values : L → I → K) (active : Set L)
    (hpadding : ∀ l, l ∉ active → ∀ i ∈ s, values l i = 0)
    (a : L → Fin (2^n) → E) (t : ℕ)
    (ht : 2^n - 1 < t) (hclose : t ≤ s.card)
    (hmatch : ∀ l i, i ∈ s →
      (polynomial (fun j => embed (v j)) n (a l)).eval (embed (domain i)) =
        embed (values l i)) :
    ∃ b : L → Fin (2^n) → K,
      (∀ l j, embed (b l j) = a l j) ∧
      (∀ l, l ∉ active → ∀ j, b l j = 0) := by
  have hsize : 2^n ≤ s.card := by omega
  have hd (l : L) := novel_coefficients_descent embed v n hv s domain (values l)
    hinj (a l) hsize (hmatch l)
  choose b hb using hd
  refine ⟨b, hb, fun l hl j => ?_⟩
  have hz := novel_coefficients_zero embed v n hv s domain hinj (a l) hsize
    (fun i hi => by rw [hmatch l i hi, hpadding l hl i hi, map_zero])
  apply embed.injective
  rw [hb, hz, map_zero]

/-- Reify the descended message in the actual base-word representation. Only
surjectivity of the representation is needed; no candidate decoder injectivity
is assumed. In particular a checked GF2^64 representation gives GF2^64 words,
and every absent lane is literally the zero word before bit decomposition. -/
theorem word_candidates_restrict {L W : Type*} [Zero W] [CharP K 2] [CharP E 2]
    (embed : K →+* E) (repr : W → K) (hrepr : Function.Surjective repr)
    (hzero : repr 0 = 0)
    (v : ℕ → K) (n : ℕ) (hv : Independent v n)
    (s : Finset I) (domain : I → K) (hinj : Set.InjOn domain s)
    (values : L → I → K) (active : Set L)
    (hpadding : ∀ l, l ∉ active → ∀ i ∈ s, values l i = 0)
    (a : L → Fin (2^n) → E) (t : ℕ)
    (ht : 2^n - 1 < t) (hclose : t ≤ s.card)
    (hmatch : ∀ l i, i ∈ s →
      (polynomial (fun j => embed (v j)) n (a l)).eval (embed (domain i)) =
        embed (values l i)) :
    ∃ words : L → Fin (2^n) → W,
      (∀ l j, embed (repr (words l j)) = a l j) ∧
      (∀ l, l ∉ active → ∀ j, words l j = 0) := by
  obtain ⟨b, hb, hpad⟩ := interleaved_novel_restriction embed v n hv s domain hinj
    values active hpadding a t ht hclose hmatch
  choose word hword using fun l j => hrepr (b l j)
  refine ⟨fun l j => if l ∈ active then word l j else 0, ?_, ?_⟩
  · intro l j
    dsimp only
    split_ifs with hl
    · rw [hword, hb]
    · rw [hzero, ← hpad l hl j, hb]
  · intro l hl j
    simp [hl]

/-- Concrete restriction to GF2^64 machine words. All field-tower and word
representation obligations are discharged by the checked exact field model. -/
theorem actual_word_candidates_restrict {L : Type*}
    (v : ℕ → Concrete.K) (n : ℕ)
    (hv : Independent (fun j => FieldModel.toBaseQuotient (v j)) n)
    (s : Finset I) (domain : I → Concrete.K) (hinj : Set.InjOn domain s)
    (values : L → I → Concrete.K) (active : Set L)
    (hpadding : ∀ l, l ∉ active → ∀ i ∈ s, values l i = 0)
    (a : L → Fin (2^n) → Concrete.E) (t : ℕ)
    (ht : 2^n - 1 < t) (hclose : t ≤ s.card)
    (hmatch : ∀ l i, i ∈ s →
      (polynomial (fun j => Concrete.E.ofK (v j)) n (a l)).eval
        (Concrete.E.ofK (domain i)) = Concrete.E.ofK (values l i)) :
    ∃ words : L → Fin (2^n) → Concrete.K,
      (∀ l j, Concrete.E.ofK (words l j) = a l j) ∧
      (∀ l, l ∉ active → ∀ j, words l j = 0) := by
  have h := word_candidates_restrict FieldModel.baseEmbedding
    FieldModel.toBaseQuotient FieldModel.toBaseQuotient_bijective.2
    FieldModel.toBaseQuotient_zero
    (fun j => FieldModel.toBaseQuotient (v j)) n hv s
    (fun i => FieldModel.toBaseQuotient (domain i))
    (fun i hi j hj he => hinj hi hj (FieldModel.toBaseQuotient_bijective.1 he))
    (fun l i => FieldModel.toBaseQuotient (values l i)) active
    (fun l hl i hi => by rw [hpadding l hl i hi, FieldModel.toBaseQuotient_zero])
    a t ht hclose (by simpa only [FieldModel.baseEmbedding_word] using hmatch)
  simpa only [FieldModel.baseEmbedding_word] using h

end
end Whir.BaseCandidateDescent

#print axioms Whir.BaseCandidateDescent.polynomial_descent
#print axioms Whir.BaseCandidateDescent.rsCode_descent
#print axioms Whir.BaseCandidateDescent.novel_coefficients_zero
#print axioms Whir.BaseCandidateDescent.word_candidates_restrict
#print axioms Whir.BaseCandidateDescent.actual_word_candidates_restrict
