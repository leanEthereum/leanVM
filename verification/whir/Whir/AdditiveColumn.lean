import Whir.AdditiveBasis
import Whir.FieldInverse

/-! Refinement of the actual append/map-scale column loop and dense encoder.
`column_map` and `encode_map` identify the real arrays with novel-polynomial
evaluation; `encode_injective` and `encode_agreement_bound` then discharge the
coding obligations, including binary-basis independence and word-index bounds.

The generic transport uses field representations preserving individual
machine operations, not an assumed encoder/RS identity. The final
`concrete_*` theorems discharge those representations using `FieldInverse`,
including the actual `kinv`, actual `E.ofK`, and certified field operations.
They retain only dimension and no-word-wrap premises. -/
namespace Whir.AdditiveCode
open Polynomial Whir.Concrete Whir.ArrayLayout
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [Inhabited F]

private theorem column_loop_map
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (scale : ∀ a s, e.map (E.scale a s) = e.map a * f.map s)
    (v : Nat → F) (x : F) (ss : List K) :
    (∀ i < ss.length, f.map ss[i]! = (normalized v i).eval x) →
    (ss.foldl (fun out s => out ++ out.map (fun a => a.scale s)) #[E.one]).map e.map =
      tab (2 ^ ss.length) fun j => (novel v ss.length j).eval x := by
  induction ss using List.reverseRecOn with
  | nil =>
    intro _
    simp [novel, tab]
    exact e.one
  | append_singleton ss s ih =>
    intro hn
    have hp : ∀ i < ss.length, f.map ss[i]! = (normalized v i).eval x := by
      intro i hi
      have h := hn i (by simp; omega)
      simpa only [getElem!_pos ss i hi,
        getElem!_pos (ss ++ [s]) i (by simp; omega), List.getElem_append_left hi] using h
    have hs : f.map s = (normalized v ss.length).eval x := by
      simpa [getElem!_pos] using hn ss.length (by simp)
    have hscale (a : Array E) :
        (a.map (fun a => a.scale s)).map e.map =
          (a.map e.map).map (fun a => a * f.map s) := by
      simp only [Array.map_map, Function.comp_def]
      congr 1
      funext a
      exact scale a s
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Array.map_append,
      hscale, ih hp, List.length_append, List.length_singleton]
    apply Array.ext
    · simp [pow_succ]; omega
    · intro j hj hj'
      have hjn : j < 2 ^ (ss.length + 1) := by simpa using hj'
      by_cases h : j < 2 ^ ss.length
      · rw [Array.getElem_append_left (by simpa using h)]
        simp [tab, novel, h]
      · rw [Array.getElem_append_right (by simpa using Nat.le_of_not_gt h)]
        simp [tab, novel, h, hs]

/-- Scalar multiplication uses exactly multiplication by the actual base
embedding, proved from the checked carryless-multiplication representation. -/
theorem scale_eq_mul_ofK (a : E) (s : K) : E.scale a s = a * E.ofK s := by
  have hz (x : K) : kmul x 0 = 0 := by
    apply FieldModel.toBaseQuotient_injective
    simp [FieldModel.toBaseQuotient_kmul]
  change E.scale a s = E.mul a (E.ofK s)
  simp [E.scale, E.mul, E.ofK, hz]

/-- Exact novel-basis evaluation of every actual dense column entry. -/
theorem column_map
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (n q : Nat) :
    (column n q).map e.map =
      tab (2 ^ n) fun j => (novel (bitBasis f.map) n j).eval (f.map (UInt64.ofNat q)) := by
  have scale : ∀ a s, e.map (E.scale a s) = e.map a * f.map s := by
    intro a s
    rw [scale_eq_mul_ofK, e.mul, ofK]
  have h := column_loop_map f e scale (bitBasis f.map) (f.map (UInt64.ofNat q))
    (normalizedSubspaces n (UInt64.ofNat q)).toList (by
      intro i hi
      simpa only [Array.getElem!_toList] using
        normalizedSubspaces_map f n (UInt64.ofNat q) i (by simpa using hi))
  unfold column
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
  change ((normalizedSubspaces n (UInt64.ofNat q)).foldl
    (fun out s => out ++ out.map (fun a => a.scale s)) #[E.one]).map e.map = _
  rw [← Array.foldl_toList]
  simpa only [Array.length_toList, QueryRefinement.size_normalizedSubspaces] using h

/-- The polynomial represented by the actual dense coefficient array. -/
def arrayPolynomial (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (n : Nat) (a : Array E) : F[X] :=
  polynomial (bitBasis f.map) n (fun j => e.map a[j.val]!)

/-- Actual dense `encode` evaluates precisely the novel-basis polynomial. -/
theorem encode_map
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (n rate : Nat) (a : Array E) (shape : a.size = 2 ^ n)
    (q : Nat) (hq : q < 2 ^ (n + rate)) :
    e.map (encode n rate a)[q]! =
      (arrayPolynomial f e n a).eval (f.map (UInt64.ofNat q)) := by
  rw [encode, getElem!_tab _ _ _ hq, e.map_dot, column_map f e ofK]
  simp only [ArrayAlgebra.dot_eq_sum,
    Array.size_map, size_tab, shape, min_self, arrayPolynomial, polynomial,
    eval_finsetSum, eval_smul, smul_eq_mul]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [getElem!_tab _ _ _ j.isLt]
  simp [getElem!_pos, show j.val < a.size by rw [shape]; exact j.isLt]

/-- The actual coefficient array embeds injectively into its polynomial;
binary-basis independence is discharged from faithful machine representation. -/
theorem arrayPolynomial_injective
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (hf : Function.Injective f.map) [CharP F 2]
    (n : Nat) (hn : n ≤ 64) (a b : Array E)
    (ha : a.size = 2 ^ n) (hb : b.size = 2 ^ n)
    (h : arrayPolynomial f e n a = arrayPolynomial f e n b) : a = b := by
  have hc := polynomial_injective (bitBasis_independent f hf n hn) h
  apply Array.ext
  · omega
  · intro i hi hi'
    apply e.injective
    have hh := congrFun hc ⟨i, by simpa [ha] using hi⟩
    simpa only [getElem!_pos a i hi, getElem!_pos b i hi'] using hh

theorem arrayPolynomial_degree_lt
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (hf : Function.Injective f.map) [CharP F 2] (n : Nat) (hn : n ≤ 64)
    (a : Array E) : (arrayPolynomial f e n a).degree < 2 ^ n :=
  polynomial_degree_lt (bitBasis_independent f hf n hn) _

/-- Compatible faithful extension representation also proves faithfulness of
the actual base embedding; callers need not postulate base injectivity. -/
theorem baseRepresentation_injective
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s) : Function.Injective f.map := by
  intro a b h
  have he : E.ofK a = E.ofK b := e.injective (by simpa only [ofK] using h)
  exact congrArg E.c0 he

omit [Inhabited F] in
/-- Distinct in-range machine query indices are distinct field points. -/
theorem evaluationPoint_injective (f : BaseRepresentation F)
    (hf : Function.Injective f.map) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : f.map (UInt64.ofNat i) = f.map (UInt64.ofNat j)) : i = j := by
  have hn := congrArg UInt64.toNat (hf h)
  simpa only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hn

/-- The exact machine query domain as an embedding suitable for RS/MCA
theorems indexed by `Fin N`; no surrogate evaluation points are introduced. -/
def machineDomain (f : BaseRepresentation F) (hf : Function.Injective f.map)
    (depth : Nat) (hd : depth ≤ 64) : Fin (2 ^ depth) ↪ F where
  toFun q := f.map (UInt64.ofNat q.val)
  inj' a b h := by
    apply Fin.ext
    have hmax : 2 ^ depth ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hd
    exact evaluationPoint_injective f hf (a.isLt.trans_le hmax) (b.isLt.trans_le hmax) h

/-- The actual encoder, represented as a whole array, is polynomial evaluation
on the actual word-index domain. -/
theorem encode_map_array
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (n rate : Nat) (a : Array E) (shape : a.size = 2 ^ n) :
    (encode n rate a).map e.map =
      tab (2 ^ (n + rate)) fun q =>
        (arrayPolynomial f e n a).eval (f.map (UInt64.ofNat q)) := by
  apply Array.ext
  · simp [encode]
  · intro q hq hq'
    have hqn : q < 2 ^ (n + rate) := by simpa using hq'
    have hqa : q < (encode n rate a).size := by simpa [encode] using hqn
    simp only [Array.getElem_map, tab, List.getElem_toArray, List.getElem_range]
    simpa only [getElem!_pos (encode n rate a) q hqa] using
      encode_map f e ofK n rate a shape q hqn

/-- Distinct actual coefficient arrays agree at at most `2^n-1` actual encoded
positions. Both novel-basis independence and query-domain injectivity are
proved from machine representation and the no-word-wrap bound. -/
theorem encode_agreement_bound
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (hf : Function.Injective f.map) [CharP F 2]
    (n rate : Nat) (depth : n + rate ≤ 64)
    (a b : Array E) (ha : a.size = 2 ^ n) (hb : b.size = 2 ^ n) (hne : a ≠ b) :
    ((Finset.range (2 ^ (n + rate))).filter fun q =>
      (encode n rate a)[q]! = (encode n rate b)[q]!).card ≤ 2 ^ n - 1 := by
  classical
  let point := fun q => f.map (UInt64.ofNat q)
  let domain := (Finset.range (2 ^ (n + rate))).image point
  have hn : n ≤ 64 := by omega
  have hpoly : arrayPolynomial f e n a ≠ arrayPolynomial f e n b :=
    fun h => hne (arrayPolynomial_injective f e hf n hn a b ha hb h)
  have hdegree (c : Array E) : (arrayPolynomial f e n c).natDegree ≤ 2 ^ n - 1 := by
    by_cases hz : arrayPolynomial f e n c = 0
    · simp [hz]
    · exact Nat.le_pred_of_lt ((natDegree_lt_iff_degree_lt hz).mpr
        (arrayPolynomial_degree_lt f e hf n hn c))
  have hagree := Whir.Soundness.evaluation_agreement domain _ _ hpoly
    (2 ^ n - 1) (hdegree a) (hdegree b)
  apply Nat.le_trans _ hagree
  apply Finset.card_le_card_of_injOn point
  · intro q hq
    obtain ⟨hqr, he⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q, hqr, rfl⟩, ?_⟩
    have hm := congrArg e.map he
    simpa only [encode_map f e ofK n rate a ha q (Finset.mem_range.mp hqr),
      encode_map f e ofK n rate b hb q (Finset.mem_range.mp hqr)] using hm
  · intro i hi j hj he
    have hmax : 2 ^ (n + rate) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) depth
    exact evaluationPoint_injective f hf
      ((Finset.mem_range.mp (Finset.mem_filter.mp hi).1).trans_le hmax)
      ((Finset.mem_range.mp (Finset.mem_filter.mp hj).1).trans_le hmax) he

/-- Faithful dense encoding follows from the actual agreement bound, not an
assumed encoder-is-RS identity. -/
theorem encode_injective
    (f : BaseRepresentation F) (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (hf : Function.Injective f.map) [CharP F 2]
    (n rate : Nat) (depth : n + rate ≤ 64)
    (a b : Array E) (ha : a.size = 2 ^ n) (hb : b.size = 2 ^ n)
    (h : encode n rate a = encode n rate b) : a = b := by
  by_contra hne
  have hagree := encode_agreement_bound f e ofK hf n rate depth a b ha hb hne
  simp only [h, Finset.filter_true, Finset.card_range] at hagree
  have hpow : 2 ^ n ≤ 2 ^ (n + rate) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ n := by positivity
  omega

/-- All representation laws for the actual base embedding, including the
executable inverse, are supplied by checked field-model theorems. -/
def concreteBaseRepresentation : BaseRepresentation E where
  map := E.ofK
  one := FieldModel.ofK_one
  add := FieldModel.ofK_xor
  mul := FieldModel.ofK_kmul
  inv := FieldModel.ofK_kinv

theorem concrete_bitBasis_independent (n : Nat) (hn : n ≤ 64) :
    Independent (bitBasis E.ofK) n :=
  bitBasis_independent concreteBaseRepresentation FieldModel.ofK_injective n hn

/-- Actual machine query points as a proved injective field domain. -/
def concreteDomain (depth : Nat) (hd : depth ≤ 64) : Fin (2 ^ depth) ↪ E :=
  machineDomain concreteBaseRepresentation FieldModel.ofK_injective depth hd

/-- The actual novel-basis polynomial of the actual coefficient array. -/
def concretePolynomial (n : Nat) (a : Array E) : E[X] :=
  arrayPolynomial concreteBaseRepresentation QueryRefinement.concreteRepresentation n a

/-- No remaining representation hypothesis: actual columns are the evaluated
novel basis for the actual normalized binary field. -/
theorem concrete_column (n q : Nat) :
    column n q =
      tab (2 ^ n) fun j => (novel (bitBasis E.ofK) n j).eval (E.ofK (UInt64.ofNat q)) := by
  simpa only [concreteBaseRepresentation, QueryRefinement.concreteRepresentation,
    id_eq, Array.map_id] using
    column_map concreteBaseRepresentation QueryRefinement.concreteRepresentation
      (fun _ => rfl) n q

/-- Full actual dense encoder/polynomial correspondence with only shape and
query bounds; no field or encoder-correctness premise remains. -/
theorem concrete_encode_eval (n rate : Nat) (a : Array E) (shape : a.size = 2 ^ n)
    (q : Nat) (hq : q < 2 ^ (n + rate)) :
    (encode n rate a)[q]! = (concretePolynomial n a).eval (E.ofK (UInt64.ofNat q)) :=
  encode_map concreteBaseRepresentation QueryRefinement.concreteRepresentation
    (fun _ => rfl) n rate a shape q hq

theorem concrete_encode_array (n rate : Nat) (a : Array E) (shape : a.size = 2 ^ n) :
    encode n rate a =
      tab (2 ^ (n + rate)) fun q =>
        (concretePolynomial n a).eval (E.ofK (UInt64.ofNat q)) := by
  simpa only [concretePolynomial, concreteBaseRepresentation,
    QueryRefinement.concreteRepresentation, id_eq, Array.map_id] using
    encode_map_array concreteBaseRepresentation QueryRefinement.concreteRepresentation
      (fun _ => rfl) n rate a shape

theorem concrete_polynomial_injective (n : Nat) (hn : n ≤ 64) (a b : Array E)
    (ha : a.size = 2 ^ n) (hb : b.size = 2 ^ n)
    (h : concretePolynomial n a = concretePolynomial n b) : a = b :=
  arrayPolynomial_injective concreteBaseRepresentation QueryRefinement.concreteRepresentation
    FieldModel.ofK_injective n hn a b ha hb h

theorem concrete_polynomial_degree_lt (n : Nat) (hn : n ≤ 64) (a : Array E) :
    (concretePolynomial n a).degree < 2 ^ n :=
  arrayPolynomial_degree_lt concreteBaseRepresentation QueryRefinement.concreteRepresentation
    FieldModel.ofK_injective n hn a

/-- Every polynomial in the RS degree space is represented by an actual
coefficient array of the required length, and conversely. -/
theorem concrete_polynomial_surjective (n : Nat) (hn : n ≤ 64) (p : E[X]) :
    (∃ a : Array E, a.size = 2 ^ n ∧ concretePolynomial n a = p) ↔
      p.degree < 2 ^ n := by
  constructor
  · rintro ⟨a, _, rfl⟩
    exact concrete_polynomial_degree_lt n hn a
  · intro hp
    obtain ⟨a, ha⟩ := (polynomial_surjective (concrete_bitBasis_independent n hn) p).mpr hp
    refine ⟨Array.ofFn a, by simp, ?_⟩
    change polynomial (bitBasis E.ofK) n (fun j => (Array.ofFn a)[j.val]!) = p
    have he : (fun j : Fin (2 ^ n) => (Array.ofFn a)[j.val]!) = a := by
      funext j
      simp [getElem!_pos, j.isLt]
    rw [he]
    exact ha

/-- Exact image equality for the actual dense encoder and the RS evaluation
space, not merely an upper degree bound for honest messages. -/
theorem concrete_encode_range (n rate : Nat) (hn : n ≤ 64) (word : Array E) :
    (∃ a : Array E, a.size = 2 ^ n ∧ encode n rate a = word) ↔
      ∃ p : E[X], p.degree < 2 ^ n ∧
        (tab (2 ^ (n + rate)) fun q => p.eval (E.ofK (UInt64.ofNat q))) = word := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨concretePolynomial n a, concrete_polynomial_degree_lt n hn a,
      (concrete_encode_array n rate a ha).symm⟩
  · rintro ⟨p, hp, he⟩
    obtain ⟨a, ha, hap⟩ := (concrete_polynomial_surjective n hn p).mpr hp
    refine ⟨a, ha, ?_⟩
    rw [concrete_encode_array n rate a ha, hap]
    exact he

/-- Actual encoded words have the exact RS agreement bound, proved without
assuming that the executable encoder is a Reed–Solomon code. -/
theorem concrete_encode_agreement_bound (n rate : Nat) (depth : n + rate ≤ 64)
    (a b : Array E) (ha : a.size = 2 ^ n) (hb : b.size = 2 ^ n) (hne : a ≠ b) :
    ((Finset.range (2 ^ (n + rate))).filter fun q =>
      (encode n rate a)[q]! = (encode n rate b)[q]!).card ≤ 2 ^ n - 1 :=
  encode_agreement_bound concreteBaseRepresentation QueryRefinement.concreteRepresentation
    (fun _ => rfl) FieldModel.ofK_injective n rate depth a b ha hb hne

/-- The actual encoder is injective on its valid coefficient arrays. -/
theorem concrete_encode_injective (n rate : Nat) (depth : n + rate ≤ 64)
    (a b : Array E) (ha : a.size = 2 ^ n) (hb : b.size = 2 ^ n)
    (h : encode n rate a = encode n rate b) : a = b :=
  encode_injective concreteBaseRepresentation QueryRefinement.concreteRepresentation
    (fun _ => rfl) FieldModel.ofK_injective n rate depth a b ha hb h

end
end Whir.AdditiveCode
