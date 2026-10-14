import Whir.Layout
import Whir.QuerySoundness
import Whir.Concrete
import Whir.FieldCardinality
import Mathlib.Algebra.BigOperators.Fin
import Whir.SamplingRefinement
import Whir.StratifiedDensity
import Whir.Soundness

/-! Counting the actual 192-bit squeeze extractor, including discarded bits. -/
namespace Whir.SamplingProbability
open Concrete FieldModel
open scoped BigOperators

/-- Representation equivalence in the same little-endian order as `E.toNat`. -/
def squeezeEquiv : E ≃ Fin (2^192) :=
  extensionEquiv.trans ((Equiv.prodCongr wordEquiv
    (Equiv.prodCongr wordEquiv wordEquiv)).trans
    ((Equiv.prodComm _ _).trans
      ((Equiv.prodCongr ((Equiv.prodComm _ _).trans finProdFinEquiv) (Equiv.refl _)).trans
        (finProdFinEquiv.trans (finCongr (by norm_num))))))

@[simp] theorem squeezeEquiv_val (a : E) : (squeezeEquiv a).val = a.toNat := by
  change a.c0.toNat + 2^64 * (a.c1.toNat + 2^64 * a.c2.toNat) =
    a.c0.toNat + 2^64 * a.c1.toNat + 2^128 * a.c2.toNat
  ring

/-- Exact uniform 192-bit integer law: every word has exactly one preimage. -/
theorem toNat_fiber (n : Fin (2^192)) :
    Fintype.card {a : E // a.toNat = n.val} = 1 := by
  classical
  have he : {a : E // a.toNat = n.val} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨squeezeEquiv.symm n, by simp [← squeezeEquiv_val]⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply squeezeEquiv.injective
        apply Fin.ext
        simpa only [Equiv.apply_symm_apply, squeezeEquiv_val] using a.property.symm
      right_inv := by intro a; cases a; rfl }
  exact (Fintype.card_congr he).trans (by simp)

/-- Split one squeeze into all full chunks and its unused high-bit tail. -/
def chunkEquiv (depth : Nat) :
    E ≃ Fin (2 ^ (192 % depth)) × (Fin (192 / depth) → Fin (2 ^ depth)) :=
  squeezeEquiv.trans ((finCongr (by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div])).trans
      (finProdFinEquiv.symm.trans
        (Equiv.prodCongr (Equiv.refl _) finFunctionFinEquiv.symm)))

theorem chunkEquiv_val (depth : Nat) (a : E) (j : Fin (192 / depth)) :
    ((chunkEquiv depth a).2 j).val =
      a.toNat / 2 ^ (j.val * depth) % 2 ^ depth := by
  change ((squeezeEquiv a).val % (2 ^ depth) ^ (192 / depth)) /
    (2 ^ depth) ^ j.val % 2 ^ depth = _
  rw [squeezeEquiv_val]
  have hpow : (2 ^ depth) ^ (192 / depth) =
      (2 ^ depth) ^ j.val * (2 ^ depth) ^ (192 / depth - j.val) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt j.isLt)]
  rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  · rw [← pow_mul, Nat.mul_comm depth j.val]
  · exact dvd_pow_self _ (by omega)

/-- Discarding the tail gives constant fibers, hence independent uniform chunks. -/
theorem chunk_fiber (depth : Nat) (chunks : Fin (192 / depth) → Fin (2 ^ depth)) :
    Fintype.card {a : E // (chunkEquiv depth a).2 = chunks} = 2 ^ (192 % depth) := by
  classical
  let e : {a : E // (chunkEquiv depth a).2 = chunks} ≃ Fin (2 ^ (192 % depth)) :=
    { toFun := fun a => (chunkEquiv depth a.val).1
      invFun := fun tail => ⟨(chunkEquiv depth).symm (tail, chunks), by simp⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply (chunkEquiv depth).injective
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext rfl a.property.symm
      right_inv := by intro tail; simp }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- All squeeze tails and all full chunks are independent coordinates. -/
def tapeEquiv (depth squeezes : Nat) :
    (Fin squeezes → E) ≃
      (Fin squeezes → Fin (2 ^ (192 % depth))) ×
        (Fin (squeezes * (192 / depth)) → Fin (2 ^ depth)) :=
  (Equiv.arrowCongr (Equiv.refl _) (chunkEquiv depth)).trans
    ((Equiv.arrowProdEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _)
        ((Equiv.curry _ _ _).symm.trans
          (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)))))

theorem tapeEquiv_val (depth squeezes : Nat) (t : Fin squeezes → E)
    (i : Fin (squeezes * (192 / depth))) :
    ((tapeEquiv depth squeezes t).2 i).val =
      (t (finProdFinEquiv.symm i).1).toNat /
        2 ^ ((i.val % (192 / depth)) * depth) % 2 ^ depth := by
  exact chunkEquiv_val depth _ _

/-- Split off a prefix without dropping the unused final-squeeze chunks. -/
def prefixEquiv {A : Type*} (total count : Nat) (h : count ≤ total) :
    (Fin total → A) ≃ (Fin count → A) × (Fin (total - count) → A) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le h).symm) (Equiv.refl _)).trans
    ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _))

@[simp] theorem prefixEquiv_apply {A : Type*} (total count : Nat) (h : count ≤ total)
    (f : Fin total → A) (i : Fin count) :
    (prefixEquiv total count h f).1 i = f ⟨i.val, lt_of_lt_of_le i.isLt h⟩ := rfl

/-- Noise includes high-bit tails of every squeeze and unused chunks of the last one. -/
abbrev Noise (depth squeezes count : Nat) :=
  (Fin squeezes → Fin (2 ^ (192 % depth))) ×
    (Fin (squeezes * (192 / depth) - count) → Fin (2 ^ depth))

def queryEquiv (depth squeezes count : Nat) (h : count ≤ squeezes * (192 / depth)) :
    (Fin squeezes → E) ≃ Noise depth squeezes count × (Fin count → Fin (2 ^ depth)) :=
  (tapeEquiv depth squeezes).trans
    ((Equiv.prodCongr (Equiv.refl _) (prefixEquiv _ count h)).trans
      ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans
        (Equiv.prodAssoc _ _ _).symm))

theorem queryEquiv_val (depth squeezes count : Nat) (h : count ≤ squeezes * (192 / depth))
    (t : Fin squeezes → E) (i : Fin count) :
    ((queryEquiv depth squeezes count h t).2 i).val =
      (t (finProdFinEquiv.symm ⟨i.val, lt_of_lt_of_le i.isLt h⟩).1).toNat /
        2 ^ ((i.val % (192 / depth)) * depth) % 2 ^ depth :=
  tapeEquiv_val depth squeezes t _

/-- Counting a coordinate event under an explicit decomposition, not an independence axiom. -/
def coordinateEventEquiv {A N I B : Type*} (e : A ≃ N × (I → B))
    (P : I → B → Prop) :
    {a : A // ∀ i, P i ((e a).2 i)} ≃ N × (∀ i, {b : B // P i b}) where
  toFun a := ((e a.val).1, fun i => ⟨(e a.val).2 i, a.property i⟩)
  invFun x := ⟨e.symm (x.1, fun i => (x.2 i).val), by
    simpa using fun i => (x.2 i).property⟩
  left_inv a := by
    apply Subtype.ext
    exact e.symm_apply_apply a.val
  right_inv x := by
    cases x
    simp

theorem coordinateEvent_card {A N I B : Type*}
    [Fintype A] [Fintype N] [Fintype I] [Fintype B]
    (e : A ≃ N × (I → B)) (P : I → B → Prop) [∀ i, DecidablePred (P i)]
    [DecidablePred (fun a => ∀ i, P i ((e a).2 i))] :
    Fintype.card {a : A // ∀ i, P i ((e a).2 i)} =
      Fintype.card N * ∏ i, Fintype.card {b : B // P i b} := by
  classical
  rw [Fintype.card_congr (coordinateEventEquiv e P), Fintype.card_prod, Fintype.card_pi]

/-- A finite uniform probability, stated as a cardinality ratio. -/
noncomputable def probability {A : Type*} [Fintype A] (P : A → Prop) : ℝ :=
  letI := Classical.decPred P
  (Fintype.card {a : A // P a} : ℝ) / Fintype.card A

theorem probability_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) :
    probability (fun a => P (e a)) = probability P := by
  classical
  unfold probability
  rw [Fintype.card_congr (Equiv.subtypeEquivOfSubtype e), Fintype.card_congr e]

/-- Every event on the actual integer representation has its uniform 192-bit probability. -/
theorem toNat_uniform (P : Nat → Prop) :
    probability (fun a : E => P a.toNat) =
      probability (fun n : Fin (2 ^ 192) => P n.val) := by
  simpa only [squeezeEquiv_val] using
    probability_equiv squeezeEquiv (fun n => P n.val)

theorem coordinateEvent_probability {A N I B : Type*}
    [Fintype A] [Fintype N] [Fintype I] [Fintype B] [Nonempty N]
    (e : A ≃ N × (I → B)) (P : I → B → Prop) :
    probability (fun a => ∀ i, P i ((e a).2 i)) =
      ∏ i, probability (P i) := by
  classical
  unfold probability
  rw [coordinateEvent_card, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun]
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  rw [mul_div_mul_left _ _ (by exact_mod_cast Fintype.card_ne_zero)]
  rw [Finset.prod_div_distrib]
  simp

instance noiseNonempty (depth squeezes count : Nat) : Nonempty (Noise depth squeezes count) :=
  ⟨(fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩)⟩

/-- Exact product law for the prefix of actual nonoverlapping raw chunks. -/
theorem rawChunks_probability (depth squeezes count : Nat)
    (h : count ≤ squeezes * (192 / depth)) (P : Fin count → Fin (2 ^ depth) → Prop) :
    probability (fun t : Fin squeezes → E =>
      ∀ i, P i ((queryEquiv depth squeezes count h t).2 i)) =
        ∏ i, probability (P i) :=
  coordinateEvent_probability (queryEquiv depth squeezes count h) P

/-- The concrete allocation always has enough full chunks, including count zero. -/
theorem squeezeCount_capacity (depth count : Nat) (hd : 0 < depth) (hmax : depth ≤ 192) :
    count ≤ ((count + 192 / depth - 1) / (192 / depth)) * (192 / depth) := by
  have hp := Layout.query_chunks_positive hd hmax
  have hm := Nat.mod_lt (count + 192 / depth - 1) hp
  have he := Nat.mod_add_div (count + 192 / depth - 1) (192 / depth)
  rw [Nat.mul_comm] at he
  omega

/-- This is exactly `Layout.rawQuery` on the actual supplied squeeze array. -/
theorem queryEquiv_rawQuery (depth squeezes count : Nat)
    (h : count ≤ squeezes * (192 / depth)) (t : Fin squeezes → E) (i : Fin count) :
    ((queryEquiv depth squeezes count h t).2 i).val =
      Layout.rawQuery depth (fun j => (Array.ofFn t)[j]!.toNat) i.val := by
  rw [queryEquiv_val]
  have hi : i.val / (192 / depth) < squeezes :=
    (finProdFinEquiv.symm (⟨i.val, lt_of_lt_of_le i.isLt h⟩ :
      Fin (squeezes * (192 / depth)))).1.isLt
  simp only [Layout.rawQuery, getElem!_pos, Array.size_ofFn, hi,
    Array.getElem_ofFn, finProdFinEquiv]
  rfl

/-- Uniformity/independence stated directly in terms of the production raw extractor.
The predicates may be chosen from the history before the query batch, but do not depend on it. -/
theorem actualRaw_probability (depth count : Nat) (hd : 0 < depth) (hmax : depth ≤ 192)
    (P : Fin count → Nat → Prop) :
    probability (fun t : Fin ((count + 192 / depth - 1) / (192 / depth)) → E =>
      ∀ i : Fin count, P i (Layout.rawQuery depth (fun j => (Array.ofFn t)[j]!.toNat) i.val)) =
      ∏ i, probability (fun raw : Fin (2 ^ depth) => P i raw.val) := by
  have h := rawChunks_probability depth _ count (squeezeCount_capacity depth count hd hmax)
    (fun i raw => P i raw.val)
  simpa only [queryEquiv_rawQuery] using h

/-- The concrete top-bit replacement, before identifying its cosets with `Layout`. -/
def concretePlace (count depth i raw : Nat) : Nat :=
  let s := (Concrete.strata count depth)[i]!
  raw % 2 ^ (depth - s.1) + s.2 * 2 ^ (depth - s.1)

theorem deriveQueries_eq (depth count : Nat) (hd : 0 < depth) (hmax : depth ≤ 64)
    (t : Fin ((count + 192 / depth - 1) / (192 / depth)) → E) :
    Concrete.deriveQueries depth count (Array.ofFn t) =
      some (Concrete.tab count fun i => concretePlace count depth i
        (Layout.rawQuery depth (fun j => (Array.ofFn t)[j]!.toNat) i)) := by
  simp [Concrete.deriveQueries, concretePlace, Layout.rawQuery,
    Nat.ne_of_gt hd, Nat.not_lt.mpr hmax]

/-- Exact joint law of the executable sampler, retaining order and repeated indices.
No iid-query or independence premise is supplied: this follows from the squeeze bijection. -/
theorem deriveQueries_probability (depth count : Nat) (hd : 0 < depth) (hmax : depth ≤ 64)
    (P : Fin count → Nat → Prop) :
    probability (fun t : Fin ((count + 192 / depth - 1) / (192 / depth)) → E =>
      ∃ qs, Concrete.deriveQueries depth count (Array.ofFn t) = some qs ∧
        ∀ i : Fin count, P i qs[i.val]!) =
      ∏ i, probability (fun raw : Fin (2 ^ depth) =>
        P i (concretePlace count depth i.val raw.val)) := by
  have h := actualRaw_probability depth count hd (by omega)
    (fun i raw => P i (concretePlace count depth i.val raw))
  convert h using 1
  congr 1
  funext t
  rw [deriveQueries_eq depth count hd hmax]
  simp [Concrete.tab, getElem!_pos]

/-- The symbolic stratum at an actual query position. -/
def queryStratum (count depth : Nat) (i : Fin count) : Layout.Stratum depth :=
  (Layout.strataBits (count.log2 + 1) count depth)[i.val]'(by
    rw [Layout.strataBits_length _ _ _ Nat.lt_log2_self]
    exact i.isLt)

theorem concretePlace_eq (count depth : Nat) (i : Fin count) (raw : Nat) :
    concretePlace count depth i.val raw = Layout.placeQuery (queryStratum count depth i) raw := by
  rw [concretePlace, SamplingRefinement.strata_getElem! count depth i.val i.isLt]
  rfl

private theorem mem_nat_image {depth : Nat} (A : Finset (Fin (2 ^ depth)))
    (a : Fin (2 ^ depth)) : a.val ∈ A.image Fin.val ↔ a ∈ A := by
  classical
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h
    have : b = a := Fin.ext he
    simpa [this] using hb
  · intro h
    exact Finset.mem_image.mpr ⟨a, h, rfl⟩

theorem queryStratum_product (count depth : Nat) (f : Layout.Stratum depth → ℝ) :
    (∏ i : Fin count, f (queryStratum count depth i)) =
      ((Layout.strataBits (count.log2 + 1) count depth).map f).prod := by
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [Layout.strataBits_length _ _ _ Nat.lt_log2_self]
  · intro i hi hj
    simp [queryStratum]

/-- Agreement is fixed before the query message. Queries are not deduplicated. -/
def allQueriesHit (depth count : Nat) (A : Finset (Fin (2 ^ depth)))
    (t : Fin ((count + 192 / depth - 1) / (192 / depth)) → E) : Prop :=
  ∃ qs, Concrete.deriveQueries depth count (Array.ofFn t) = some qs ∧
    ∀ i : Fin count, qs[i.val]! ∈ A.image Fin.val

/-- Exact product of the actual coset-hit densities, for the actual sampler. -/
theorem actual_coset_product (depth count : Nat) (hd : 0 < depth) (hmax : depth ≤ 64)
    (A : Finset (Fin (2 ^ depth))) :
    probability (allQueriesHit depth count A) =
      ((Layout.strataBits (count.log2 + 1) count depth).map
        (StratifiedDensity.density A)).prod := by
  classical
  unfold allQueriesHit
  rw [deriveQueries_probability depth count hd hmax]
  rw [← queryStratum_product]
  apply Finset.prod_congr rfl
  intro i _
  have hp : (fun raw : Fin (2 ^ depth) =>
      concretePlace count depth i.val raw.val ∈ A.image Fin.val) =
      (fun raw => StratifiedDensity.placed (queryStratum count depth i) raw ∈ A) := by
    funext raw
    apply propext
    rw [concretePlace_eq]
    exact mem_nat_image A (StratifiedDensity.placed (queryStratum count depth i) raw)
  rw [hp]
  simp only [probability, Fintype.card_fin]
  convert StratifiedDensity.raw_probability_eq_density A (queryStratum count depth i) using 1
  congr 2
  exact congrArg (fun inst : Fintype {raw : Fin (2 ^ depth) //
    StratifiedDensity.placed (queryStratum count depth i) raw ∈ A} =>
      @Fintype.card _ inst) (Subsingleton.elim _ _)

/-- The query error bound, including count zero, repeated full-domain cosets,
unused high bits, and a partially consumed final squeeze. -/
theorem actual_query_bound (depth count : Nat) (hd : 0 < depth) (hmax : depth ≤ 64)
    (A : Finset (Fin (2 ^ depth))) :
    probability (allQueriesHit depth count A) ≤
      StratifiedDensity.globalDensity A ^ count := by
  rw [actual_coset_product depth count hd hmax A]
  exact StratifiedDensity.strataBits_product_le _ _ _ A Nat.lt_log2_self

/-- Compatibility with the rational finite-probability interface of the security game. -/
theorem probability_eq_uniformProb {Ω : Type*} [Fintype Ω] (P : Ω → Prop)
    [DecidablePred P] :
    probability P = (Soundness.uniformProb (Finset.univ.filter P) : ℝ) := by
  classical
  simp [probability, Soundness.uniformProb, Fintype.card_subtype]

theorem actual_query_bound_rat (depth count : Nat) (hd : 0 < depth) (hmax : depth ≤ 64)
    (A : Finset (Fin (2 ^ depth))) :
    letI := Classical.decPred (allQueriesHit depth count A)
    Soundness.uniformProb (Finset.univ.filter (allQueriesHit depth count A)) ≤
      ((A.card : ℚ) / (2 ^ depth : ℕ)) ^ count := by
  classical
  have h := actual_query_bound depth count hd hmax A
  rw [probability_eq_uniformProb] at h
  unfold StratifiedDensity.globalDensity at h
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_natCast] using h

end Whir.SamplingProbability
