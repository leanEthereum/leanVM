/-
  LeanVM.Protocol.ToVCVio.Rom.Bounds

  Two instances of the random-oracle potential bound: hitting a fixed target set, and the
  birthday bound for collisions. Candidate for VCVio.
-/

module

public import LeanVM.Protocol.ToVCVio.Rom.Potential
public import VCVio.OracleComp.QueryTracking.Collision
import VCVio.OracleComp.QueryTracking.Birthday
import ToMathlib.Data.ENNReal.Gauss

/-!
# Fresh hits and collisions under the lazy random oracle

Two classical bounds for VCVio's `randomOracle` on `D →ₒ R`, each proved by exhibiting a
potential for `LeanVM.Protocol.ToVCVio.Rom.Potential`.

* **Fresh hits** (`prEvent_cacheHits_le`). For a target set `T ⊆ R`, the potential is the
  indicator that some cached answer lies in `T` (`hitPotential T`). A fresh query raises it in
  expectation by at most `|T| / |R|` (`freshStepBound_hitPotential`), so from a cache with no
  answer in `T`, a computation with at most `Q` queries receives a fresh answer in `T` with
  probability at most `Q · |T| / |R|`.
* **Collisions** (`prEvent_cacheHasCollision_le`). The step from a collision-free cache with `k`
  entries creates a collision with probability at most `k / |R|`, an increment that grows with
  the cache, so the potential is budgeted (`birthdayPotential`): `1` on a cache with a
  collision, and otherwise `∑_{j < n} (k + j) / |R|` with `n` queries left. From the empty cache
  the bound is `∑_{j < Q} j / |R| = Q (Q - 1) / (2 |R|)`, the same tight birthday bound as
  VCVio's `prEvent_cacheCollision_le_birthday_total_tight`, which states it for
  `cachingOracle`; here it is stated for `randomOracle`.
-/

namespace LeanVM.Protocol

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

@[expose] public section

namespace Rom

variable {D R : Type} [DecidableEq D] [SampleableType R] [Fintype R]

/-! ## Fresh hits -/

/-- Some cached answer lies in `T`. -/
def CacheHits (T : Set R) (c : (D →ₒ R).QueryCache) : Prop :=
  ∃ t u, c t = some u ∧ u ∈ T

open Classical in
/-- The fresh-hit potential: one if some cached answer lies in `T`, zero otherwise. -/
noncomputable def hitPotential (T : Finset R) (c : (D →ₒ R).QueryCache) : ℝ≥0∞ :=
  if CacheHits (T : Set R) c then 1 else 0

omit [SampleableType R] [Fintype R] in
/-- Recording a fresh answer `u` creates a hit exactly when the cache already had one or `u`
lies in `T`. -/
theorem cacheHits_cacheQuery_iff (T : Set R) (c : (D →ₒ R).QueryCache) (t : D) (u : R)
    (hc : c t = none) : CacheHits T (c.cacheQuery t u) ↔ CacheHits T c ∨ u ∈ T := by
  constructor
  · rintro ⟨t', u', h, hu'⟩
    by_cases ht : t' = t
    · subst ht
      rw [QueryCache.cacheQuery_self, Option.some.injEq] at h
      exact Or.inr (h ▸ hu')
    · rw [QueryCache.cacheQuery_of_ne _ _ ht] at h
      exact Or.inl ⟨t', u', h, hu'⟩
  · rintro (⟨t', u', h, hu'⟩ | hu)
    · have ht : t' ≠ t := fun ht ↦ by subst ht; simp [hc] at h
      exact ⟨t', u', by rw [QueryCache.cacheQuery_of_ne _ _ ht]; exact h, hu'⟩
    · exact ⟨t, u, QueryCache.cacheQuery_self _ _ _, hu⟩

/-- A fresh query raises the fresh-hit potential in expectation by at most `|T| / |R|`. -/
theorem freshStepBound_hitPotential (T : Finset R) :
    FreshStepBound (hitPotential (D := D) T) (T.card / Fintype.card R) := by
  classical
  intro c t hc
  by_cases hhit : CacheHits (T : Set R) c
  · have hcard : (Fintype.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have h1 : ∀ u, hitPotential T (c.cacheQuery t u) = 1 := fun u ↦
      ite_eq_left ((cacheHits_cacheQuery_iff _ c t u hc).mpr (Or.inl hhit))
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [ENNReal.div_self hcard (ENNReal.natCast_ne_top _)]
    exact le_self_add.trans (add_le_add_left (by simp [hitPotential, hhit]) _)
  · have h1 : ∀ u, hitPotential T (c.cacheQuery t u) = if u ∈ T then 1 else 0 := fun u ↦ by
      simp only [hitPotential, cacheHits_cacheQuery_iff _ c t u hc, hhit, false_or,
        Finset.mem_coe]
    simp only [h1, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp [hitPotential, hhit]

/-- **The fresh-hit bound.** From a cache with no answer in `T`, a computation with at most `Q`
queries, run against the lazy random oracle, ends with a cached answer in `T` with probability
at most `Q · |T| / |R|`: some fresh answer lands in `T`. -/
theorem prEvent_cacheHits_le {α : Type} (T : Finset R) (oa : OracleComp (D →ₒ R) α) (Q : ℕ)
    (hQ : IsTotalQueryBound oa Q) (c₀ : (D →ₒ R).QueryCache)
    (hc₀ : ¬ CacheHits (T : Set R) c₀) :
    Pr{let z ← (simulateQ (D →ₒ R).randomOracle oa).run c₀}[CacheHits (T : Set R) z.2] ≤
      Q * (T.card / Fintype.card R) := by
  classical
  have h := prEvent_run_randomOracle_le_of_freshStepBound (freshStepBound_hitPotential T) oa Q
    hQ c₀ (fun _ c ↦ CacheHits (T : Set R) c)
    (fun z _ hz ↦ by simp [hitPotential, hz])
  simpa [hitPotential, hc₀] using h

/-! ## Collisions -/

open Classical in
/-- The birthday potential with `n` queries left: one on a cache with a collision, and
otherwise `∑_{j < n} (k + j) / |R|` for a cache with `k` entries. -/
noncomputable def birthdayPotential (n : ℕ) (c : (D →ₒ R).QueryCache) : ℝ≥0∞ :=
  if CacheHasCollision c then 1
  else ∑ j ∈ Finset.range n, (c.enncard + j) / Fintype.card R

omit [SampleableType R] [Fintype R] in
/-- Collisions persist when a fresh point is recorded. -/
theorem cacheHasCollision_cacheQuery {c : (D →ₒ R).QueryCache} {t : D} (hc : c t = none)
    (u : R) (h : CacheHasCollision c) : CacheHasCollision (c.cacheQuery t u) := by
  obtain ⟨t₁, t₂, u₁, u₂, hne, h₁, h₂, heq⟩ := h
  have hle := QueryCache.le_cacheQuery c (u := u) hc
  exact ⟨t₁, t₂, u₁, u₂, hne, hle h₁, hle h₂, heq⟩

/-- The birthday potential is a budgeted potential for `randomOracle`. -/
theorem isBudgetedPotential_birthdayPotential :
    IsBudgetedPotential (birthdayPotential (D := D) (R := R)) where
  mono n c := by
    unfold birthdayPotential
    split_ifs
    · exact le_rfl
    · rw [Finset.sum_range_succ]
      exact le_self_add
  fresh n c t hc := by
    classical
    have hcard : (Fintype.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    by_cases hcol : CacheHasCollision c
    · have h1 : ∀ u, birthdayPotential n (c.cacheQuery t u) = 1 := fun u ↦
        ite_eq_left (cacheHasCollision_cacheQuery hc u hcol)
      simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [ENNReal.div_self hcard (ENNReal.natCast_ne_top _)]
      simp [birthdayPotential, hcol]
    simp only [birthdayPotential, hcol, ite_false]
    set k := c.enncard with hk
    by_cases htop : k = ⊤
    · rw [Finset.sum_range_succ', htop]
      simp [ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top (Fintype.card R))]
    -- The keys populated in `c` form a finite set of at most `k` elements.
    have hfin : c.toSet.Finite := Set.encard_ne_top_iff.mp fun h ↦ htop (by
      simp [hk, QueryCache.enncard, h])
    set S := hfin.toFinset.image Sigma.fst with hS
    have hSmem : ∀ t', c t' ≠ none → t' ∈ S := by
      intro t' ht'
      obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp ht'
      exact Finset.mem_image.mpr ⟨⟨t', u'⟩, hfin.mem_toFinset.mpr hu', rfl⟩
    have hSk : (S.card : ℝ≥0∞) ≤ k := by
      rw [hk, QueryCache.enncard, hfin.encard_eq_coe_toFinset_card]
      exact_mod_cast Finset.card_image_le
    have hbad := card_responses_creating_cacheCollision_le (t := t) hcol hSmem
    -- Each recorded cache either has a collision or has at most `k + 1` entries.
    have hpoint : ∀ u, (if CacheHasCollision (c.cacheQuery t u) then 1
        else ∑ j ∈ Finset.range n, ((c.cacheQuery t u).enncard + j) / Fintype.card R) ≤
        (if CacheHasCollision (c.cacheQuery t u) then 1 else 0) +
          ∑ j ∈ Finset.range n, (k + ((j + 1 : ℕ) : ℝ≥0∞)) / Fintype.card R := by
      intro u
      split_ifs
      · exact le_self_add
      · rw [zero_add]
        refine Finset.sum_le_sum fun j _ ↦ ENNReal.div_le_div_right ?_ _
        calc (c.cacheQuery t u).enncard + j ≤ k + 1 + j := by
              gcongr
              exact QueryCache.enncard_cacheQuery_le c t u
          _ = k + ((j + 1 : ℕ) : ℝ≥0∞) := by
              rw [Nat.cast_succ, add_assoc, add_comm (1 : ℝ≥0∞)]
    calc (∑ u, (if CacheHasCollision (c.cacheQuery t u) then 1
            else ∑ j ∈ Finset.range n, ((c.cacheQuery t u).enncard + j) / Fintype.card R))
            / Fintype.card R
        ≤ (∑ u, ((if CacheHasCollision (c.cacheQuery t u) then 1 else 0) +
            ∑ j ∈ Finset.range n, (k + ((j + 1 : ℕ) : ℝ≥0∞)) / Fintype.card R))
            / Fintype.card R := by
          gcongr with u
          exact hpoint u
      _ = (Finset.univ.filter fun u ↦ CacheHasCollision (c.cacheQuery t u)).card
            / Fintype.card R +
            ∑ j ∈ Finset.range n, (k + ((j + 1 : ℕ) : ℝ≥0∞)) / Fintype.card R := by
          rw [sum_add_const_div_card (spec := D →ₒ R) t, Finset.sum_boole]
      _ ≤ (k + ((0 : ℕ) : ℝ≥0∞)) / Fintype.card R +
            ∑ j ∈ Finset.range n, (k + ((j + 1 : ℕ) : ℝ≥0∞)) / Fintype.card R := by
          gcongr
          rw [Nat.cast_zero, add_zero]
          exact (Nat.cast_le.mpr hbad).trans hSk
      _ = ∑ j ∈ Finset.range (n + 1), (k + (j : ℝ≥0∞)) / Fintype.card R := by
          rw [Finset.sum_range_succ' (fun j ↦ (k + (j : ℝ≥0∞)) / Fintype.card R), add_comm]

/-- **The birthday bound for `randomOracle`.** A computation with at most `Q` queries, run
against the lazy random oracle from the empty cache, ends with two distinct points cached with
the same answer with probability at most `Q (Q - 1) / (2 |R|)`. -/
theorem prEvent_cacheHasCollision_le {α : Type} (oa : OracleComp (D →ₒ R) α) (Q : ℕ)
    (hQ : IsTotalQueryBound oa Q) :
    Pr{let z ← (simulateQ (D →ₒ R).randomOracle oa).run ∅}[CacheHasCollision z.2] ≤
      ((Q * (Q - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card R) := by
  have h := prEvent_run_randomOracle_le_of_budgeted isBudgetedPotential_birthdayPotential oa Q
    hQ ∅ (fun _ c ↦ CacheHasCollision c) (fun z _ hz ↦ by simp [birthdayPotential, hz])
  have hempty : ¬ CacheHasCollision (∅ : (D →ₒ R).QueryCache) := by
    rintro ⟨t₁, _, _, _, _, h₁, _, _⟩
    simp at h₁
  rw [← ENNReal.gauss_sum_inv_eq]
  refine h.trans (le_of_eq ?_)
  simp only [birthdayPotential, hempty, ite_false, QueryCache.enncard_empty, zero_add,
    div_eq_mul_inv]

end Rom

end
end LeanVM.Protocol
