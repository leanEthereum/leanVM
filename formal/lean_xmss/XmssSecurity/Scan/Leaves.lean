import XmssSecurity.Scan.Ghost
import XmssSecurity.Scan.Step

/-!
# Per-leaf bookkeeping of the adversary phase

A leaf index is signed once the trace has an entry at it; its first entry's initial cache is its
frozen cache. `dec` reads an encoding input back as its leaf index and position. The lemmas here say
how one oracle answer or one signing request moves the caches the potentials read.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Ghost

open Partner

/-- The first trace entry at a leaf index. -/
def first (trace : SigningCacheTrace) (leafIndex : LeafIndex) : Option SigningCacheEntry :=
  trace.find? fun entry => entry.request.leafIndex = leafIndex

theorem first_some {trace : SigningCacheTrace} {leafIndex : LeafIndex} {entry : SigningCacheEntry}
    (h : first trace leafIndex = some entry) : entry ∈ trace ∧ entry.request.leafIndex = leafIndex :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem first_append_of_some {trace : SigningCacheTrace} {leafIndex : LeafIndex}
    {entry : SigningCacheEntry} (h : first trace leafIndex = some entry) (rest : SigningCacheTrace) :
    first (trace ++ rest) leafIndex = some entry := by
  simp only [first, List.find?_append] at h ⊢
  rw [h]; rfl

theorem first_append_of_ne {trace : SigningCacheTrace} {leafIndex : LeafIndex}
    (entry : SigningCacheEntry) (h : entry.request.leafIndex ≠ leafIndex) :
    first (trace ++ [entry]) leafIndex = first trace leafIndex := by
  simp only [first, List.find?_append, List.find?_singleton]
  simp [h]

theorem first_append_self {trace : SigningCacheTrace} (entry : SigningCacheEntry) :
    first (trace ++ [entry]) entry.request.leafIndex ≠ none := by
  simp [first, List.find?_append]

theorem first_eq_none_iff {trace : SigningCacheTrace} {leafIndex : LeafIndex} :
    first trace leafIndex = none ↔ leafIndex ∉ trace.leafIndices := by
  simp [first, SigningCacheTrace.leafIndices]

theorem first_of_nodup {trace : SigningCacheTrace} (hnodup : trace.leafIndices.Nodup)
    {entry : SigningCacheEntry} (hentry : entry ∈ trace) :
    first trace entry.request.leafIndex = some entry := by
  cases h : first trace entry.request.leafIndex with
  | none =>
      exact absurd (List.mem_map.mpr ⟨entry, hentry, rfl⟩) (first_eq_none_iff.mp h)
  | some other =>
      obtain ⟨hother, hleaf⟩ := first_some h
      rw [List.inj_on_of_nodup_map (by simpa [SigningCacheTrace.leafIndices] using hnodup)
        hother hentry hleaf]

/-- The cache a leaf index's potentials read: its first entry's initial cache once signed. -/
def frozen (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (leafIndex : LeafIndex) :
    QueryCache HashSpec :=
  ((first trace leafIndex).map SigningCacheEntry.initialCache).getD cache

theorem frozen_of_none {cache : QueryCache HashSpec} {trace : SigningCacheTrace} {leafIndex : LeafIndex}
    (h : first trace leafIndex = none) : frozen cache trace leafIndex = cache := by
  simp [frozen, h]

theorem frozen_of_some {cache : QueryCache HashSpec} {trace : SigningCacheTrace} {leafIndex : LeafIndex}
    {entry : SigningCacheEntry} (h : first trace leafIndex = some entry) :
    frozen cache trace leafIndex = entry.initialCache := by
  simp [frozen, h]

variable (parameter : PublicParameter)

theorem input_ne_of_ne {leafIndex other : LeafIndex} (h : leafIndex ≠ other) (y z : Position) :
    input parameter leafIndex y ≠ input parameter other z := fun he =>
  h (Concrete.CacheView.leafIndex_eq_of_encodingInput_eq parameter he)

/-- An encoding input's leaf index and position. -/
noncomputable def dec (x : HashInput) : Option (LeafIndex × Position) :=
  if h : ∃ p : LeafIndex × Position, input parameter p.1 p.2 = x then some h.choose else none

theorem dec_input (leafIndex : LeafIndex) (y : Position) :
    dec parameter (input parameter leafIndex y) = some (leafIndex, y) := by
  have h : ∃ p : LeafIndex × Position, input parameter p.1 p.2 = input parameter leafIndex y :=
    ⟨(leafIndex, y), rfl⟩
  rw [dec, dite_eq_left h]
  have hspec := h.choose_spec
  have hleaf := Concrete.CacheView.leafIndex_eq_of_encodingInput_eq parameter hspec
  rw [hleaf] at hspec
  have hy := input_injective parameter leafIndex hspec
  rw [Option.some.injEq]
  exact Prod.ext hleaf hy

theorem dec_eq_some {x : HashInput} {p : LeafIndex × Position} (h : dec parameter x = some p) :
    x = input parameter p.1 p.2 := by
  unfold dec at h
  split at h
  · rename_i hx
    rw [← Option.some.inj h]
    exact hx.choose_spec.symm
  · cases h

theorem dec_eq_none {x : HashInput} (h : dec parameter x = none) (leafIndex : LeafIndex) (y : Position) :
    x ≠ input parameter leafIndex y := by
  rintro rfl
  rw [dec_input] at h
  cases h

variable {parameter}

/-- A query at `x` leaves the frozen cache of a leaf index that is signed or does not own `x`. -/
theorem frozen_cacheQuery_agree {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {x : HashInput} (u : HashOutput) {leafIndex : LeafIndex}
    (h : first trace leafIndex ≠ none ∨ ∀ y, x ≠ input parameter leafIndex y) (y : Position) :
    frozen (cache.cacheQuery x u) trace leafIndex (input parameter leafIndex y) =
      frozen cache trace leafIndex (input parameter leafIndex y) := by
  cases hf : first trace leafIndex with
  | some entry => rw [frozen_of_some hf, frozen_of_some hf]
  | none =>
      rw [frozen_of_none hf, frozen_of_none hf]
      exact QueryCache.cacheQuery_of_ne _ _ fun he =>
        (h.resolve_left (by simpa using hf)) y he.symm

/-! ### The oracle on one query -/

theorem romImpl_expect_unif (n : ℕ) (cache : QueryCache HashSpec) (G : QueryCache HashSpec → ℝ≥0∞) :
    ∑' r, Pr{let x ← (romImpl (.inl n)).run cache}[x = r] * G r.2 = G cache := by
  have hrun : (unifFwdImpl HashSpec n).run cache =
      (fun sample => (sample, cache)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run (hashSpec := HashSpec) (liftM (unifSpec.query n) : ProbComp _) cache)
  change ∑' r, Pr{let x ← (unifFwdImpl HashSpec n).run cache}[x = r] * G r.2 = G cache
  rw [hrun, OracleComp.tsum_prEvent_map_mul]
  exact OracleComp.tsum_prEvent_mul_of_const_on_support _ (fun _ _ => rfl)

theorem romImpl_expect_cached {x : HashInput} {cache : QueryCache HashSpec} {o : HashOutput}
    (hx : cache x = some o) (G : QueryCache HashSpec → ℝ≥0∞) :
    ∑' r, Pr{let y ← (romImpl (.inr x)).run cache}[y = r] * G r.2 = G cache := by
  change ∑' r, Pr{let y ← (randomOracle (spec := HashSpec) x).run cache}[y = r] * G r.2 = G cache
  rw [randomOracle, QueryImpl.withCaching_run_some _ hx, OracleComp.tsum_prEvent_pure_mul]

theorem romImpl_expect_fresh {x : HashInput} {cache : QueryCache HashSpec} (hx : cache x = none)
    (G : QueryCache HashSpec → ℝ≥0∞) :
    ∑' r, Pr{let y ← (romImpl (.inr x)).run cache}[y = r] * G r.2 = ex fun u : HashOutput => G (cache.cacheQuery x u) := by
  change ∑' r, Pr{let y ← (randomOracle (spec := HashSpec) x).run cache}[y = r] * G r.2 = _
  rw [randomOracle_run_none_eq_uniformHashOutput _ _ hx, OracleComp.tsum_prEvent_map_mul, tsum_fintype, ex]
  rfl

theorem romImpl_support_unif {n : ℕ} {cache : QueryCache HashSpec} {r}
    (hr : r ∈ support ((romImpl (.inl n)).run cache)) : r.2 = cache := by
  have hrun : (unifFwdImpl HashSpec n).run cache =
      (fun sample => (sample, cache)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run (hashSpec := HashSpec) (liftM (unifSpec.query n) : ProbComp _) cache)
  change r ∈ support ((unifFwdImpl HashSpec n).run cache) at hr
  rw [hrun, support_map] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

theorem romImpl_support_cached {x : HashInput} {cache : QueryCache HashSpec} {o : HashOutput}
    (hx : cache x = some o) {r} (hr : r ∈ support ((romImpl (.inr x)).run cache)) : r.2 = cache := by
  change r ∈ support ((randomOracle (spec := HashSpec) x).run cache) at hr
  rw [randomOracle, QueryImpl.withCaching_run_some _ hx, support_pure] at hr
  rw [hr]

theorem romImpl_support_fresh {x : HashInput} {cache : QueryCache HashSpec} (hx : cache x = none) {r}
    (hr : r ∈ support ((romImpl (.inr x)).run cache)) : r.2 = cache.cacheQuery x r.1 := by
  change r ∈ support ((randomOracle (spec := HashSpec) x).run cache) at hr
  rw [randomOracle_run_none_eq_uniformHashOutput _ _ hx, support_map] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

/-! ### Signing -/

variable (secretKey : SecretKey)

/-- The signer changes no other leaf index's encoding inputs. -/
theorem sign_other_leaf {leafIndex other : LeafIndex} {message : Message} {cache : QueryCache HashSpec}
    {r : Option Signature × QueryCache HashSpec}
    (hr : r ∈ support ((simulateQ romImpl (Concrete.scheme.sign secretKey leafIndex message)).run cache))
    (hne : leafIndex ≠ other) (y : Position) :
    r.2 (input secretKey.parameter other y) = cache (input secretKey.parameter other y) := by
  cases hc : cache (input secretKey.parameter other y) with
  | none =>
      exact Concrete.precomputedCappedSign_preserves_other_leafIndex_encodingInput secretKey leafIndex
        other message y cache r.2 r.1 hr hne hc
  | some o => exact xmssRom_cache_le _ cache r hr hc

/-- A signature selects an input whose cached digest is valid. -/
theorem sign_selected_valid {leafIndex : LeafIndex} {message : Message} {cache : QueryCache HashSpec}
    {r : Option Signature × QueryCache HashSpec}
    (hr : r ∈ support ((simulateQ romImpl (Concrete.scheme.sign secretKey leafIndex message)).run cache))
    {signature : Signature} (hs : r.1 = some signature) {o : HashOutput}
    (ho : cache (input secretKey.parameter leafIndex (message, signature.randomness)) = some o) :
    TargetSum.ValidDigest (truncateHash o) := by
  obtain ⟨result, final⟩ := r
  simp only at hs
  subst hs
  obtain ⟨encoding, hdecode⟩ := Concrete.precomputedCappedSign_success_decode secretKey ⟨leafIndex, message⟩
    cache final signature hr
  have hfinal : final (input secretKey.parameter leafIndex (message, signature.randomness)) = some o :=
    xmssRom_cache_le _ cache _ hr ho
  have hfinal' : final (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
      (message, signature.randomness)) = some o := hfinal
  unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt at hdecode
  rw [hfinal'] at hdecode
  exact ⟨encoding, hdecode⟩

/-- After a signing request at `leafIndex`, every leaf index reads the same frozen cache. -/
theorem frozen_sign_agree {request : SignRequest} {cache : QueryCache HashSpec}
    {trace : SigningCacheTrace} {r : Option Signature × QueryCache HashSpec}
    (hr : r ∈ support ((simulateQ romImpl (Concrete.scheme.sign secretKey request.leafIndex
      request.message)).run cache)) (leafIndex : LeafIndex) (y : Position) :
    frozen r.2 (trace ++ [⟨request, r.1, cache, r.2⟩]) leafIndex (input secretKey.parameter leafIndex y) =
      frozen cache trace leafIndex (input secretKey.parameter leafIndex y) := by
  cases hf : first trace leafIndex with
  | some entry => rw [frozen_of_some hf, frozen_of_some (first_append_of_some hf _)]
  | none =>
      rw [frozen_of_none hf]
      by_cases hleaf : request.leafIndex = leafIndex
      · subst hleaf
        have hnew : first (trace ++ [⟨request, r.1, cache, r.2⟩]) request.leafIndex =
            some ⟨request, r.1, cache, r.2⟩ := by
          unfold first at hf ⊢
          rw [List.find?_append, hf]
          simp
        rw [frozen_of_some hnew]
      · rw [frozen_of_none ((first_append_of_ne _ hleaf).trans hf)]
        exact sign_other_leaf secretKey hr hleaf y

end XmssSecurity.Ghost
