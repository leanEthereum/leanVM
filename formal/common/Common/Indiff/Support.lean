module

public import Common.Indiff.Games

@[expose] public section

/-!
# Indifferentiability: what the combined game's steps can reach

The reachable outcomes of each step of the combined game, run in the random oracle model for
`H` and `T`, described without probabilities: every path value a step queries ends up cached,
the cache only grows, the cached value of a path (`valC`) is the value the step used, and the
rest of the step is a function of these values and of the uniform draws.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- The cache of the intermediate games' random oracles. -/
abbrev ACache (Msg Dg E C : Type) := (aSpec Msg Dg E C).QueryCache

/-- The cached value of a path, when its oracle answers are cached. -/
def valC (c : ACache Msg Dg E C) (β : List (Dg × E)) : Option (SpState Dg E C) :=
  match P.unpad β with
  | some m => (c (.inl m)).bind fun d ↦ (c (.inr β)).map fun t ↦ ((d, t.1.2), t.2)
  | none => c (.inr β)

/-- The oracle points that the value of `β` reads. -/
def ValPt (β : List (Dg × E)) : (aSpec Msg Dg E C).Domain → Prop
  | .inl m => P.unpad β = some m
  | .inr γ => γ = β

/-- Cached values stay cached. -/
theorem valC_mono {c c' : ACache Msg Dg E C} (h : c ≤ c') {β : List (Dg × E)}
    {v : SpState Dg E C} (hv : valC P c β = some v) : valC P c' β = some v := by
  unfold valC at hv ⊢
  split at hv
  · obtain ⟨d, hd, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hv
    simp [h hd, h ht]
  · exact h hv

/-- The value of a path depends only on the cache at its oracle points. -/
theorem valC_congr {c c' : ACache Msg Dg E C} (β : List (Dg × E))
    (h : ∀ t, ValPt (C := C) P β t → c t = c' t) : valC P c β = valC P c' β := by
  unfold valC
  split
  · next m hm => rw [h (.inl m) hm, h (.inr β) rfl]
  · rw [h (.inr β) rfl]

/-- A random-oracle step at a point keeps the rest of the cache. -/
theorem roStep_support {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] (t : ι) (c : hs.QueryCache)
    {z : hs.Range t × hs.QueryCache} (hz : z ∈ support (roStep t c)) :
    c ≤ z.2 ∧ z.2 t = some z.1 ∧ ∀ t', t' ≠ t → z.2 t' = c t' := by
  rcases h : c t with _ | u
  · rw [roStep_of_none h] at hz
    simp only [support_bind, support_uniformSample, Set.mem_univ, support_pure,
      Set.iUnion_true, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨u, rfl⟩ := hz
    exact ⟨QueryCache.le_cacheQuery _ h, by simp, fun t' ht' ↦ by simp [ht']⟩
  · rw [roStep_of_some h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, h, fun _ _ ↦ rfl⟩

/-- **The value step.** Querying the value of `β` caches it, keeps the cache elsewhere, and
returns the cached value. -/
theorem val_support (β : List (Dg × E)) (c : ACache Msg Dg E C)
    {z : SpState Dg E C × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl (val P β)).run c)) :
    c ≤ z.2 ∧ valC P z.2 β = some z.1 ∧ ∀ t, ¬ ValPt (C := C) P β t → z.2 t = c t := by
  unfold val at hz
  split at hz
  · next m hm =>
    simp only [simulateQ_bind, StateT.run_bind, run_hq, simulateQ_pure, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨d, c₁⟩, h₁, ⟨t, c₂⟩, h₂, rfl⟩ := hz
    obtain ⟨hc₁, hd, hc₁'⟩ := roStep_support _ c h₁
    obtain ⟨hc₂, ht, hc₂'⟩ := roStep_support _ c₁ h₂
    refine ⟨le_trans hc₁ hc₂, ?_, fun t' ht' ↦ ?_⟩
    · simp only [valC, hm]
      rw [hc₂' (.inl m) (by simp), hd, ht]
      rfl
    · simp only at ht' ⊢
      rw [hc₂' t' (by rintro rfl; exact ht' rfl), hc₁' t' (by rintro rfl; exact ht' hm)]
  · next hm =>
    rw [run_hq] at hz
    obtain ⟨hc, ht, hc'⟩ := roStep_support _ c hz
    refine ⟨hc, ?_, fun t' ht' ↦ hc' t' (by rintro rfl; exact ht' rfl)⟩
    simp only [valC, hm]
    exact ht

/-- Querying the value of a path whose value is cached returns it and changes nothing. -/
theorem val_run_of_valC (β : List (Dg × E)) (c : ACache Msg Dg E C) {v : SpState Dg E C}
    (hv : valC P c β = some v) :
    (simulateQ (aSpec Msg Dg E C).romImpl (val P β)).run c = pure (v, c) := by
  unfold valC at hv
  unfold val
  split at hv
  · next m hm =>
    obtain ⟨d, hd, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hv
    simp only [hm, simulateQ_bind, StateT.run_bind, run_hq, roStep_of_some hd, pure_bind,
      roStep_of_some ht, simulateQ_pure, StateT.run_pure]
  · next hm =>
    simp only [hm, run_hq, roStep_of_some hv]

/-- A uniform draw leaves the cache alone. -/
theorem drawSt_run (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl
      (drawSt (Msg := Msg) (Dg := Dg) (E := E) (C := C))).run c =
      (fun u ↦ (u, c)) <$> ($ᵗ (SpState Dg E C)) :=
  simulateQ_romImpl_liftM_run _ _

/-- The full view's walk as a function of the path values `vf` and the uniform draws `us`. -/
def detWalk (used : List (Dg × E) → Bool) (vf : List (Dg × E) → SpState Dg E C) :
    List (Dg × E) → SpState Dg E C → PermutationEdges (SpState Dg E C) → List (Dg × E) →
      List (SpState Dg E C) → SpState Dg E C × PermutationEdges (SpState Dg E C)
  | _, s, A, [], _ => (s, A)
  | pre, s, A, B :: bs, us =>
    match forwardLookup A (absorb s B) with
    | some y => detWalk used vf (pre ++ [B]) y A bs us.tail
    | none =>
      let y := if used (pre ++ [B]) then us.headD s else vf (pre ++ [B])
      detWalk used vf (pre ++ [B]) y ((absorb s B, y) :: A) bs us.tail

/-- **The walk step.** The walk caches the values of all paths it goes through, keeps the cache
elsewhere, and its outcome is `detWalk` over any function agreeing with the cached values. -/
theorem allWalk_support (used : List (Dg × E) → Bool) (pre : List (Dg × E))
    (s : SpState Dg E C) (A : PermutationEdges (SpState Dg E C)) (bs : List (Dg × E))
    (c : ACache Msg Dg E C)
    {z : (SpState Dg E C × PermutationEdges (SpState Dg E C)) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      (allWalk P used pre s A bs)).run c)) :
    c ≤ z.2 ∧ (∀ i < bs.length, valC P z.2 (pre ++ bs.take (i + 1)) ≠ none) ∧
      (∀ t, (∀ i < bs.length, ¬ ValPt (C := C) P (pre ++ bs.take (i + 1)) t) → z.2 t = c t) ∧
      ∃ us, ∀ vf : List (Dg × E) → SpState Dg E C,
        (∀ i < bs.length, valC P z.2 (pre ++ bs.take (i + 1)) =
          some (vf (pre ++ bs.take (i + 1)))) →
        z.1 = detWalk used vf pre s A bs us := by
  induction bs generalizing pre s A c with
  | nil =>
    simp only [allWalk, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨le_rfl, by simp, fun _ _ ↦ rfl, [], fun _ _ ↦ rfl⟩
  | cons B bs ih =>
    simp only [allWalk, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨v, c₁⟩, h₁, w₂, h₂, hz⟩ := hz
    rw [drawSt_run] at h₂
    simp only [support_map, Set.mem_image] at h₂
    obtain ⟨u, -, rfl⟩ := h₂
    obtain ⟨hc₁, hv, hc₁'⟩ := val_support P _ c h₁
    dsimp only at hc₁ hv hc₁' hz
    have key : ∀ (y : SpState Dg E C) (A' : PermutationEdges (SpState Dg E C)),
        z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
          (allWalk P used (pre ++ [B]) y A' bs)).run c₁) →
        c₁ ≤ z.2 ∧ c ≤ z.2 ∧
          (∀ i < (B :: bs).length, valC P z.2 (pre ++ (B :: bs).take (i + 1)) ≠ none) ∧
          (∀ t, (∀ i < (B :: bs).length,
            ¬ ValPt (C := C) P (pre ++ (B :: bs).take (i + 1)) t) → z.2 t = c t) ∧
          ∃ us', ∀ vf : List (Dg × E) → SpState Dg E C,
            (∀ i < (B :: bs).length, valC P z.2 (pre ++ (B :: bs).take (i + 1)) =
              some (vf (pre ++ (B :: bs).take (i + 1)))) →
            z.1 = detWalk used vf (pre ++ [B]) y A' bs us' := by
      intro y A' hz'
      obtain ⟨hc, hcached, hagree, us', hdet⟩ := ih (pre ++ [B]) y A' c₁ hz'
      refine ⟨hc, le_trans hc₁ hc, fun i hi ↦ ?_, fun t ht ↦ ?_, us', fun vf hvf ↦ hdet vf ?_⟩
      · rcases i with _ | i
        · simp [valC_mono P hc hv]
        · have := hcached i (by simp at hi; omega)
          simpa [List.take_succ_cons] using this
      · rw [hagree t fun i hi ↦ ?_, hc₁' t (by simpa using ht 0 (by simp))]
        simpa [List.take_succ_cons] using ht (i + 1) (by simp; omega)
      · intro i hi
        simpa [List.take_succ_cons] using hvf (i + 1) (by simp; omega)
    split at hz
    · next y hy =>
      obtain ⟨-, hc, hcached, hagree, us', hdet⟩ := key y A hz
      refine ⟨hc, hcached, hagree, u :: us', fun vf hvf ↦ ?_⟩
      simp only [detWalk, hy, List.tail_cons]
      exact hdet vf hvf
    · next hy =>
      obtain ⟨hc₁z, hc, hcached, hagree, us', hdet⟩ := key _ _ hz
      refine ⟨hc, hcached, hagree, u :: us', fun vf hvf ↦ ?_⟩
      have hvB : v = vf (pre ++ [B]) := by
        have h0 := hvf 0 (by simp)
        simp only [List.take_succ_cons, List.take_zero] at h0
        rw [valC_mono P hc₁z hv] at h0
        exact Option.some.inj h0
      simp only [detWalk, hy, List.tail_cons, List.headD_cons]
      rw [← hvB]
      exact hdet vf hvf

/-- **The forward step of the simulator over path values.** Either `x` is recorded, or it is a
fresh rooted node whose path value is queried, or a fresh unrooted node answered with `u`. -/
theorem visFwd_support (x u : SpState Dg E C) (σ : SimState Dg E C) (c : ACache Msg Dg E C)
    {z : (SpState Dg E C × SimState Dg E C × Option (List (Dg × E) × SpState Dg E C)) ×
      ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl (visFwd P x u σ)).run c)) :
    (∃ y, forwardLookup σ.edges x = some y ∧ z = ((y, σ, none), c)) ∨
    (∃ s β, forwardLookup σ.edges x = none ∧ chainOf σ.chains x = some (s, β) ∧
      (z.1.1, z.2) ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
        (val P (β ++ [blockTo s x]))).run c) ∧
      z.1 = (z.1.1, ⟨(x, z.1.1) :: σ.edges, (z.1.1, β ++ [blockTo s x]) :: σ.chains⟩,
        some (β ++ [blockTo s x], z.1.1))) ∨
    (forwardLookup σ.edges x = none ∧ chainOf σ.chains x = none ∧
      z = ((u, ⟨(x, u) :: σ.edges, σ.chains⟩, none), c)) := by
  unfold visFwd at hz
  split at hz
  · next y hy =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    exact Or.inl ⟨y, hy, hz⟩
  · next hy =>
    split at hz
    · next s β hch =>
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨v, c'⟩, hv, rfl⟩ := hz
      exact Or.inr (Or.inl ⟨s, β, hy, hch, hv, rfl⟩)
    · next hch =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      exact Or.inr (Or.inr ⟨hy, hch, hz⟩)

/-- The combined forward step's reachable outcomes. -/
theorem combFwd_support (x : SpState Dg E C) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C)
    {z : ((SpState Dg E C × SpState Dg E C) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combFwd P iv x).run cs)).run c)) :
    ∃ u r, (r, z.2) ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      (visFwd P x u cs.sim)).run c) ∧ z.1 = fwdOut P iv cs x u r := by
  simp only [combFwd, StateT.run_mk, simulateQ_bind, StateT.run_bind, drawSt_run,
    simulateQ_pure, StateT.run_pure, bind_map_left, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, support_uniformSample, Set.mem_univ, true_and] at hz
  obtain ⟨u, ⟨r, c'⟩, hr, rfl⟩ := hz
  exact ⟨u, r, hr, rfl⟩

/-- The combined inverse step's reachable outcomes. -/
theorem combInv_support (y : SpState Dg E C) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C)
    {z : ((SpState Dg E C × SpState Dg E C) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combInv iv y).run cs)).run c)) :
    ∃ u, z = (invOut iv cs y u, c) := by
  simp only [combInv, StateT.run_mk, simulateQ_bind, StateT.run_bind, drawSt_run,
    simulateQ_pure, StateT.run_pure, bind_map_left, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨u, -, rfl⟩ := hz
  exact ⟨u, rfl⟩

/-- The combined hash step's reachable outcomes. -/
theorem combHash_support (m : Msg) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C)
    {z : ((Dg × Dg) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combHash P iv m).run cs)).run c)) :
    ∃ w c₁ d, (w, c₁) ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      (allWalk P (usedPath P cs.sim.chains cs.hashed) [] iv cs.all (P.pad m))).run c) ∧
      (d, z.2) ∈ support (roStep (hs := aSpec Msg Dg E C) (.inl m) c₁) ∧
      z.1 = hashOut cs m w d := by
  simp only [combHash, StateT.run_mk, simulateQ_bind, StateT.run_bind, run_hq,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨⟨w, c₁⟩, hw, ⟨d, c₂⟩, hd, rfl⟩ := hz
  exact ⟨w, c₁, d, hw, hd, rfl⟩

end Setting

end Common
