module

public import Common.Indiff.Perm

@[expose] public section

/-!
# Indifferentiability: the collision bound

In the visible game without path queries, followed by the end phase (`visRun P iv false`),
both collisions are unlikely:

* a **visible collision** needs a fresh simulator draw — a uniform state, or the value of a fresh
  rooted path, whose capacity is a fresh uniform draw from the path oracle — to land on one of
  the at most `2q + 1` visible capacities: at most `(2q + 1) / |C|` per permutation query
  (`prEvent_vis_bad_le`);
* a **hidden collision** needs one of the hidden paths' values, all drawn fresh in the end phase,
  to land on a visible capacity or on another hidden value's capacity (`prEvent_coll_endPhase`).

Together: probability at most `(3q² + 2q) / |C|` for a distinguisher of cost `q`
(`prEvent_visRun_le`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-! ## Collisions among path-oracle answers -/

/-- A capacity collision among the path oracle's answers at the paths `H`: an answer at a path of
`H` has a capacity in `K`, or the capacity of the answer at another path of `H`. -/
def Coll (H : Finset (List (Dg × E))) (K : List C) (c : ACache Msg Dg E C) : Prop :=
  ∃ β ∈ H, ∃ t, c (.inr β) = some t ∧
    (t.2 ∈ K ∨ ∃ γ ∈ H, γ ≠ β ∧ ∃ t', c (.inr γ) = some t' ∧ t'.2 = t.2)

/-- The capacities of the path oracle's cached answers at the paths `H`. -/
noncomputable def collCaps (H : Finset (List (Dg × E))) (c : ACache Msg Dg E C) : List C :=
  H.toList.filterMap fun γ ↦ (c (.inr γ)).map Prod.snd

theorem length_collCaps_le (H : Finset (List (Dg × E))) (c : ACache Msg Dg E C) :
    (collCaps H c).length ≤ H.card := by
  unfold collCaps
  exact (List.length_filterMap_le _ _).trans (by simp)

/-- A collision after recording a fresh answer is an old collision, or the fresh answer's
capacity among the visible and the cached capacities. -/
theorem coll_cacheQuery {H : Finset (List (Dg × E))} {K : List C} {c : ACache Msg Dg E C}
    {β : List (Dg × E)} (hβ : c (.inr β) = none) (t : SpState Dg E C)
    (h : Coll H K (c.cacheQuery (.inr β) t)) :
    Coll H K c ∨ t.2 ∈ K ++ collCaps H c := by
  obtain ⟨γ, hγ, t₀, ht₀, hcol⟩ := h
  by_cases hγβ : γ = β
  · subst hγβ
    rw [QueryCache.cacheQuery_self] at ht₀
    obtain rfl := Option.some.inj ht₀
    right
    rcases hcol with h | ⟨δ, hδ, hne, t', ht', heq⟩
    · exact List.mem_append_left _ h
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hne)] at ht'
      refine List.mem_append_right _ ?_
      rw [← heq]
      simp only [collCaps, List.mem_filterMap, Finset.mem_toList, Option.map_eq_some_iff]
      exact ⟨δ, hδ, t', ht', rfl⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hγβ)] at ht₀
    rcases hcol with h | ⟨δ, hδ, hne, t', ht', heq⟩
    · exact Or.inl ⟨γ, hγ, t₀, ht₀, Or.inl h⟩
    · by_cases hδβ : δ = β
      · subst hδβ
        rw [QueryCache.cacheQuery_self] at ht'
        obtain rfl := Option.some.inj ht'
        right
        refine List.mem_append_right _ ?_
        rw [heq]
        simp only [collCaps, List.mem_filterMap, Finset.mem_toList, Option.map_eq_some_iff]
        exact ⟨γ, hγ, t₀, ht₀, rfl⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hδβ)] at ht'
        exact Or.inl ⟨γ, hγ, t₀, ht₀, Or.inr ⟨δ, hδ, hne, t', ht', heq⟩⟩

/-- Collisions only read the path oracle's answers. -/
theorem coll_congr {H : Finset (List (Dg × E))} {K : List C} {c c' : ACache Msg Dg E C}
    (h : ∀ β, c' (.inr β) = c (.inr β)) : Coll H K c' ↔ Coll H K c := by
  simp only [Coll, h]

/-- A uniform state's capacity lands in a list of capacities with probability at most its length
over `|C|`. -/
theorem prEvent_cap_mem_le (L : List C) :
    Pr{let t ← $ᵗ (SpState Dg E C)}[t.2 ∈ L] ≤ L.length / (Fintype.card C : ℝ≥0∞) :=
  SampleableType.prEvent_uniformSample_prod_le_of_forall_fst (fun t : SpState Dg E C ↦ t.2 ∈ L)
    fun _ ↦ prEvent_uniform_mem_le L

/-- **A path value creates a collision with probability at most `(|K| + |H|) / |C|`.** -/
theorem prEvent_coll_val (H : Finset (List (Dg × E))) (K : List C) (β : List (Dg × E))
    (c : ACache Msg Dg E C) (hc : ¬ Coll H K c) :
    Pr{let z ← (simulateQ (aSpec Msg Dg E C).romImpl (val P β)).run c}[Coll H K z.2] ≤
      (K.length + H.card) / (Fintype.card C : ℝ≥0∞) := by
  -- the random-oracle part of the value does not touch the path oracle's answers
  have hro : ∀ m, ∀ w ∈ support (roStep (hs := aSpec Msg Dg E C) (.inl m) c), ¬ Coll H K w.2 ∧
      (∀ β, w.2 (.inr β) = c (.inr β)) := by
    intro m w hw
    obtain ⟨-, -, hagree⟩ := roStep_support _ c hw
    have h : ∀ β, w.2 (.inr β) = c (.inr β) := fun β ↦ hagree _ (by simp)
    exact ⟨(coll_congr h).not.mpr hc, h⟩
  -- the path-oracle step
  have hT : ∀ c' : ACache Msg Dg E C, ¬ Coll H K c' → (∀ β, c' (.inr β) = c (.inr β)) →
      Pr{let z ← roStep (hs := aSpec Msg Dg E C) (.inr β) c'}[Coll H K z.2] ≤
        (K.length + H.card) / (Fintype.card C : ℝ≥0∞) := by
    intro c' hc' hagree
    rcases h : c' (.inr β) with _ | t
    · rw [roStep_of_none h, bind_pure_comp, prEvent_map]
      change Pr{let t ← $ᵗ (SpState Dg E C)}[Coll H K (c'.cacheQuery (.inr β) t)] ≤ _
      calc Pr{let t ← $ᵗ (SpState Dg E C)}[Coll H K (c'.cacheQuery (.inr β) t)]
          ≤ Pr{let t ← $ᵗ (SpState Dg E C)}[t.2 ∈ K ++ collCaps H c'] :=
            prEvent_mono _ _ _ fun t ht ↦ (coll_cacheQuery h t ht).resolve_left hc'
        _ ≤ (K ++ collCaps H c').length / (Fintype.card C : ℝ≥0∞) := prEvent_cap_mem_le _
        _ ≤ (K.length + H.card) / (Fintype.card C : ℝ≥0∞) := by
            gcongr
            rw [List.length_append]
            exact_mod_cast Nat.add_le_add_left (length_collCaps_le H c') _
    · rw [roStep_of_some h]
      simp [hc']
  unfold val
  split
  · next m hm =>
    simp only [simulateQ_bind, StateT.run_bind, run_hq, simulateQ_pure, StateT.run_pure]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun w hw ↦ ?_
    obtain ⟨hw1, hw2⟩ := hro m w hw
    simp only [bind_pure_comp, prEvent_map]
    exact hT w.2 hw1 hw2
  · rw [run_hq]
    exact hT c hc fun _ ↦ rfl

/-- The sponge's path queries create a collision with probability at most `(|K| + |H|) / |C|` per
block. -/
theorem prEvent_coll_skel (H : Finset (List (Dg × E))) (K : List C) (pre bs : List (Dg × E))
    (c : ACache Msg Dg E C) (hc : ¬ Coll H K c) :
    Pr{let z ← (simulateQ (aSpec Msg Dg E C).romImpl (skel (C := C) P pre bs)).run c}[
      Coll H K z.2] ≤ bs.length * ((K.length + H.card) / (Fintype.card C : ℝ≥0∞)) := by
  induction bs generalizing pre c with
  | nil => simp [skel, hc]
  | cons B bs ih =>
    simp only [skel, simulateQ_bind, StateT.run_bind]
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun w ↦ Coll H K w.2) _
      (ε := bs.length * ((K.length + H.card) / (Fintype.card C : ℝ≥0∞)))
      fun w _ hw ↦ ?_).trans ?_
    · rw [drawSt_run, bind_map_left]
      exact prEvent_bind_le_of_forall_le _ _ _ fun u ↦ ih _ w.2 hw
    · rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_one_mul, add_comm]
      gcongr
      exact prEvent_coll_val P H K _ c hc

/-- The end phase creates a collision with probability at most `(|K| + |H|) / |C|` per block of
the hashed messages. -/
theorem prEvent_coll_endPhase (H : Finset (List (Dg × E))) (K : List C) (ms : List Msg)
    (c : ACache Msg Dg E C) (hc : ¬ Coll H K c) :
    Pr{let z ← (simulateQ (aSpec Msg Dg E C).romImpl (endPhase (C := C) P ms)).run c}[
      Coll H K z.2] ≤
      (ms.map fun m ↦ (P.pad m).length).sum * ((K.length + H.card) / (Fintype.card C : ℝ≥0∞)) := by
  induction ms generalizing c with
  | nil => simp [endPhase, hc]
  | cons m ms ih =>
    simp only [endPhase, simulateQ_bind, StateT.run_bind]
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun w ↦ Coll H K w.2) _
      (ε := (ms.map fun m ↦ (P.pad m).length).sum *
        ((K.length + H.card) / (Fintype.card C : ℝ≥0∞)))
      fun w _ hw ↦ ih w.2 hw).trans ?_
    rw [List.map_cons, List.sum_cons, Nat.cast_add, add_mul]
    gcongr
    simpa using prEvent_coll_skel P H K [] (P.pad m) c hc

/-! ## The visible game without path queries -/

/-- The visible game without path queries, with the random oracles' cache in the state. -/
noncomputable abbrev visF : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (VState Dg E C Msg × ACache Msg Dg E C) ProbComp) :=
  foldRO (visImpl P iv false)

/-- The reachable outcomes of a visible step without path queries. -/
theorem visImpl_false_support (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (vs : VState Dg E C Msg) {z} (hz : z ∈ support ((visImpl P iv false t).run vs)) :
    (z.2.2.1 = (match t with | .inr (.inl m) => m :: vs.2.1 | _ => vs.2.1)) ∧
    (z.2.1.edges.length ≤ vs.1.edges.length + (match t with | .inr (.inr _) => 1 | _ => 0)) ∧
    (z.2.2.2 = true → vs.2.2 = false → ∃ q, t = .inr (.inr q)) := by
  rcases t with n | m | x | y
  · simp only [visImpl] at hz
    rw [StateT.run_monadLift] at hz
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨rfl, by simp, fun h h' ↦ by simp_all⟩
  · simp only [visImpl, StateT.run_mk, Bool.false_eq_true, ↓reduceIte,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨d, -, rfl⟩ := hz
    exact ⟨rfl, by simp, fun h h' ↦ by simp_all⟩
  · simp only [visImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, r, hr, rfl⟩ := hz
    refine ⟨rfl, ?_, fun _ _ ↦ ⟨_, rfl⟩⟩
    unfold visFwd at hr
    split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; simp
    · split at hr
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
        obtain ⟨v, -, rfl⟩ := hr; simp
      · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; simp
  · simp only [visImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    refine ⟨rfl, ?_, fun _ _ ↦ ⟨_, rfl⟩⟩
    simp only [visInv]; split <;> simp

/-- The reachable outcomes of a folded visible step come from the unfolded step. -/
theorem visF_support (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : VState Dg E C Msg × ACache Msg Dg E C) {z} (hz : z ∈ support ((visF P iv t).run s)) :
    ∃ w ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl ((visImpl P iv false t).run s.1)).run
      s.2), z = (w.1.1, (w.1.2, w.2)) := by
  rw [visF, foldRO_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- The bookkeeping of the simulator holds along the visible game without path queries. -/
theorem vStruct_visF (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : VState Dg E C Msg × ACache Msg Dg E C) (hs : VStruct P iv s.1.1 s.2) {z}
    (hz : z ∈ support ((visF P iv t).run s)) : VStruct P iv z.2.1.1 z.2.2 := by
  obtain ⟨w, hw, rfl⟩ := visF_support P iv t s hz
  have h := visImpl_false_proj P iv t s.1
  have hw' : ((w.1.1, w.1.2.1), w.2) ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((idealTImpl P t).run s.1.1)).run s.2) := by
    rw [← h, simulateQ_map, StateT.run_map, support_map]
    exact ⟨w, hw, rfl⟩
  exact vStruct_idealT t hs hw'

/-- The size of a visible state: its simulator edges and the blocks of its hashed messages. -/
def vsize (vs : VState Dg E C Msg) : ℕ :=
  vs.1.edges.length + (vs.2.1.map fun m ↦ (P.pad m).length).sum

/-- A visible step raises the size by at most its cost. -/
theorem vsize_visF (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : VState Dg E C Msg × ACache Msg Dg E C) {z} (hz : z ∈ support ((visF P iv t).run s)) :
    vsize P z.2.1 ≤ vsize P s.1 + queryCost (Dg := Dg) P t := by
  obtain ⟨w, hw, rfl⟩ := visF_support P iv t s hz
  obtain ⟨h1, h2, -⟩ := visImpl_false_support P iv t s.1 (fst_mem_support_of_mem_support_run hw)
  rcases t with n | m | q
  · simp only [vsize, queryCost] at h1 h2 ⊢
    rw [h1]; omega
  · simp only [vsize, queryCost] at h1 h2 ⊢
    rw [h1, List.map_cons, List.sum_cons]; omega
  · simp only [vsize, queryCost] at h1 h2 ⊢
    rw [h1]; omega

/-- A fresh path value's capacity lands in a list with probability at most its length over
`|C|`. -/
theorem prEvent_val_cap_le (β : List (Dg × E)) (c : ACache Msg Dg E C) (h : c (.inr β) = none)
    (L : List C) :
    Pr{let w ← (simulateQ (aSpec Msg Dg E C).romImpl (val P β)).run c}[w.1.2 ∈ L] ≤
      L.length / (Fintype.card C : ℝ≥0∞) := by
  rcases hm : P.unpad β with _ | m
  · rw [val_run_fresh_none P hm c h, bind_pure_comp, prEvent_map]
    exact prEvent_cap_mem_le L
  · rw [val_run_fresh_some P hm c h]
    refine prEvent_bind_le_of_forall_le _ _ _ fun w ↦ ?_
    rw [bind_pure_comp, prEvent_map]
    exact prEvent_cap_mem_le L

/-- The run of a visible forward step without path queries. -/
theorem visImpl_false_fwd_run (x : SpState Dg E C) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl ((visImpl P iv false (.inr (.inr (.forward x)))).run vs)).run
      c = ($ᵗ (SpState Dg E C)) >>= fun u ↦ (fun w ↦ ((w.1.1, (w.1.2.1, vs.2.1, vs.2.2 ||
        ((forwardLookup vs.1.edges x).isNone && decide (w.1.1.2 ∈ knownC iv vs.1)))), w.2)) <$>
        (simulateQ (aSpec Msg Dg E C).romImpl (visFwd P x u vs.1)).run c := by
  simp only [visImpl, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind, drawSt_run]
  simp

/-- The run of a visible inverse step without path queries. -/
theorem visImpl_false_inv_run (y : SpState Dg E C) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl ((visImpl P iv false (.inr (.inr (.inverse y)))).run vs)).run
      c = (fun u ↦ (((visInv y u vs.1).1, ((visInv y u vs.1).2, vs.2.1, vs.2.2 ||
        ((inverseLookup vs.1.edges y).isNone && decide (u.2 ∈ knownC iv vs.1)))), c)) <$>
        ($ᵗ (SpState Dg E C)) := by
  simp only [visImpl, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind, drawSt_run]
  simp

/-- **A visible collision per step.** A visible step without path queries raises the collision
flag with probability at most its cost times the number of visible capacities over `|C|`. -/
theorem prEvent_visF_bad_le (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : VState Dg E C Msg × ACache Msg Dg E C) (hV : VStruct P iv s.1.1 s.2)
    (hb : ¬ s.1.2.2 = true) :
    Pr{let z ← (visF P iv t).run s}[z.2.1.2.2 = true] ≤
      queryCost (Dg := Dg) P t * ((knownC iv s.1.1).length / (Fintype.card C : ℝ≥0∞)) := by
  rcases t with n | m | q
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
    · exact zero_le
    · obtain ⟨w, hw, rfl⟩ := visF_support P iv _ s hz
      obtain ⟨-, -, h3⟩ := visImpl_false_support P iv _ s.1
        (fst_mem_support_of_mem_support_run hw)
      obtain ⟨q, hq⟩ := h3 h (by simpa using hb)
      simp at hq
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
    · exact zero_le
    · obtain ⟨w, hw, rfl⟩ := visF_support P iv _ s hz
      obtain ⟨-, -, h3⟩ := visImpl_false_support P iv _ s.1
        (fst_mem_support_of_mem_support_run hw)
      obtain ⟨q, hq⟩ := h3 h (by simpa using hb)
      simp at hq
  · simp only [queryCost, Nat.cast_one, one_mul]
    simp only [Bool.not_eq_true] at hb
    rw [visF, foldRO_run, prEvent_map]
    cases q with
    | forward x =>
      rw [visImpl_false_fwd_run]
      rcases hy : forwardLookup s.1.1.edges x with _ | y
      · rcases hch : chainOf s.1.1.chains x with _ | ⟨σ₀, β⟩
        · simp only [visFwd, hy, hch, simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp,
            prEvent_map]
          refine (prEvent_mono _ _ _ fun u hu ↦ ?_).trans (prEvent_cap_mem_le (knownC iv s.1.1))
          simpa [hb] using hu
        · simp only [visFwd_run_rooted P hy hch, Functor.map_map]
          refine prEvent_bind_le_of_forall_le _ _ _ fun u ↦ ?_
          rw [prEvent_map]
          refine (prEvent_mono _ _ _ fun w hw ↦ ?_).trans (prEvent_val_cap_le P _ s.2
            (by by_contra h'; exact rootedPath_notMem hV hy hch (hV.tFresh _ h')) _)
          simpa [hb] using hw
      · simp only [visFwd, hy, simulateQ_pure, StateT.run_pure, map_pure]
        rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
        · exact zero_le
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨u, -, rfl⟩ := hz
          simp [hb] at h
    | inverse y =>
      rw [visImpl_false_inv_run, prEvent_map]
      refine (prEvent_mono _ _ _ fun u hu ↦ ?_).trans (prEvent_cap_mem_le (knownC iv s.1.1))
      simp only [hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hu
      exact hu.2

/-! ## The collision bound -/

/-- The hidden paths of a visible state. -/
noncomputable def hiddenSet (vs : VState Dg E C Msg) : Finset (List (Dg × E)) :=
  ((hPaths P vs.2.1).filter fun β ↦ β ∉ vPaths vs.1).toFinset

theorem mem_hiddenSet {vs : VState Dg E C Msg} {β : List (Dg × E)} :
    β ∈ hiddenSet P vs ↔ Hidden P vs β := by
  simp [hiddenSet, Hidden]

theorem card_hiddenSet_le (vs : VState Dg E C Msg) :
    (hiddenSet P vs).card ≤ (vs.2.1.map fun m ↦ (P.pad m).length).sum := by
  unfold hiddenSet
  refine (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans (le_of_eq ?_))
  simp only [hPaths, List.length_flatMap, prefixesOf, List.length_map, List.length_range]

theorem length_knownC (σ : SimState Dg E C) : (knownC iv σ).length = 2 * σ.edges.length + 1 := by
  simp only [knownC, List.length_cons, List.length_flatMap, List.length_cons, List.length_nil]
  induction σ.edges with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

/-- The capacity of a cached path value is the path oracle's answer's. -/
theorem valC_cap {c : ACache Msg Dg E C} {β : List (Dg × E)} {v : SpState Dg E C}
    (h : valC P c β = some v) : ∃ t, c (.inr β) = some t ∧ t.2 = v.2 := by
  unfold valC at h
  split at h
  · obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨t, ht, rfl⟩
  · exact ⟨v, h, rfl⟩

/-- A hidden collision is a collision among the path oracle's answers at hidden paths. -/
theorem coll_of_EC {vs : VState Dg E C Msg} {c : ACache Msg Dg E C} (h : EC P iv vs c) :
    Coll (hiddenSet P vs) (knownC iv vs.1) c := by
  obtain ⟨β, v, hβ, hv, h⟩ := h
  obtain ⟨t, ht, htv⟩ := valC_cap P hv
  refine ⟨β, (mem_hiddenSet P).mpr hβ, t, ht, ?_⟩
  rcases h with h | ⟨γ, w, hγ, hne, hw, hwv⟩
  · exact Or.inl (htv ▸ h)
  · obtain ⟨t', ht', htw⟩ := valC_cap P hw
    exact Or.inr ⟨γ, (mem_hiddenSet P).mpr hγ, hne, t', ht', by rw [htw, hwv, htv]⟩

/-- No hidden path has a path-oracle answer before the end phase. -/
theorem not_coll_of_vStruct {vs : VState Dg E C Msg} {c : ACache Msg Dg E C}
    (hV : VStruct P iv vs.1 c) (K : List C) : ¬ Coll (hiddenSet P vs) K c := by
  rintro ⟨β, hβ, t, ht, -⟩
  exact ((mem_hiddenSet P).mp hβ).2 (hV.tFresh β (by rw [ht]; simp))

/-- The arithmetic of the hidden-collision bound. -/
theorem hidden_arith {v h q : ℕ} (hq : v + h ≤ q) : h * (2 * v + 1 + h) ≤ q * (q + 1) := by
  nlinarith

/-- **The collision bound.** In the visible game without path queries followed by the end phase,
a distinguisher of cost at most `q` causes a visible or a hidden collision with probability at
most `(q (2q + 1) + q (q + 1)) / |C|`. -/
theorem prEvent_visRun_le {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) (q : ℕ)
    (hD : QueryCostAtMost D (queryCost (Dg := Dg) P) q) :
    Pr{let z ← (simulateQ (aSpec Msg Dg E C).romImpl
        (visRun P iv false D (SimState.init iv, [], false))).run ∅}[
      z.1.2.2.2 = true ∨ EC P iv z.1.2 z.2] ≤
      (q * (2 * q + 1) + q * (q + 1) : ℕ) / (Fintype.card C : ℝ≥0∞) := by
  set vs₀ : VState Dg E C Msg := (SimState.init iv, [], false)
  have hfold := run_simulateQ_foldRO (visImpl P iv false) D vs₀ (∅ : ACache Msg Dg E C)
  simp only [visRun, simulateQ_bind, StateT.run_bind]
  rw [hfold, bind_map_left]
  have hinit : VStruct P iv vs₀.1 (∅ : ACache Msg Dg E C) := vStruct_init
  -- the visible collisions along the run
  have hbad : Pr{let z ← (simulateQ (visF P iv) D).run (vs₀, ∅)}[z.2.1.2.2 = true] ≤
      q * ((2 * q + 1 : ℕ) / (Fintype.card C : ℝ≥0∞)) := by
    have := prEvent_run_bad_le (spec' := unifSpec) (visF P iv) (fun s ↦ s.1.2.2 = true)
      (fun s ↦ VStruct P iv s.1.1 s.2) (queryCost (Dg := Dg) P) (fun s ↦ vsize P s.1) q
      ((2 * q + 1 : ℕ) / (Fintype.card C : ℝ≥0∞))
      (fun t s hs z hz ↦ vStruct_visF P iv t s hs hz)
      (fun t s _ z hz ↦ vsize_visF P iv t s hz)
      (fun t s hs hb hN ↦ (prEvent_visF_bad_le P iv t s hs hb).trans (by
        gcongr
        rw [length_knownC]
        have : s.1.1.edges.length ≤ vsize P s.1 := Nat.le_add_right _ _
        omega)) D q hD (vs₀, ∅) hinit (by simp [vsize, vs₀, SimState.init])
    simpa [vs₀] using this
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z ↦ z.2.1.2.2 = true) _
    (ε := (q * (q + 1) : ℕ) / (Fintype.card C : ℝ≥0∞)) fun z hz hzb ↦ ?_).trans ?_
  · -- the hidden collisions in the end phase
    have hV := inv_of_mem_support_run (spec' := unifSpec) (visF P iv)
      (fun s ↦ VStruct P iv s.1.1 s.2) (fun t s hs z hz ↦ vStruct_visF P iv t s hs hz) D hinit
      z hz
    have hsize := size_le_of_mem_support_run (spec' := unifSpec) (visF P iv)
      (fun s ↦ VStruct P iv s.1.1 s.2) (queryCost (Dg := Dg) P) (fun s ↦ vsize P s.1)
      (fun t s hs z hz ↦ vStruct_visF P iv t s hs hz) (fun t s _ z hz ↦ vsize_visF P iv t s hz)
      D q hD hinit z hz
    simp only [vsize, vs₀, SimState.init, List.length_nil, List.map_nil, List.sum_nil,
      add_zero, zero_add] at hsize
    simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, Functor.map_map]
    refine (prEvent_mono _ _ _ fun w hw ↦ ?_).trans
      ((prEvent_coll_endPhase P (hiddenSet P z.2.1) (knownC iv z.2.1.1) z.2.1.2.1 z.2.2
        (not_coll_of_vStruct P iv hV _)).trans ?_)
    · rcases hw with hw | hw
      · exact absurd hw hzb
      · exact coll_of_EC P iv hw
    · rw [mul_div_assoc']
      gcongr
      have h1 := card_hiddenSet_le P z.2.1
      rw [length_knownC]
      set h := (z.2.1.2.1.map fun m ↦ (P.pad m).length).sum
      calc (h : ℝ≥0∞) * ((2 * z.2.1.1.edges.length + 1 : ℕ) + (hiddenSet P z.2.1).card)
          ≤ (h : ℝ≥0∞) * ((2 * z.2.1.1.edges.length + 1 : ℕ) + h) := by gcongr
        _ = ((h * (2 * z.2.1.1.edges.length + 1 + h) : ℕ) : ℝ≥0∞) := by push_cast; ring
        _ ≤ _ := by exact_mod_cast hidden_arith hsize
  · rw [Nat.cast_add, ENNReal.add_div]
    gcongr
    refine hbad.trans (le_of_eq ?_)
    rw [mul_div_assoc', Nat.cast_mul]

end Setting

end Common
