module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Common.Defs
public import Common.Game2

@[expose] public section

/-!
# The random-permutation model

A *random permutation* of a finite state type `S` is a uniformly random bijection `π : S ≃ S`
that every party may query in both directions: forward, `π x`, and inverse, `π⁻¹ y`
(`permutationOracleSpec S`).

Sampling `π` eagerly is out of reach for `S` the 1600-bit Keccak state, so the model samples it
lazily, as the lazily sampled random oracle samples a function. The state of the lazy
permutation (`lazyRandomPermutation`) is the list of edges `(x, π x)` fixed so far, newest first. A forward
query at a point `x` the list answers returns the recorded `π x`; a fresh forward query draws
`π x` uniformly from the points outside the current range, records the edge and returns it. An
inverse query is the same with domain and range exchanged.

What is proved here:

* the edge list stays a partial bijection (`isPartialPerm_of_mem_support`): its inputs are
  distinct and its outputs are distinct;
* every answer is recorded, edges are never removed (`lazyPerm_answer_mem`,
  `lazyPerm_log_suffix`), so the answers given along a run are those of one partial bijection:
  forward and inverse answers are consistent with each other;
* every partial bijection of a finite type extends to a permutation
  (`exists_perm_extends`), so every run of the lazy permutation is consistent with some
  permutation of `S`;
* a fresh answer is uniform over the points not yet used (`evalDist_uniformAvoiding`).

These are the properties the indifferentiability bound uses.
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

variable {S : Type}

section Lookup

variable [DecidableEq S]

/-- A recorded forward answer comes from an edge of the log. -/
theorem mem_of_fwdLookup_eq_some {E : PermutationEdges S} {x y : S} (h : forwardLookup E x = some y) :
    (x, y) ∈ E := by
  induction E with
  | nil => simp [forwardLookup] at h
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    by_cases hx : a = x
    · subst hx
      simp only [forwardLookup, ↓reduceIte, Option.some.injEq] at h
      simp [h]
    · simp only [forwardLookup, hx, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A recorded inverse answer comes from an edge of the log. -/
theorem mem_of_invLookup_eq_some {E : PermutationEdges S} {x y : S} (h : inverseLookup E y = some x) :
    (x, y) ∈ E := by
  induction E with
  | nil => simp [inverseLookup] at h
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    by_cases hy : b = y
    · subst hy
      simp only [inverseLookup, ↓reduceIte, Option.some.injEq] at h
      simp [h]
    · simp only [inverseLookup, hy, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- The log has no forward answer at `x` exactly when `x` is not an input of the log. -/
theorem fwdLookup_eq_none_iff {E : PermutationEdges S} {x : S} :
    forwardLookup E x = none ↔ x ∉ E.map Prod.fst := by
  induction E with
  | nil => simp [forwardLookup]
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    by_cases hx : a = x
    · subst hx
      simp [forwardLookup]
    · simp [forwardLookup, hx, ih, Ne.symm hx]

/-- The log has no inverse answer at `y` exactly when `y` is not an output of the log. -/
theorem invLookup_eq_none_iff {E : PermutationEdges S} {y : S} :
    inverseLookup E y = none ↔ y ∉ E.map Prod.snd := by
  induction E with
  | nil => simp [inverseLookup]
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    by_cases hy : b = y
    · subst hy
      simp [inverseLookup]
    · simp [inverseLookup, hy, ih, Ne.symm hy]

end Lookup

section Sampling

variable [Fintype S] [DecidableEq S] [SampleableType S]

/-- A uniform draw outside `l` avoids `l` whenever some point does. -/
theorem notMem_of_mem_support_uniformAvoiding {l : List S} (h : ∃ y, y ∉ l) {y : S}
    (hy : y ∈ support (uniformAvoiding l)) : y ∉ l := by
  rw [uniformAvoiding, dite_eq_left_of_eq_true (eq_true h)] at hy
  simp only [support_map, Set.mem_image] at hy
  obtain ⟨z, -, rfl⟩ := hy
  exact z.2

/-- **A fresh answer is uniform over the unused points:** a draw outside `l` satisfies an event
`p` with probability `#{y ∉ l | p y} / #{y ∉ l}`. -/
theorem prEvent_uniformAvoiding {l : List S} (h : ∃ y, y ∉ l) (p : S → Prop)
    [DecidablePred p] :
    Pr{let y ← uniformAvoiding l}[p y] =
      (Finset.univ.filter fun y ↦ y ∉ l ∧ p y).card /
        ((Finset.univ.filter fun y ↦ y ∉ l).card : ℝ≥0∞) := by
  rw [uniformAvoiding, dite_eq_left_of_eq_true (eq_true h), prEvent_map]
  let : Nonempty {y // y ∉ l} := ⟨⟨h.choose, h.choose_spec⟩⟩
  let : SampleableType {y // y ∉ l} := SampleableType.subtype S (· ∉ l)
  rw [SampleableType.prEvent_uniformSample, Fintype.card_subtype]
  congr 2
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∉ l) p)

end Sampling

section LazyPerm

variable [Fintype S] [DecidableEq S] [SampleableType S]

/-- A lazily sampled random *function* in both directions: a recorded point is answered from the
log, a fresh answer is uniform over all of `S` (it may repeat a used point). Not a model of a
permutation: the indifferentiability proof compares `lazyRandomPermutation` with it. -/
noncomputable def lazyFun : QueryImpl (permutationOracleSpec S) (StateT (PermutationEdges S) ProbComp)
  | .forward x => StateT.mk fun A =>
      match forwardLookup A x with
      | some y => pure (y, A)
      | none => (fun y ↦ (y, (x, y) :: A)) <$> ($ᵗ S)
  | .inverse y => StateT.mk fun A =>
      match inverseLookup A y with
      | some x => pure (x, A)
      | none => (fun x ↦ (x, (x, y) :: A)) <$> ($ᵗ S)

/-- A log is a partial bijection: its inputs are distinct and its outputs are distinct. -/
def IsPartialPerm (E : PermutationEdges S) : Prop :=
  (E.map Prod.fst).Nodup ∧ (E.map Prod.snd).Nodup

omit [Fintype S] [DecidableEq S] [SampleableType S] in
/-- The empty log is a partial bijection. -/
theorem isPartialPerm_nil : IsPartialPerm ([] : PermutationEdges S) := ⟨List.nodup_nil, List.nodup_nil⟩

omit [DecidableEq S] [SampleableType S] in
/-- A partial bijection whose outputs cover `S` has inputs covering `S`. -/
theorem forall_mem_fst_of_forall_mem_snd {E : PermutationEdges S} (hE : IsPartialPerm E)
    (h : ∀ y : S, y ∈ E.map Prod.snd) (x : S) : x ∈ E.map Prod.fst := by
  classical
  by_contra hx
  have hsnd : Fintype.card S ≤ (E.map Prod.snd).length := by
    calc Fintype.card S = (Finset.univ : Finset S).card := Finset.card_univ.symm
      _ ≤ (E.map Prod.snd).toFinset.card := Finset.card_le_card fun y _ ↦ by simpa using h y
      _ ≤ _ := List.toFinset_card_le _
  have hfst : (E.map Prod.fst).length < Fintype.card S := by
    rw [← List.toFinset_card_of_nodup hE.1]
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun heq ↦ hx ?_⟩)
    have hmem : x ∈ (E.map Prod.fst).toFinset := heq ▸ Finset.mem_univ x
    simpa using hmem
  simp only [List.length_map] at hsnd hfst
  omega

omit [DecidableEq S] [SampleableType S] in
/-- A partial bijection whose inputs cover `S` has outputs covering `S`. -/
theorem forall_mem_snd_of_forall_mem_fst {E : PermutationEdges S} (hE : IsPartialPerm E)
    (h : ∀ x : S, x ∈ E.map Prod.fst) (y : S) : y ∈ E.map Prod.snd := by
  have hE' : IsPartialPerm (E.map Prod.swap) := by
    simpa [IsPartialPerm, List.map_map, Function.comp_def, And.comm] using hE
  have := forall_mem_fst_of_forall_mem_snd hE' (by simpa [List.map_map, Function.comp_def]
    using h) y
  simpa [List.map_map, Function.comp_def] using this

/-- **The lazy permutation keeps a partial bijection.** -/
theorem isPartialPerm_of_mem_support (q : PermutationQuery S) {E : PermutationEdges S} (hE : IsPartialPerm E)
    {z : S × PermutationEdges S} (hz : z ∈ support ((lazyRandomPermutation q).run E)) : IsPartialPerm z.2 := by
  cases q with
  | forward x =>
    simp only [lazyRandomPermutation, StateT.run_mk] at hz
    rcases hx : forwardLookup E x with _ | y
    · rw [hx] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hxE : x ∉ E.map Prod.fst := fwdLookup_eq_none_iff.mp hx
      have hfree : ∃ y, y ∉ E.map Prod.snd := by
        by_contra hall
        push Not at hall
        exact hxE (forall_mem_fst_of_forall_mem_snd hE hall x)
      exact ⟨List.nodup_cons.mpr ⟨hxE, hE.1⟩,
        List.nodup_cons.mpr ⟨notMem_of_mem_support_uniformAvoiding hfree hy, hE.2⟩⟩
    · rw [hx] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hE
  | inverse y =>
    simp only [lazyRandomPermutation, StateT.run_mk] at hz
    rcases hy : inverseLookup E y with _ | x
    · rw [hy] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hyE : y ∉ E.map Prod.snd := invLookup_eq_none_iff.mp hy
      have hfree : ∃ x, x ∉ E.map Prod.fst := by
        by_contra hall
        push Not at hall
        exact hyE (forall_mem_snd_of_forall_mem_fst hE hall y)
      exact ⟨List.nodup_cons.mpr ⟨notMem_of_mem_support_uniformAvoiding hfree hx, hE.1⟩,
        List.nodup_cons.mpr ⟨hyE, hE.2⟩⟩
    · rw [hy] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hE

/-- **Answers are recorded.** After a forward query `π x` answered `y`, the edge `(x, y)` is in
the log; after an inverse query `π⁻¹ y` answered `x`, the edge `(x, y)` is in the log. -/
theorem lazyPerm_answer_mem (q : PermutationQuery S) {E : PermutationEdges S}
    {z : S × PermutationEdges S} (hz : z ∈ support ((lazyRandomPermutation q).run E)) :
    match q with
    | .forward x => (x, z.1) ∈ z.2
    | .inverse y => (z.1, y) ∈ z.2 := by
  cases q with
  | forward x =>
    simp only [lazyRandomPermutation, StateT.run_mk] at hz
    rcases hx : forwardLookup E x with _ | y
    · rw [hx] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨y, -, rfl⟩ := hz
      exact List.mem_cons_self
    · rw [hx] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact mem_of_fwdLookup_eq_some hx
  | inverse y =>
    simp only [lazyRandomPermutation, StateT.run_mk] at hz
    rcases hy : inverseLookup E y with _ | x
    · rw [hy] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨x, -, rfl⟩ := hz
      exact List.mem_cons_self
    · rw [hy] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact mem_of_invLookup_eq_some hy

/-- **Edges are never removed:** the log before a query is a suffix of the log after it. -/
theorem lazyPerm_log_suffix (q : PermutationQuery S) {E : PermutationEdges S}
    {z : S × PermutationEdges S} (hz : z ∈ support ((lazyRandomPermutation q).run E)) : E <:+ z.2 := by
  cases q with
  | forward x =>
    simp only [lazyRandomPermutation, StateT.run_mk] at hz
    rcases hx : forwardLookup E x with _ | y
    · rw [hx] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨y, -, rfl⟩ := hz
      exact List.suffix_cons _ _
    · rw [hx] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact List.suffix_refl _
  | inverse y =>
    simp only [lazyRandomPermutation, StateT.run_mk] at hz
    rcases hy : inverseLookup E y with _ | x
    · rw [hy] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨x, -, rfl⟩ := hz
      exact List.suffix_cons _ _
    · rw [hy] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact List.suffix_refl _

/-- Over a whole run, the lazy permutation keeps a partial bijection and only adds edges. -/
theorem isPartialPerm_suffix_of_mem_support_simulateQ {α : Type}
    (oa : OracleComp (permutationOracleSpec S) α) {E : PermutationEdges S} (hE : IsPartialPerm E)
    {z : α × PermutationEdges S} (hz : z ∈ support ((simulateQ lazyRandomPermutation oa).run E)) :
    IsPartialPerm z.2 ∧ E <:+ z.2 := by
  induction oa using OracleComp.inductionOn generalizing E with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hE, List.suffix_refl _⟩
  | query_bind q k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, monadLift_self,
      mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have h1 := isPartialPerm_of_mem_support q hE hw
    obtain ⟨h2, h3⟩ := ih w.1 h1 hz
    exact ⟨h2, (lazyPerm_log_suffix q hw).trans h3⟩

end LazyPerm

section Extension

variable [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- **A partial bijection extends to a permutation.** Every log in which inputs are distinct and
outputs are distinct is the graph of the restriction of some permutation of `S`. So the answers
of every run of `lazyRandomPermutation` are those of a permutation. -/
theorem exists_perm_extends {E : PermutationEdges S} (hE : IsPartialPerm E) :
    ∃ π : Equiv.Perm S, ∀ e ∈ E, π e.1 = e.2 := by
  classical
  let f : {e // e ∈ E} → S := fun e ↦ e.1.1
  let g : {e // e ∈ E} → S := fun e ↦ e.1.2
  have hf : Function.Injective f := fun e e' h ↦
    Subtype.ext (List.inj_on_of_nodup_map hE.1 e.2 e'.2 h)
  have hg : Function.Injective g := fun e e' h ↦
    Subtype.ext (List.inj_on_of_nodup_map hE.2 e.2 e'.2 h)
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨π, fun e he ↦ hπ ⟨e, he⟩⟩

end Extension

end Common
