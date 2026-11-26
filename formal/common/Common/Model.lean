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

What is proved here: a fresh answer is uniform over the points not yet used
(`prEvent_uniformAvoiding`), and the lazily sampled random function in both directions
(`lazyFun`) that the indifferentiability proof compares the lazy permutation with.
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

end LazyPerm

end Common
