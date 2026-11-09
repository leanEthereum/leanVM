module

public import Common.Indiff.Support

@[expose] public section

/-!
# Indifferentiability: the invariant of the combined game

The combined game's two views answer alike as long as two things have not happened:

* **a visible collision** (`CState.bad`): some simulator draw — a fresh answer, forward or
  inverse — has a capacity already visible (`knownC`): the initial capacity, or a capacity of
  either end of an earlier simulator edge;
* **a hidden collision** (`EC`): the value of a *hidden* path — a prefix of a hashed message's
  padding that the simulator has not rooted — has the capacity of a visible state or of another
  hidden path's value.

`Inv` is the invariant of the combined game: unconditional bookkeeping facts (`Struct`), and,
when neither collision has happened, the agreement facts (`Cons`): the full view is the visible
edges together with the hidden edges (`allMem`), the visible edges are a partial bijection whose
unrooted inputs have no rooted capacity, the rooted capacities are distinct, and no answer has
differed yet.
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

/-- The simulator's rooted paths (with the empty path). -/
def vPaths (σ : SimState Dg E C) : List (List (Dg × E)) := σ.chains.map Prod.snd

/-- The prefixes of the hashed messages' paddings. -/
def hPaths (hashed : List Msg) : List (List (Dg × E)) :=
  hashed.flatMap fun m ↦ prefixesOf (P.pad m)

/-- A *hidden* path: a prefix of a hashed message's padding that the simulator has not rooted. -/
def Hidden (vs : VState Dg E C Msg) (β : List (Dg × E)) : Prop :=
  β ∈ hPaths P vs.2.1 ∧ β ∉ vPaths vs.1

/-- The state at the end of a path: the initial state for the empty path, the path's value
otherwise. -/
def svC (c : ACache Msg Dg E C) (β : List (Dg × E)) : Option (SpState Dg E C) :=
  if β = [] then some iv else valC P c β

/-- **A hidden collision**: the value of a hidden path has a visible capacity, or the capacity of
another hidden path's value. -/
def EC (vs : VState Dg E C Msg) (c : ACache Msg Dg E C) : Prop :=
  ∃ β v, Hidden P vs β ∧ valC P c β = some v ∧
    (v.2 ∈ knownC iv vs.1 ∨ ∃ γ w, Hidden P vs γ ∧ γ ≠ β ∧ valC P c γ = some w ∧ w.2 = v.2)

/-- A hidden edge: the sponge's edge into the value of a hidden path. -/
def HiddenEdge (vs : VState Dg E C Msg) (c : ACache Msg Dg E C)
    (e : SpState Dg E C × SpState Dg E C) : Prop :=
  ∃ β B s v, Hidden P vs (β ++ [B]) ∧ svC P iv c β = some s ∧
    valC P c (β ++ [B]) = some v ∧ e = (absorb s B, v)

/-- A rooted simulator edge: from a rooted node to the rooted state of its path. -/
def RootedEdge (σ : SimState Dg E C) (e : SpState Dg E C × SpState Dg E C) : Prop :=
  ∃ s β B, (s, β) ∈ σ.chains ∧ (e.2, β ++ [B]) ∈ σ.chains ∧ e.1 = absorb s B

/-- The edges the full view should hold: the visible ones and the hidden ones. -/
def GEdge (cs : CState Dg E C Msg) (c : ACache Msg Dg E C)
    (e : SpState Dg E C × SpState Dg E C) : Prop :=
  e ∈ cs.sim.edges ∨ HiddenEdge P iv cs.vis c e

/-- The unconditional bookkeeping facts of the combined game. -/
structure Struct (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) : Prop where
  /-- The initial state is rooted at the empty path. -/
  root : (iv, []) ∈ cs.sim.chains
  /-- A rooted state is the state at the end of its path. -/
  chainVal : ∀ p ∈ cs.sim.chains, svC P iv c p.2 = some p.1
  /-- A rooted state with a nonempty path is reached by a simulator edge from the rooted state of
  the path without its last block. -/
  chainEdge : ∀ p ∈ cs.sim.chains, p.2 ≠ [] → ∃ q ∈ cs.sim.chains, ∃ B,
    p.2 = q.2 ++ [B] ∧ (absorb q.1 B, p.1) ∈ cs.sim.edges
  /-- The value of every prefix of a hashed message's padding is cached. -/
  hCached : ∀ β ∈ hPaths P cs.hashed, valC P c β ≠ none

/-- The agreement facts about the simulator's state, while no collision has happened. -/
structure VisCons (σ : SimState Dg E C) : Prop where
  /-- Rooted states have distinct capacities. -/
  chainCap : (σ.chains.map fun p ↦ p.1.2).Nodup
  /-- Simulator edges have distinct inputs. -/
  vKeys : (σ.edges.map Prod.fst).Nodup
  /-- Simulator edges have distinct outputs. -/
  vVals : (σ.edges.map Prod.snd).Nodup
  /-- A simulator edge is rooted, or its input has no rooted capacity. -/
  vClass : ∀ e ∈ σ.edges, RootedEdge σ e ∨ ∀ p ∈ σ.chains, p.1.2 ≠ e.1.2

/-- The agreement facts of the combined game, while no collision has happened. -/
structure Cons (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) : Prop where
  /-- The simulator's state is consistent. -/
  vis : VisCons cs.sim
  /-- The full view holds exactly the visible and the hidden edges. -/
  allMem : ∀ e, e ∈ cs.all ↔ GEdge P iv cs c e
  /-- No answer has differed. -/
  noDiff : cs.diff = false

/-- **The invariant of the combined game.** -/
def Inv (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) : Prop :=
  Struct P iv cs c ∧ (cs.bad = false → ¬ EC P iv cs.vis c → Cons P iv cs c)

/-! ## Lists and lookups -/

omit [DecidableEq E] [DecidableEq C] [DecidableEq Msg] in
/-- A prefix of a padding's prefix is a prefix of the padding, or empty. -/
theorem init_mem_prefixesOf {bs β : List (Dg × E)} {B : Dg × E}
    (h : β ++ [B] ∈ prefixesOf bs) : β = [] ∨ β ∈ prefixesOf bs := by
  simp only [prefixesOf, List.mem_map, List.mem_range] at h ⊢
  obtain ⟨i, hi, hβ⟩ := h
  have hlen := congrArg List.length hβ
  simp only [List.length_take, List.length_append, List.length_singleton] at hlen
  rcases i with _ | i
  · left
    exact List.length_eq_zero_iff.mp (by omega)
  · right
    refine ⟨i, by omega, ?_⟩
    calc bs.take (i + 1) = (bs.take (i + 1 + 1)).take (i + 1) := by
          rw [List.take_take]; congr 1; omega
      _ = (β ++ [B]).take (i + 1) := by rw [hβ]
      _ = β := by rw [List.take_left' (by omega)]

omit [DecidableEq E] [DecidableEq C] [DecidableEq Msg] in
/-- The prefixes of a list are its nonempty `take`s. -/
theorem mem_prefixesOf {bs β : List (Dg × E)} :
    β ∈ prefixesOf bs ↔ ∃ i < bs.length, β = bs.take (i + 1) := by
  simp only [prefixesOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

/-- A forward lookup finds the output of a recorded edge whose input is unique. -/
theorem fwdLookup_eq_some_of_mem {A : PermutationEdges (SpState Dg E C)} {x y : SpState Dg E C}
    (h : (x, y) ∈ A) (huniq : ∀ e ∈ A, e.1 = x → e.2 = y) : forwardLookup A x = some y := by
  induction A with
  | nil => simp at h
  | cons e A ih =>
    obtain ⟨a, b⟩ := e
    by_cases hax : a = x
    · subst hax
      simp only [forwardLookup, ↓reduceIte]
      exact congrArg some (huniq (a, b) List.mem_cons_self rfl)
    · simp only [forwardLookup, hax, ↓reduceIte]
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hax
      · exact ih h fun e he ↦ huniq e (List.mem_cons_of_mem _ he)

/-- An inverse lookup finds the input of a recorded edge whose output is unique. -/
theorem invLookup_eq_some_of_mem {A : PermutationEdges (SpState Dg E C)} {x y : SpState Dg E C}
    (h : (x, y) ∈ A) (huniq : ∀ e ∈ A, e.2 = y → e.1 = x) : inverseLookup A y = some x := by
  induction A with
  | nil => simp at h
  | cons e A ih =>
    obtain ⟨a, b⟩ := e
    by_cases hby : b = y
    · subst hby
      simp only [inverseLookup, ↓reduceIte]
      exact congrArg some (huniq (a, b) List.mem_cons_self rfl)
    · simp only [inverseLookup, hby, ↓reduceIte]
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h; exact absurd h.2.symm hby
      · exact ih h fun e he ↦ huniq e (List.mem_cons_of_mem _ he)

/-- The rooted state of `chainOf` is a chain with the node's capacity. -/
theorem chainOf_some {VC : List (SpState Dg E C × List (Dg × E))} {x s : SpState Dg E C}
    {β : List (Dg × E)} (h : chainOf VC x = some (s, β)) : (s, β) ∈ VC ∧ s.2 = x.2 := by
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

/-- Without a `chainOf`, no chain has the node's capacity. -/
theorem chainOf_none {VC : List (SpState Dg E C × List (Dg × E))} {x : SpState Dg E C}
    (h : chainOf VC x = none) : ∀ p ∈ VC, p.1.2 ≠ x.2 := by
  intro p hp hpx
  have := List.find?_eq_none.mp h p hp
  simp [hpx] at this

/-! ## Visible capacities -/

/-- Membership in the visible capacities. -/
theorem mem_knownC {σ : SimState Dg E C} {k : C} :
    k ∈ knownC iv σ ↔ k = iv.2 ∨ ∃ e ∈ σ.edges, k = e.1.2 ∨ k = e.2.2 := by
  simp [knownC]

theorem iv_mem_knownC (σ : SimState Dg E C) : iv.2 ∈ knownC iv σ :=
  (mem_knownC iv).mpr (Or.inl rfl)

theorem fst_mem_knownC {σ : SimState Dg E C} {e : SpState Dg E C × SpState Dg E C}
    (he : e ∈ σ.edges) : e.1.2 ∈ knownC iv σ :=
  (mem_knownC iv).mpr (Or.inr ⟨e, he, Or.inl rfl⟩)

theorem snd_mem_knownC {σ : SimState Dg E C} {e : SpState Dg E C × SpState Dg E C}
    (he : e ∈ σ.edges) : e.2.2 ∈ knownC iv σ :=
  (mem_knownC iv).mpr (Or.inr ⟨e, he, Or.inr rfl⟩)

/-- Visible capacities after recording an edge. -/
theorem mem_knownC_cons {σ : SimState Dg E C} {x y : SpState Dg E C}
    {VC : List (SpState Dg E C × List (Dg × E))} {k : C} :
    k ∈ knownC iv ⟨(x, y) :: σ.edges, VC⟩ ↔ k ∈ knownC iv σ ∨ k = x.2 ∨ k = y.2 := by
  simp only [mem_knownC, List.mem_cons]
  constructor
  · rintro (h | ⟨e, he | he, h⟩)
    · exact Or.inl (Or.inl h)
    · subst he; exact Or.inr h
    · exact Or.inl (Or.inr ⟨e, he, h⟩)
  · rintro ((h | ⟨e, he, h⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨e, Or.inr he, h⟩
    · exact Or.inr ⟨(x, y), Or.inl rfl, h⟩

/-- A rooted state's capacity is visible. -/
theorem chain_cap_mem_knownC {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (hS : Struct P iv cs c) {p : SpState Dg E C × List (Dg × E)} (hp : p ∈ cs.sim.chains) :
    p.1.2 ∈ knownC iv cs.sim := by
  by_cases h : p.2 = []
  · have := hS.chainVal p hp
    simp only [svC, h, ↓reduceIte, Option.some.injEq] at this
    rw [← this]; exact iv_mem_knownC iv _
  · obtain ⟨q, -, B, -, he⟩ := hS.chainEdge p hp h
    exact snd_mem_knownC iv he

end Setting

end Common
