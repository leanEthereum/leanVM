/-
  LeanVM.Compiler.Unnamed

  The values of a function's trace that its core function never names, marked so that they take
  no frame cell.
-/

module

public import LeanVM.Compiler.Trace
public import LeanVM.Compiler.Map
public import LeanVM.Core.Renumber

/-!
# Values no statement names

A function's expansion makes values its core function never names: the destination of an
`@inline` call whose return aliases a run or an address, a `StackBuf` cell never read, the site of
an `@inline` call. No instruction or hint touches a cell such a value takes. `markUnnamed` rewrites
the trace so that it takes none: each `alloc` event of `Kind.cell` is split into its maximal
segments of values the core function names (`namedVals`: its parameters and `Stmt.valsList` of its
body), which stay `Kind.cell`, and of values it does not, which become `Kind.unnamed`. Placement
gives consecutive `Kind.cell` events consecutive cells, so a run of named values keeps its cells
consecutive, and the values of the trace, in order, are unchanged (`segments_vals`).

The decision reads the core function alone, and `markUnnamed_named` proves that no value the core
function names is marked: placement keeps a cell for every value a statement names. The trace is
advice, so no proof of the back end depends on the pass: soundness holds for every trace, and
completeness is the per-function checks, evaluated on the program as traced.
-/

namespace LeanVM.Compiler

open LeanVM.Core

@[expose] public section

/-- The values a core function names: its parameters and every value of its statements. -/
def namedVals (f : Fn) : VMap Unit :=
  (f.params ++ Stmt.valsList f.body).foldl (fun m v => m.insert v ()) {}

/-- A list's maximal segments of values on one side of `p`, each with its side. -/
def segments (p : V → Bool) : List V → List (Bool × List V)
  | [] => []
  | v :: vs =>
      match segments p vs with
      | (b, s) :: rest => if p v == b then (b, v :: s) :: rest else (p v, [v]) :: (b, s) :: rest
      | [] => [(p v, [v])]

/-- An event, the values of a `Kind.cell` allocation that `p` rejects marked `Kind.unnamed`. -/
def markEvent (p : V → Bool) : Event → List Event
  | .alloc vs .cell => (segments p vs).map fun x => .alloc x.2 (if x.1 then .cell else .unnamed)
  | e => [e]

/-- A function's trace, every value of a `Kind.cell` allocation that the core function `f` does
not name marked `Kind.unnamed`. -/
def markUnnamed (f : Fn) (trace : Array Event) : Array Event :=
  (trace.toList.flatMap (markEvent (namedVals f).contains)).toArray

/-- The source lines of a function's statements, `(n, line)` with `n` the events of the trace
before the statement, moved to the positions of `markUnnamed f trace`. -/
def markLines (f : Fn) (trace : Array Event) (lines : Array (Nat × Nat)) : Array (Nat × Nat) :=
  let p := (namedVals f).contains
  let (pos, n) := trace.foldl (init := (#[], 0)) fun (pos, n) e =>
    (pos.push n, n + (markEvent p e).length)
  let pos := pos.push n
  lines.map fun (k, line) => (pos.getD k k, line)

theorem foldl_insert_contains (l : List V) (m : VMap Unit) (v : V)
    (h : v ∈ l ∨ m.contains v = true) :
    (l.foldl (fun m v => m.insert v ()) m).contains v = true := by
  induction l generalizing m with
  | nil => simpa using h
  | cons w ws ih =>
    apply ih
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inr (by simp [KMap.contains, KMap.get?_insert])
      · exact .inl h
    · refine .inr ?_
      simp only [KMap.contains, KMap.get?_insert] at h ⊢
      split <;> simp_all

/-- Every value the core function names is in `namedVals`. -/
theorem namedVals_contains {f : Fn} {v : V} (h : v ∈ f.params ++ Stmt.valsList f.body) :
    (namedVals f).contains v = true :=
  foldl_insert_contains _ _ v (.inl h)

/-- Each segment's values are on its side. -/
theorem segments_side (p : V → Bool) (vs : List V) :
    ∀ x ∈ segments p vs, ∀ v ∈ x.2, p v = x.1 := by
  induction vs with
  | nil => simp [segments]
  | cons v vs ih =>
    intro x hx w hw
    cases h : segments p vs with
    | nil =>
      simp only [segments, h, List.mem_singleton] at hx
      subst hx
      simp only [List.mem_singleton] at hw
      subst hw
      rfl
    | cons y rest =>
      obtain ⟨b, s⟩ := y
      rw [h] at ih
      by_cases hb : p v = b
      · simp only [segments, h, hb, BEq.rfl, ite_true, List.mem_cons] at hx
        rcases hx with rfl | hx
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact hb
          · exact ih (b, s) (by simp) w hw
        · exact ih x (by simp [hx]) w hw
      · have hb' : (p v == b) = false := by simpa using hb
        simp only [segments, h, hb', Bool.false_eq_true, ite_false, List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · simp only [List.mem_singleton] at hw
          rw [hw]
        · exact ih _ (by simp) w hw
        · exact ih x (by simp [hx]) w hw

/-- The segments, one after another, are the list. -/
theorem segments_vals (p : V → Bool) (vs : List V) : (segments p vs).flatMap (·.2) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases h : segments p vs with
    | nil =>
      rw [h] at ih
      simp only [segments, h, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      simp only [List.flatMap_nil] at ih
      rw [← ih]
    | cons y rest =>
      obtain ⟨b, s⟩ := y
      rw [h, List.flatMap_cons] at ih
      by_cases hb : p v = b
      · simp only [segments, h, hb, BEq.rfl, ite_true, List.flatMap_cons, List.cons_append, ih]
      · have hb' : (p v == b) = false := by simpa using hb
        simp only [segments, h, hb', Bool.false_eq_true, ite_false, List.flatMap_cons,
          List.singleton_append, ih]

/-- **No named value is marked**: a value of a `Kind.unnamed` event of the marked trace that the
core function names was in a `Kind.unnamed` event of the trace already. -/
theorem markUnnamed_named {f : Fn} {trace : Array Event} {vs : List V} {v : V}
    (he : Event.alloc vs .unnamed ∈ (markUnnamed f trace).toList) (hv : v ∈ vs)
    (hn : v ∈ f.params ++ Stmt.valsList f.body) :
    ∃ ws, Event.alloc ws .unnamed ∈ trace.toList ∧ v ∈ ws := by
  simp only [markUnnamed, List.toList_toArray, List.mem_flatMap] at he
  obtain ⟨e, het, hm⟩ := he
  match e, hm with
  | .alloc ws .cell, hm =>
      simp only [markEvent, List.mem_map] at hm
      obtain ⟨x, hx, hxe⟩ := hm
      have hside := segments_side _ ws x hx v
      cases hb : x.1
      · simp only [hb, Bool.false_eq_true, ite_false, Event.alloc.injEq, and_true] at hxe
        have := hside (by rw [hxe]; exact hv)
        rw [hb, namedVals_contains hn] at this
        exact absurd this (by simp)
      · simp [hb] at hxe
  | .alloc _ .unnamed, hm =>
      simp only [markEvent, List.mem_singleton] at hm
      exact ⟨_, by rw [← hm] at het; exact het, hv⟩
  | .alloc _ .pooled, hm | .alloc _ .addr, hm | .alloc _ .ret, hm | .alloc _ .padRun, hm
  | .alloc _ .spongeRun, hm | .emit, hm | .enter, hm | .leave, hm | .use _, hm | .shift _ _, hm
  | .chain, hm | .note _, hm =>
      simp [markEvent] at hm

end
end LeanVM.Compiler
