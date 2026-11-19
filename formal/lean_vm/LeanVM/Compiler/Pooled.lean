/-
  LeanVM.Compiler.Pooled

  The constants of a function's trace that read the scope's pooled cell of their word: a value
  set by one `const` and otherwise only read as a single cell, marked `Kind.pooled`.
-/

module

public import LeanVM.Compiler.Trace
public import LeanVM.Compiler.Map
public import LeanVM.Core.Renumber

/-!
# Constants read from the pool

A value the lowering writes with a `SET` into a cell of its own (`expr_into`, a `StackBuf` cell)
and that every other statement only reads, as a single cell, needs no cell of its own: the cell
of the scope's constant pool holding the same word serves every reader. `markPooled` rewrites the
trace so that placement does this: the value leaves its allocation and is made
`Kind.pooled` right before the `emit` of its `const`, as `const_cell`'s result is. Placement then
binds it to the pooled cell and emits nothing when the scope holds the word, and otherwise takes
the next free cell, emits the `SET` and teaches the pool.

The values (`poolable`), decided from the core function (`poolScan`, in placement's order of the
statements) and the trace's allocations:

* the first statement naming the value is its `const`, and no other statement writes it;
* it is allocated in the next free cells (`Kind.cell`) or in the padding run (`Kind.padRun`), and
  the value leaves that allocation: the values of the run a statement names as a run (a KECCAK
  window of the padding run, a buffer's run) are named otherwise than as one cell read, so they
  stay, and stay consecutive;
* every other statement names it only as one cell it reads (an operand, a pointer, a branch's
  condition, a selector, a call's argument, a KECCAK message cell `m0..m3` or `b8`), never as a
  destination, a cell of a run, a returned value or a parameter, nor as the source of a copy into
  a sponge run (`Kind.spongeRun`), whose copies are dropped only when their sources lie in
  consecutive cells;
* every statement naming it is in the block of its `const` or in a block inside it, so the value
  is in scope wherever it is named.

Statement `k` of the body in post-order (`postOrder`: a branch's or a `match`'s blocks before
it) is the `k`-th `emit` of the trace, since placement passes one `emit` a statement; so the pass
needs the body's order alone (`poolSites`).

The trace is advice: no proof of the back end depends on the pass. Soundness holds for every
trace, the pooled cell holding the word wherever it is read (the pool's invariant), and
completeness is the per-function checks, evaluated on the program as traced. `markPooled_alloc`
says what the pass does to the allocations: each of the marked trace is one of the trace's with
values taken out, or one value `poolable` accepted, made `Kind.pooled`.
-/

namespace LeanVM.Compiler

open LeanVM.Core

@[expose] public section

/-- The scan of a core function for its poolable constants (`poolScan`). -/
structure PoolScan where
  /-- The values named so far. -/
  seen : VMap Unit := {}
  /-- Each value whose first naming is a `const`, with the blocks around that `const`, innermost
  first. -/
  home : VMap (List Nat) := {}
  /-- The values named otherwise than as one cell read, or out of their `const`'s block. -/
  bad : VMap Unit := {}
  /-- The blocks around the statement scanned, innermost first. -/
  blocks : List Nat := []
  /-- The blocks entered so far. -/
  count : Nat := 0
  /-- The values of the trace's sponge runs (`Kind.spongeRun`). -/
  sponge : VMap Unit := {}

namespace PoolScan

/-- Whether the blocks `inner` are the blocks `outer` or blocks inside them. -/
def within (outer inner : List Nat) : Bool :=
  outer == inner.drop (inner.length - outer.length)

/-- A value read as one cell. -/
def rd (s : PoolScan) (v : V) : PoolScan :=
  let s' := { s with seen := s.seen.insert v () }
  match s.home.get? v with
  | some h => if within h s.blocks then s' else { s' with bad := s'.bad.insert v () }
  | none => s'

/-- A value named otherwise. -/
def oth (s : PoolScan) (v : V) : PoolScan :=
  { s with seen := s.seen.insert v (), bad := s.bad.insert v () }

/-- A value set by a `const`. -/
def cst (s : PoolScan) (v : V) : PoolScan :=
  if s.seen.contains v then s.oth v
  else { s with seen := s.seen.insert v (), home := s.home.insert v s.blocks }

def rds (s : PoolScan) (vs : List V) : PoolScan := vs.foldl rd s
def oths (s : PoolScan) (vs : List V) : PoolScan := vs.foldl oth s

/-- A block begins. -/
def enter (s : PoolScan) : PoolScan :=
  { s with blocks := s.count :: s.blocks, count := s.count + 1 }

/-- A block ends: the blocks around are those before it. -/
def exit (s outer : PoolScan) : PoolScan := { s with blocks := outer.blocks }

/-- An atom. -/
def atom (s : PoolScan) : Atom → PoolScan
  | .const d _ => s.cst d
  | .add d a b | .mul d a b => (s.rds [a, b]).oth d
  | .copy d a => if s.sponge.contains d then (s.oth a).oth d else (s.rd a).oth d
  | .load d p _ => (s.rd p).oth d
  | .assertEq a b | .assertInK a b => s.rds [a, b]
  | .assertNe x i p => (s.rd x).oths [i, p]
  | .rangeCheck x y t1 t2 k => (s.rds [x, k]).oths [y, t1, t2]
  | .keccak ins outs _ _ =>
      let ix := ins.zipIdx
      let s := s.rds (ix.filterMap fun (v, i) => if i < 4 || i == 8 then some v else none)
      (s.oths (ix.filterMap fun (v, i) => if i < 4 || i == 8 then none else some v)).oths outs
  | .frameAddr p run => s.oths (p :: run)
  | .hint h => s.oths h.vals
  | .touch t p => (s.rd p).oth t

end PoolScan

open PoolScan in
mutual
/-- The scan of statements, in placement's order. -/
def scanStmts : PoolScan → List Stmt → PoolScan
  | s, [] => s
  | s, st :: rest => scanStmts (scanStmt s st) rest

/-- The scan of a statement. -/
def scanStmt : PoolScan → Stmt → PoolScan
  | s, .atom a => s.atom a
  | s, .ite c z n =>
      let s := s.rd c
      let s := (scanStmts s.enter z).exit s
      (scanStmts s.enter n).exit s
  | s, .match_ x arms => scanArms (s.rd x) arms
  | s, .call _ args rets => (s.rds args).oths rets
  | s, .callIf c _ args => s.rds (c :: args)
  | s, .dispatch x _ args rets => (s.rds (x :: args)).oths rets
  | s, .ret vs => s.oths vs

/-- The scan of a `match`'s arms, each a block. -/
def scanArms : PoolScan → List (List Stmt) → PoolScan
  | s, [] => s
  | s, arm :: arms => scanArms ((scanStmts s.enter arm).exit s) arms
end

/-- The values of the trace's sponge runs. -/
def spongeVals (trace : Array Event) : VMap Unit :=
  trace.foldl (init := {}) fun m e =>
    match e with
    | .alloc vs .spongeRun => vs.foldl (fun m v => m.insert v ()) m
    | _ => m

/-- The scan of a function: its parameters, then its body. -/
def poolScan (f : Fn) (trace : Array Event) : PoolScan :=
  scanStmts (({ sponge := spongeVals trace } : PoolScan).oths f.params) f.body

/-- The kinds of allocation a value is taken out of when it is pooled: the next free cells
(`Kind.cell`) and the padding run (`Kind.padRun`), whose cells are taken in order. -/
def Kind.splits : Kind → Bool
  | .cell | .padRun => true
  | _ => false

/-- The values of the trace's allocations of a kind that `Kind.splits`. -/
def cellVals (trace : Array Event) : List V :=
  trace.toList.flatMap fun
    | .alloc vs k => if k.splits then vs else []
    | _ => []

/-- The values `markPooled` makes pooled: allocated as `Kind.cell` or in the padding run, set by
the `const` naming them first, and otherwise only read as one cell in that `const`'s block. -/
def poolable (f : Fn) (trace : Array Event) : VMap Unit :=
  let s := poolScan f trace
  (cellVals trace).foldl (init := {}) fun m v =>
    if s.home.contains v && !s.bad.contains v then m.insert v () else m

mutual
/-- The statements in the order placement passes their `emit`s: a branch's or a `match`'s blocks
before it. -/
def postOrder : List Stmt → List Stmt
  | [] => []
  | st :: rest => postStmt st ++ postOrder rest

/-- A statement's blocks in post-order, then the statement. -/
def postStmt : Stmt → List Stmt
  | .ite c z n => postOrder z ++ postOrder n ++ [.ite c z n]
  | .match_ x arms => postArms arms ++ [.match_ x arms]
  | st => [st]

def postArms : List (List Stmt) → List Stmt
  | [] => []
  | arm :: arms => postOrder arm ++ postArms arms
end

/-- The value a statement makes pooled: a `const` of a value in `K`. -/
def poolSite (K : VMap Unit) : Stmt → Option V
  | .atom (.const d _) => if K.contains d then some d else none
  | _ => none

/-- For each `emit` of the trace in order, the value made pooled right before it. -/
def poolSites (K : VMap Unit) (f : Fn) : List (Option V) :=
  (postOrder f.body).map (poolSite K)

/-- An event other than an `emit`, the values of `K` taken out of an allocation of a kind that
`Kind.splits`. -/
def poolEvent (K : VMap Unit) : Event → List Event
  | .alloc vs k =>
      if k.splits && vs.any fun v => K.contains v then
        let ws := vs.filter fun v => !K.contains v
        if ws.isEmpty then [] else [.alloc ws k]
      else [.alloc vs k]
  | e => [e]

/-- The events of the trace from an `emit` on, each with what replaces it: `sites` the values
made pooled before this `emit` and the ones after. -/
def poolEvents (K : VMap Unit) : List (Option V) → List Event → List (List Event)
  | _, [] => []
  | sites, e :: es =>
      match e with
      | .emit =>
          ((match sites.head? with
            | some (some d) => [.alloc [d] .pooled]
            | _ => []) ++ [.emit]) :: poolEvents K sites.tail es
      | e => poolEvent K e :: poolEvents K sites es

/-- What replaces each event of the trace. -/
def markPooledParts (f : Fn) (trace : Array Event) : List (List Event) :=
  let K := poolable f trace
  poolEvents K (poolSites K f) trace.toList

/-- A function's trace, each value of `poolable` made `Kind.pooled` right before its `const`. -/
def markPooled (f : Fn) (trace : Array Event) : Array Event :=
  (markPooledParts f trace).flatten.toArray

/-- The source lines of a function's statements, `(n, line)` with `n` the events of the trace
before the statement, moved to the positions of `markPooled f trace`. -/
def markPooledLines (f : Fn) (trace : Array Event) (lines : Array (Nat × Nat)) :
    Array (Nat × Nat) :=
  let (pos, n) := (markPooledParts f trace).foldl (init := (#[], 0)) fun (pos, n) p =>
    (pos.push n, n + p.length)
  let pos := pos.push n
  lines.map fun (k, line) => (pos.getD k k, line)

/-! ## What the pass does -/

theorem mem_of_head? {l : List (Option V)} {o : Option V} (h : l.head? = some o) : o ∈ l := by
  cases l with
  | nil => cases h
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp

theorem mem_of_mem_tail {l : List (Option V)} {o : Option V} (h : o ∈ l.tail) : o ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => exact List.mem_cons_of_mem _ h

theorem poolEvent_alloc {K : VMap Unit} {e : Event} {vs : List V} {k : Kind}
    (h : Event.alloc vs k ∈ poolEvent K e) : ∃ ws, e = .alloc ws k ∧ vs.Sublist ws := by
  cases e with
  | alloc ws k' =>
      simp only [poolEvent] at h
      split at h
      · split at h
        · simp at h
        · simp only [List.mem_singleton, Event.alloc.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨ws, rfl, List.filter_sublist⟩
      · simp only [List.mem_singleton, Event.alloc.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨vs, rfl, List.Sublist.refl _⟩
  | _ => simp [poolEvent] at h

theorem poolEvents_alloc (K : VMap Unit) :
    ∀ (sites : List (Option V)) (es : List Event) (vs : List V) (k : Kind),
      Event.alloc vs k ∈ (poolEvents K sites es).flatten →
        (∃ ws, Event.alloc ws k ∈ es ∧ vs.Sublist ws) ∨
          (k = .pooled ∧ ∃ d, vs = [d] ∧ some d ∈ sites) := by
  intro sites es
  induction es generalizing sites with
  | nil => simp [poolEvents]
  | cons e es ih =>
    intro vs k h
    have tail : ∀ {s : List (Option V)}, (∀ x ∈ s, x ∈ sites) →
        Event.alloc vs k ∈ (poolEvents K s es).flatten →
          (∃ ws, Event.alloc ws k ∈ e :: es ∧ vs.Sublist ws) ∨
            (k = .pooled ∧ ∃ d, vs = [d] ∧ some d ∈ sites) := by
      intro s hs h
      rcases ih s vs k h with ⟨ws, hw, hsub⟩ | ⟨hk, d, rfl, hd⟩
      · exact .inl ⟨ws, List.mem_cons_of_mem _ hw, hsub⟩
      · exact .inr ⟨hk, d, rfl, hs _ hd⟩
    cases e with
    | emit =>
        simp only [poolEvents, List.flatten_cons, List.mem_append] at h
        rcases h with h | h
        · cases hs : sites.head? with
          | none => simp [hs] at h
          | some o =>
            cases o with
            | none => simp [hs] at h
            | some d =>
              simp [hs] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .inr ⟨rfl, d, rfl, mem_of_head? hs⟩
        · exact tail (fun x hx => mem_of_mem_tail hx) h
    | alloc ws k' =>
        simp only [poolEvents, List.flatten_cons, List.mem_append] at h
        rcases h with h | h
        · obtain ⟨ws', he, hsub⟩ := poolEvent_alloc h
          cases he
          exact .inl ⟨ws, List.mem_cons_self .., hsub⟩
        · exact tail (fun x hx => hx) h
    | _ =>
        simp only [poolEvents, List.flatten_cons, List.mem_append] at h
        rcases h with h | h
        · obtain ⟨_, he, _⟩ := poolEvent_alloc h
          cases he
        · exact tail (fun x hx => hx) h

/-- **What the pass does to allocations**: an allocation of the marked trace is one of the
trace's with values taken out, or one value `poolable` accepts made `Kind.pooled`. -/
theorem markPooled_alloc {f : Fn} {trace : Array Event} {vs : List V} {k : Kind}
    (h : Event.alloc vs k ∈ (markPooled f trace).toList) :
    (∃ ws, Event.alloc ws k ∈ trace.toList ∧ vs.Sublist ws) ∨
      (k = .pooled ∧ ∃ d, vs = [d] ∧ (poolable f trace).contains d = true) := by
  simp only [markPooled, markPooledParts, List.toList_toArray] at h
  rcases poolEvents_alloc _ _ _ vs k h with h | ⟨hk, d, rfl, hd⟩
  · exact .inl h
  · refine .inr ⟨hk, d, rfl, ?_⟩
    simp only [poolSites, List.mem_map] at hd
    obtain ⟨st, -, hst⟩ := hd
    simp only [poolSite] at hst
    split at hst
    · rename_i d' _
      by_cases hk : (poolable f trace).contains d' = true
      · simp only [hk, ↓reduceIte, Option.some.injEq] at hst
        subst hst
        exact hk
      · simp [hk] at hst
    · cases hst

end
end LeanVM.Compiler
