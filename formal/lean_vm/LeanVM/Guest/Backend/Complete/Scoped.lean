/-
  LeanVM.Guest.Backend.Complete.Scoped

  The traced functions whose frames the completeness proof can fill: every value a statement
  names was made on the statement's own path, in a block around it.
-/

module

public import LeanVM.Guest.Backend.Place
public import LeanVM.Guest.Memory.Fresh

/-!
# Scoped traces

Placement rewinds the next free cell for each arm of a `match` (the arms share their cells, one
arm running) and keeps every value it placed. It never checks that a value a statement names was
made on that statement's path, so it accepts a function whose frame no single memory can hold:

    match x [[v := 3], [w := 5]]; z := v · v; return

places `v` and `w` in one cell, and on the path through the second arm the cell must hold both
`σ w` and `σ v`. The completeness proof therefore asks of the traced function that it is
**scoped**: walking its body and its trace in the order placement reads them, every value a
statement names (`atomUses`, `atomTmps`, a branch condition, a selector, a call's arguments and
returns, the returned values) was made by an `alloc` event of a block around the statement on
its path, or is a parameter; every value a `use` or `shift` event names too; and a path makes at
most one return area (`Kind.ret`), of at most the function's return cells.

`scopedE` is the walk, `scopedB` its decision and `Scoped` the proposition the proofs take. The
walk is placement's own reading of the trace (`flushN`, `expect`, `inBlock`, `placeArms`) with the
values in scope instead of cells.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The state of the walk: the trace from the event it is at, the values in scope on the path,
and whether the path made its return area. -/
structure SSt where
  rest : List Event
  live : VMap Unit
  retDone : Bool

/-- The values put in scope. -/
def addLive (live : VMap Unit) (vs : List V) : VMap Unit :=
  vs.foldl (fun m v => m.insert v ()) live

/-- The values made before the next statement or the end of the block (`flushN`): `rc` is the
function's return cells. -/
def flushS (rc : Nat) : List Event → VMap Unit → Bool → Except String SSt
  | [], live, r => .ok ⟨[], live, r⟩
  | e :: es, live, r =>
      match e with
      | .alloc vs kind =>
          if kind == .ret then
            if r then .error "a second return area on one path"
            else if rc < vs.length then .error "a return area past the return cells"
            else flushS rc es (addLive live vs) true
          else flushS rc es (addLive live vs) r
      | .use v =>
          if live.contains v then flushS rc es live r else .error "a use of a value out of scope"
      | .shift v _ =>
          if live.contains v then flushS rc es live r else .error "a shift of a value out of scope"
      | .chain => flushS rc es live r
      | .note _ => flushS rc es live r
      | _ => .ok ⟨e :: es, live, r⟩

/-- `flushS` at a state. -/
def flushAt (rc : Nat) (s : SSt) : Except String SSt := flushS rc s.rest s.live s.retDone

/-- Pass the event `e`, which the walk must be at (`expect`). -/
def expectS (e : Event → Bool) (what : String) (s : SSt) : Except String SSt :=
  match s.rest with
  | ev :: es => if e ev then .ok { s with rest := es } else .error s!"the trace is not at {what}"
  | [] => .error s!"the trace ends before {what}"

/-- The values are in scope. -/
def inScope (live : VMap Unit) (vs : List V) : Bool := vs.all live.contains

/-- A statement's own values in scope, or the error naming the first that is not. -/
def needScope (live : VMap Unit) (vs : List V) (what : String) : Except String Unit :=
  if inScope live vs then .ok ()
  else .error s!"{what} names a value out of scope: {(vs.find? (!live.contains ·)).map (·.idx)}"

/-- The values a statement names itself, its blocks apart. -/
def ownUses : Stmt → List V
  | .atom a => atomUses a ++ atomTmps a
  | .ite c _ _ => [c]
  | .match_ x _ => [x]
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: (args ++ rets)
  | .ret vs => vs

mutual
/-- A block. -/
def scopeBlock (rc : Nat) : List Stmt → SSt → Except String SSt
  | [], s => .ok s
  | st :: rest, s => do
      let s' ← scopeStmt rc st s
      scopeBlock rc rest s'

/-- A statement: its values in scope after the values made before it. -/
def scopeStmt (rc : Nat) : Stmt → SSt → Except String SSt
  | .ite c z nz, s => do
      let s ← flushAt rc s
      needScope s.live [c] "a branch"
      let s₁ ← scopeInner rc z s
      match s₁.rest with
      | .enter :: _ =>
          let s₂ ← scopeInner rc nz { s₁ with retDone := s.retDone }
          expectS isEmit "a branch" { s₂ with retDone := s₁.retDone || s₂.retDone }
      | _ =>
          if !nz.isEmpty then .error "an else block the trace does not enter"
          else expectS isEmit "a branch" s₁
  | .match_ x arms, s => do
      let s ← flushAt rc s
      needScope s.live [x] "a match"
      let s' ← scopeArms rc arms s s.retDone
      expectS isEmit "a match" s'
  | st, s => do
      let s ← flushAt rc s
      let s ← expectS isEmit "a statement" s
      needScope s.live (ownUses st) "a statement"
      pure s

/-- A block of its own (`inBlock`): its values leave scope at its end. -/
def scopeInner (rc : Nat) (ss : List Stmt) (s : SSt) : Except String SSt := do
  let s₁ ← expectS isEnter "a block" s
  let s₂ ← scopeBlock rc ss s₁
  let s₃ ← flushAt rc s₂
  let s₄ ← expectS isLeave "the end of a block" s₃
  pure { s₄ with live := s.live }

/-- The arms of a `match`, each from the scope before it; `acc` is whether some arm walked so far
made the return area. -/
def scopeArms (rc : Nat) : List (List Stmt) → SSt → Bool → Except String SSt
  | [], s, acc => .ok { s with retDone := acc }
  | arm :: more, s, acc => do
      let s₁ ← scopeInner rc arm s
      scopeArms rc more { s₁ with retDone := s.retDone } (acc || s₁.retDone)
end

/-- The walk of a traced function: its parameters in scope, its body, the values made after its
last statement, and nothing left of the trace. -/
def scopedE (tf : TracedFn) : Except String Unit := do
  let s ← scopeBlock tf.rets tf.core.body ⟨tf.trace.toList, addLive {} tf.core.params, false⟩
  let s ← flushAt tf.rets s
  if s.rest.isEmpty then .ok () else .error "the trace goes on past the function"

/-- **Scoped, decided.** -/
def scopedB (tf : TracedFn) : Bool :=
  match scopedE tf with
  | .ok () => true
  | .error _ => false

/-- **A scoped traced function**: what the completeness proof asks of each function beyond its
placement. -/
def Scoped (tf : TracedFn) : Prop := scopedB tf = true

end
end LeanVM.Guest.Backend.Complete
